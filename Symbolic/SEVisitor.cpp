/* ─────────────────────────────────── Symbolic/SEVisitor.cpp ─────────────── */
#include "SEVisitor.hpp"
#include <sstream>
#include <unordered_map>
#include <stdexcept>

namespace {            /* helpers & local state for this translation unit */

// give each call  getMapAtMatch( … , … )  its own synthetic map name
static std::unordered_map<const FuncCall*,std::string> matchMemo;
static int                                              matchCnt = 0;

/* tiny helpers */
static inline bool isTrueLiteral (const std::string& s){ return s=="true";  }
static inline bool isFalseLiteral(const std::string& s){ return s=="false"; }

/*────────────────────────  Expr  ➜  SMT-LIB (fully interpreted) ───────────*/
static std::string smtOf(SymbolicEnv& sigma, bool strictMode, const Expr& e)
{
    struct V : ASTVisitor {
        SymbolicEnv &sigma;
        bool         strict;
        std::string  s;                               // produced snippet
        V(SymbolicEnv& sig, bool strict) : sigma(sig), strict(strict) {}

        /* recurse */
        std::string sub(const Expr& ex) {
            V t(sigma, strict); const_cast<Expr&>(ex).accept(t); return t.s;
        }

        /* ───────────── leaves ───────────── */
        void visit(const Var& n) override {
            if (n.name == "=") { s = "\"=\""; return; }           // string literal
            if (n.name == "true" || n.name == "false") { s = n.name; return; }
            s = sigma.symFor(n.name);                             // program var
        }
        void visit(const Num& n)    override { s = std::to_string(n.value); }
        void visit(const String& n) override { s = '"' + n.value + '"';    }

        /* ───────────── helpers & API calls ───────────── */
        void visit(const FuncCall& n) override
        {
            /* 0. boolean constants: true()/false() */
            if ((n.name=="true" || n.name=="false") && n.args.empty()) { s = n.name; return; }

            /* 1. input() / input(x)  → fresh symbol */
            if (n.name=="input" && (n.args.size()==0 || n.args.size()==1)) {
                s = sigma.freshSym("inp"); return;
            }

            /* 2. equals/boolEq(a,b) → (= a b) */
            if ((n.name=="equals" || n.name=="boolEq") && n.args.size()==2) {
                s = "(= " + sub(*n.args[0]) + ' ' + sub(*n.args[1]) + ')'; return;
            }

            /* 3. not / not1 */
            if ((n.name=="not" || n.name=="not1") && n.args.size()==1) {
                std::string x = sub(*n.args[0]);
                if (isTrueLiteral(x))  { s = "false"; return; }
                if (isFalseLiteral(x)) { s = "true";  return; }
                s = "(not " + x + ')'; return;
            }

            /* 4. is_true / is_false wrappers */
            if (n.name=="is_true"  && n.args.size()==1) { s = sub(*n.args[0]);           return; }
            if (n.name=="is_false" && n.args.size()==1) { s = "(not " + sub(*n.args[0]) + ')'; return; }

            /* 5. and_operator / and2(e1 … en) → (and …) with constant folding */
            if ((n.name=="and_operator" || n.name=="and2") && !n.args.empty()) {
                std::vector<std::string> parts; parts.reserve(n.args.size());
                for (auto& a : n.args) {
                    std::string t = sub(*a);
                    if (isFalseLiteral(t)) { s="false"; return; }     // short-circuit
                    if (!isTrueLiteral(t)) parts.push_back(std::move(t));
                }
                if (parts.empty()) { s="true"; return; }
                if (parts.size()==1) { s=parts[0]; return; }
                std::ostringstream oss; oss << "(and"; for (auto& p:parts) oss<<' '<<p; oss<<')'; s=oss.str(); return;
            }

            /* 6. or_operator / or2(e1 … en) → (or …) with constant folding */
            if ((n.name=="or_operator" || n.name=="or2") && !n.args.empty()) {
                std::vector<std::string> parts; parts.reserve(n.args.size());
                for (auto& a : n.args) {
                    std::string t = sub(*a);
                    if (isTrueLiteral(t)) { s="true"; return; }       // short-circuit
                    if (!isFalseLiteral(t)) parts.push_back(std::move(t));
                }
                if (parts.empty()) { s="false"; return; }
                if (parts.size()==1) { s=parts[0]; return; }
                std::ostringstream oss; oss << "(or"; for (auto& p:parts) oss<<' '<<p; oss<<')'; s=oss.str(); return;
            }

            /* 7. getMapAtMatch(user,pass) : invent a synthetic map */
            if (n.name=="getMapAtMatch" && n.args.size()==2) {
                auto it = matchMemo.find(&n);
                if (it==matchMemo.end()) {
                    it = matchMemo.emplace(&n, "Match" + std::to_string(++matchCnt)).first;
                    sigma.declareMap(it->second);                 // register Dom_/Val_
                }
                s = it->second;       // return base id (used later by dom / mapped_value)
                return;
            }

            /* 8. dom(M) — with Var *or* getMapAtMatch(...) ----------------- */
            if (n.name=="dom" && n.args.size()==1) {
                const Expr* arg = n.args[0].get();

                /*   dom( M )  where M is a plain Var  */
                if (auto* v = dynamic_cast<const Var*>(arg)) {
                    if (!sigma.isMap(v->name)) sigma.declareMap(v->name);
                    s = sigma.getMap(v->name).dom;  return;
                }

                /*   dom( getMapAtMatch(u,p) )  */
                if (auto* gm = dynamic_cast<const FuncCall*>(arg);
                    gm && gm->name=="getMapAtMatch") {
                    visit(*gm);                           // fills   s = "Matchk"
                    const auto& ms = sigma.getMap(s);     // (now s == base id)
                    s = ms.dom;                           // use its Dom_*
                    return;
                }
            }

            /* helper to resolve map base id from either Var or getMapAtMatch */
            auto mapBaseFromExpr = [&](const Expr& m) -> std::string {
                if (auto* v = dynamic_cast<const Var*>(&m)) {
                    if (!sigma.isMap(v->name)) sigma.declareMap(v->name);
                    return v->name;
                }
                if (auto* gm = dynamic_cast<const FuncCall*>(&m)) {
                    if (gm->name=="getMapAtMatch") {
                        // evaluate to ensure we memoize & declare
                        std::string id = sub(m); // returns "Match#"
                        if (!sigma.isMap(id)) sigma.declareMap(id);
                        return id;
                    }
                }
                return {}; // unknown expression kind for map
            };

            /* 9. in_dom(M,k) ------------------------------------------------- */
            if (n.name=="in_dom" && n.args.size()==2) {
                std::string base = mapBaseFromExpr(*n.args[0]);
                if (!base.empty()) {
                    const auto& ms = sigma.getMap(base);
                    s = "(select " + ms.dom + ' ' + sub(*n.args[1]) + ')';
                    return;
                }
            }

            /* 10. not_in variants ------------------------------------------- */
            if (n.name=="not_in" && n.args.size()==2) {
                std::string base;  const Expr* key=nullptr;

                /* pattern-1: not_in(k, dom(M)) */
                if (auto* d = dynamic_cast<const FuncCall*>(n.args[1].get());
                    d && d->name=="dom" && d->args.size()==1)
                {
                    base = mapBaseFromExpr(*d->args[0]);
                    key  = n.args[0].get();
                }

                /* pattern-2: not_in(M, k) (M may be Var or getMapAtMatch) */
                if (base.empty()) {
                    base = mapBaseFromExpr(*n.args[0]);
                    key  = n.args[1].get();
                }

                if (!base.empty()) {
                    const auto& ms = sigma.getMap(base);
                    s = "(not (select " + ms.dom + ' ' + sub(*key) + "))";
                    return;
                }
            }

            /* 11. mapped_value / mapVal (M,k) → select Val_M k -------------- */
            if ((n.name=="mapped_value" || n.name=="mapVal") && n.args.size()==2) {
                std::string base = mapBaseFromExpr(*n.args[0]);
                if (!base.empty()) {
                    const auto& ms = sigma.getMap(base);
                    s = "(select " + ms.val + ' ' + sub(*n.args[1]) + ')';
                    return;
                }
            }

            /* 12. in(k, Dom)   generic membership + tolerant singleton --------
             *     - If rhs is dom(M)/Dom_*, we emit (select Dom_M k).
             *     - If rhs is a String literal and strict==false, treat as (= k "lit").
             */
            if (n.name=="in" && n.args.size()==2) {
                if (dynamic_cast<const String*>(n.args[1].get())) {
                    if (strict) {
                        throw std::runtime_error("Strict mode: in(x, \"lit\") is forbidden; use equals(x,\"lit\").");
                    }
                    sigma.addWarning("lowered in(x, \"lit\") to (= x \"lit\")");
                    s = "(= " + sub(*n.args[0]) + ' ' + sub(*n.args[1]) + ')';
                    return;
                }
                // generic: (select <rhs> <lhs>)  ; works if rhs == Dom_M
                s = "(select " + sub(*n.args[1]) + ' ' + sub(*n.args[0]) + ')';
                return;
            }

            /* fallback – unknown thing: keep uninterpreted (rare now) */
            std::ostringstream oss; oss << '(' << n.name;
            for (auto& a : n.args) oss << ' ' << sub(*a); oss << ')';
            s = oss.str();
        }

        /* ignore pure structural nodes */
        void visit(const Assign&)       override {}
        void visit(const FuncCallStmt&) override {}
        void visit(const Program&)      override {}
        void visit(const Set&)          override {}
        void visit(const Map&)          override {}
        void visit(const Tuple&)        override {}
        void visit(const TypeConst&)    override {}
        void visit(const FuncType&)     override {}
        void visit(const MapType&)      override {}
        void visit(const TupleType&)    override {}
        void visit(const SetType&)      override {}
        void visit(const Decl&)         override {}
        void visit(const FuncDecl&)     override {}
        void visit(const APIcall&)      override {}
        void visit(const API&)          override {}
        void visit(const Response&)     override {}
        void visit(const Init&)         override {}
        void visit(const Spec&)         override {}
    };

    V v(sigma, strictMode); const_cast<Expr&>(e).accept(v); return v.s;
}
/*───────────────────────────────────────────────────────────────────────────*/
} // namespace



/* ─────────────  statement visitors  (collect path predicates) ──────────── */
void SEVisitor::visit(const Assign& n)
{
    const std::string lhs = sigma.bumpScalar(n.left->name);   // SSA bump
    const std::string rhs = smtOf(sigma, strictMode, *n.right);

    sigma.addPredicate("(= " + lhs + ' ' + (rhs.empty() ? "\"\"" : rhs) + ')');
}

void SEVisitor::visit(const FuncCallStmt& n)
{
    if ((n.call->name=="assume" || n.call->name=="assert") && !n.call->args.empty())
        sigma.addPredicate( smtOf(sigma, strictMode, *n.call->args[0]) );
}

void SEVisitor::visit(const Program& n)
{
    for (auto& st : n.statements) st->accept(*this);
}

/* these expression kinds are handled only inside smtOf() */
void SEVisitor::visit(const Var&)      {}
void SEVisitor::visit(const FuncCall&) {}
void SEVisitor::visit(const Num&)      {}
void SEVisitor::visit(const String&)   {}
