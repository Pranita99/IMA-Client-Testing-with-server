#ifndef SMTLIB_PRINTER_HPP
#define SMTLIB_PRINTER_HPP

#include <ostream>
#include <sstream>
#include <fstream>
#include <unordered_map>
#include "../ast.hpp"
#include "SymbolicEnv.hpp"

namespace {

static inline bool isTrueLiteral (const std::string& s){ return s=="true"; }
static inline bool isFalseLiteral(const std::string& s){ return s=="false"; }
static inline std::string emptyBoolSetArray() { return "(as const (Array String Bool) false)"; }

static std::string smtOf(SymbolicEnv& sigma, const Expr& expr)
{
    struct V : ASTVisitor {
        explicit V(SymbolicEnv& sig) : sigma(sig) {}
        SymbolicEnv& sigma;
        std::ostringstream out;

        std::string sub(const Expr& e) { V t(sigma); const_cast<Expr&>(e).accept(t); return t.out.str(); }

        void visit(const Var& n) override {
            if (n.name=="true" || n.name=="false") { out << n.name; return; }
            out << sigma.symFor(n.name);
        }
        void visit(const Num& n) override { out << n.value; }
        void visit(const String& n) override { out << '"' << n.value << '"'; }

        void visit(const FuncCall& n) override
        {
            if ((n.name=="true" || n.name=="false") && n.args.empty()) { out << n.name; return; }

            if ((n.name=="input" || n.name=="fresh") && (n.args.size() <= 1)) {
                out << sigma.freshSym(n.name == "input" ? "inp" : "fresh");
                return;
            }

            if ((n.name=="equals" || n.name=="boolEq") && n.args.size()==2) {
                out << "(= " << sub(*n.args[0]) << " " << sub(*n.args[1]) << ')'; return;
            }

            if ((n.name=="not" || n.name=="not1") && n.args.size()==1) {
                std::string x = sub(*n.args[0]);
                if (isTrueLiteral(x))  { out << "false"; return; }
                if (isFalseLiteral(x)) { out << "true";  return; }
                out << "(not " << x << ')'; return;
            }

            if (n.name=="is_true"  && n.args.size()==1) { out << sub(*n.args[0]); return; }
            if (n.name=="is_false" && n.args.size()==1) { out << "(not " << sub(*n.args[0]) << ')'; return; }

            if ((n.name=="and_operator" || n.name=="and2") && !n.args.empty()) {
                std::vector<std::string> parts;
                for (auto& a : n.args) {
                    std::string t = sub(*a);
                    if (isFalseLiteral(t)) { out << "false"; return; }
                    if (!isTrueLiteral(t)) parts.push_back(std::move(t));
                }
                if (parts.empty())  { out << "true"; return; }
                if (parts.size()==1){ out << parts[0]; return; }
                out << "(and"; for (auto& p : parts) out << " " << p; out << ')'; return;
            }

            if ((n.name=="or_operator" || n.name=="or2") && !n.args.empty()) {
                std::vector<std::string> parts;
                for (auto& a : n.args) {
                    std::string t = sub(*a);
                    if (isTrueLiteral(t))  { out << "true";  return; }
                    if (!isFalseLiteral(t)) parts.push_back(std::move(t));
                }
                if (parts.empty())  { out << "false"; return; }
                if (parts.size()==1){ out << parts[0]; return; }
                out << "(or"; for (auto& p : parts) out << " " << p; out << ')'; return;
            }

            if (n.name=="getMapAtMatch" && n.args.size()==2) {
                static std::unordered_map<const FuncCall*,std::string> memo;
                static int cnt = 0;
                auto it = memo.find(&n);
                if (it==memo.end()) {
                    it = memo.emplace(&n, "Match" + std::to_string(++cnt)).first;
                    sigma.declareMap(it->second);
                }
                out << it->second;
                return;
            }

            auto mapBaseFromExpr = [&](const Expr& me) -> std::string {
                if (auto* v = dynamic_cast<const Var*>(&me)) {
                    if (!sigma.isMap(v->name)) sigma.declareMap(v->name);
                    return v->name;
                }
                if (auto* gm = dynamic_cast<const FuncCall*>(&me); gm && gm->name=="getMapAtMatch") {
                    std::string id = sub(me);
                    if (!sigma.isMap(id)) sigma.declareMap(id);
                    return id;
                }
                return {};
            };

            if (n.name=="dom" && n.args.size()==1) {
                std::string base = mapBaseFromExpr(*n.args[0]);
                if (!base.empty()) { out << sigma.getMap(base).dom; return; }
            }

            if (n.name=="in_dom" && n.args.size()==2) {
                std::string base = mapBaseFromExpr(*n.args[0]);
                if (!base.empty()) { out << "(select " << sigma.getMap(base).dom << " " << sub(*n.args[1]) << ')'; return; }
            }

            if (n.name=="not_in" && n.args.size()==2) {
                std::string base; const Expr* key = nullptr;
                if (auto* dom = dynamic_cast<const FuncCall*>(n.args[1].get()); dom && dom->name=="dom" && dom->args.size()==1)
                { base = mapBaseFromExpr(*dom->args[0]); key = n.args[0].get(); }
                if (base.empty()) { base = mapBaseFromExpr(*n.args[0]); key = n.args[1].get(); }
                if (!base.empty()) { out << "(not (select " << sigma.getMap(base).dom << " " << sub(*key) << "))"; return; }
            }

            // mapVal variants
            if ((n.name=="mapped_value" || n.name=="mapVal") && n.args.size()==2) {
                // nested: mapVal(mapVal(M,k1), k2)  => use BVal_M
                if (auto* inner_fc = dynamic_cast<const FuncCall*>(n.args[0].get())) {
                    if (inner_fc->name == "mapped_value" || inner_fc->name == "mapVal") {
                        // find base M and mark it as bucket
                        std::string base;
                        if (!inner_fc->args.empty()) {
                            if (auto* inner_base_var = dynamic_cast<const Var*>(inner_fc->args[0].get()))
                                base = inner_base_var->name;
                            else if (auto* inner_get = dynamic_cast<const FuncCall*>(inner_fc->args[0].get())) {
                                if (inner_get->name=="getMapAtMatch" && !inner_get->args.empty())
                                    base = sub(*inner_fc->args[0]);
                            }
                        }
                        if (!base.empty()) sigma.ensureBucketVal(base);
                        if (!base.empty()) {
                            out << "(select (select " << sigma.getMap(base).bval
                                << " " << sub(*inner_fc->args[1]) << ") "
                                << sub(*n.args[1]) << ")";
                            return;
                        }
                    }
                }
                // simple: mapVal(M,k) => String
                std::string base = mapBaseFromExpr(*n.args[0]);
                if (!base.empty()) { out << "(select " << sigma.getMap(base).val << " " << sub(*n.args[1]) << ')'; return; }
            }

            // in(x, setExpr)
            if (n.name=="in" && n.args.size()==2) {
                // in(x, mapVal(M,k1)) => (select (select BVal_M k1) x)
                if (auto* rhs_fc = dynamic_cast<const FuncCall*>(n.args[1].get())) {
                    if ((rhs_fc->name=="mapped_value" || rhs_fc->name=="mapVal") && rhs_fc->args.size()==2) {
                        if (auto* base_v = dynamic_cast<const Var*>(rhs_fc->args[0].get())) {
                            sigma.ensureBucketVal(base_v->name);
                            const auto& ms = sigma.getMap(base_v->name);
                            out << "(select (select " << ms.bval << " " << sub(*rhs_fc->args[1]) << ") "
                                << sub(*n.args[0]) << ")";
                            return;
                        }
                    }
                }
                if (dynamic_cast<const String*>(n.args[1].get())) {
                    sigma.addWarning("lowered in(x, \"lit\") to (= x \"lit\")");
                    out << "(= " << sub(*n.args[0]) << " " << sub(*n.args[1]) << ')'; return;
                }
                out << "(select " << sub(*n.args[1]) << " " << sub(*n.args[0]) << ')'; return;
            }

            if (n.name=="subset" && n.args.size()==2) {
                std::string A = sub(*n.args[0]);
                std::string B = sub(*n.args[1]);
                if (isTrueLiteral(B))  { out << "true\n";  return; }
                if (isFalseLiteral(B)) { out << "(forall ((k String)) (not (select " << A << " k)))\n"; return; }
                out << "(forall ((k String)) (=> (select " << A << " k) (select " << B << " k)))\n"; return;
            }

            if (n.name=="not_empty" && n.args.size()==1) {
                std::string dom;
                if (auto* v = dynamic_cast<const Var*>(n.args[0].get())) {
                    if (!sigma.isMap(v->name)) sigma.declareMap(v->name);
                    dom = sigma.getMap(v->name).dom;
                } else if (auto* fc = dynamic_cast<const FuncCall*>(n.args[0].get()); fc && fc->name=="dom" && fc->args.size()==1) {
                    dom = sub(*fc);
                } else {
                    out << "(not_empty " << sub(*n.args[0]) << ")"; return;
                }
                std::string k = sigma.freshSym("ne_witness");
                out << "(select " << dom << " " << k << ")\n"; return;
            }

            if (n.name=="map_bump" && (n.args.size()==2 || n.args.size()==3)) {
                const Var* mvar = dynamic_cast<const Var*>(n.args[0].get());
                if (!mvar) throw std::runtime_error("map_bump: first argument must be a map Var");
                const auto& M = mvar->name;
                const auto& ms = sigma.getMap(M);

                if (n.args.size()==2) {
                    out << "(store " << ms.dom << " " << sub(*n.args[1]) << " true)";
                } else {
                    sigma.ensureBucketVal(M);
                    out << "(store (select " << ms.bval << " " << sub(*n.args[1]) << ") "
                        << sub(*n.args[2]) << " true)";
                }
                return;
            }

            if (n.name=="clear_bucket" && (n.args.size()==1 || n.args.size()==2)) {
                out << emptyBoolSetArray(); return;
            }

            // Uninterpreted functions used in paths/specs
            if (n.name=="generateQRCode" && n.args.size()==1) {
                sigma.declareUF("(declare-fun generateQRCode (String) String)");
                out << "(generateQRCode " << sub(*n.args[0]) << ")"; return;
            }

            // Fallback: print as-is
            out << '(' << n.name;
            for (auto& a : n.args) out << " " << sub(*a);
            out << ')';
        }

        // stubs
        void visit(const Assign&) override {}
        void visit(const FuncCallStmt&) override {}
        void visit(const Program&) override {}
        void visit(const Decl&) override {}
        void visit(const FuncDecl&) override {}
        void visit(const APIcall&) override {}
        void visit(const API&) override {}
        void visit(const Response&) override {}
        void visit(const Init&) override {}
        void visit(const Spec&) override {}
        void visit(const Set&) override {}
        void visit(const Map&) override {}
        void visit(const Tuple&) override {}
        void visit(const TypeConst&) override {}
        void visit(const FuncType&) override {}
        void visit(const MapType&) override {}
        void visit(const TupleType&) override {}
        void visit(const SetType&) override {}
    };

    V v(sigma);
    const_cast<Expr&>(expr).accept(v);
    return v.out.str();
}

} // anonymous namespace
#endif /* SMTLIB_PRINTER_HPP */
