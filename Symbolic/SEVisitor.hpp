// Symbolic/SEVisitor.hpp
#pragma once
#include "../ASTVis.hpp"
#include "../ast.hpp"
#include "SymbolicEnv.hpp"
#include <string>
#include <vector>
#include <unordered_map>
#include <functional>

/*
 * SEVisitor
 * ----------
 * Walks the (IMA-mutated) program and:
 *   - lowers assignments / assume / assert into SMT via SymbolicEnv
 *   - (NEW) snapshots each non-(assume/assert) call's arguments so we can
 *     later emit arg→SSA (or literals) into ctc.json for mid-run execution.
 *   - exposes helpers for staged solving (collectVars, callSnaps)
 *
 * Back-compat: retains Checkpoint API so existing code compiles.
 */
class SEVisitor : public ASTVisitor {
public:
    explicit SEVisitor(SymbolicEnv& sigma, bool strict=false)
        : sigma(sigma), strictMode(strict) {}

    /* =====  statements we translate  ===== */
    void visit(const Assign& n)       override;
    void visit(const FuncCallStmt& n) override;
    void visit(const Program& n)      override;

    /* =====  expressions translated via smtOf() (no-op here) ===== */
    void visit(const Var&)      override {}
    void visit(const FuncCall&) override {}
    void visit(const Num&)      override {}
    void visit(const String&)   override {}

    /* =====  everything else ignored for path-constraints ===== */
    void visit(const Set&)        override {}
    void visit(const Map&)        override {}
    void visit(const Tuple&)      override {}
    void visit(const TypeConst&)  override {}
    void visit(const FuncType&)   override {}
    void visit(const MapType&)    override {}
    void visit(const TupleType&)  override {}
    void visit(const SetType&)    override {}
    void visit(const Decl&)       override {}
    void visit(const FuncDecl&)   override {}
    void visit(const APIcall&)    override {}
    void visit(const API&)        override {}
    void visit(const Response&)   override {}
    void visit(const Init&)       override {}
    void visit(const Spec&)       override {}

    void setStrict(bool b) { strictMode = b; }

    /* =====  NEW: snapshots for MAIN execution / mid-run solving  ===== */
    struct CallArgSnap {
        std::string name;        // best-effort arg name (Var name or arg1/arg2…)
        std::string ssa_or_lit;  // "xN" if SSA, or JSON literal like "\"abc\"" / "123"
        bool        is_ssa = true;
    };
    struct CallSnap {
        std::string              at;    // e.g., "signup#1"
        std::vector<CallArgSnap> args;  // positional order
    };

    const std::vector<CallSnap>& callSnaps() const { return snaps; }

    /* =====  Back-compat: staged/concolic helpers (kept) ===== */
    struct Checkpoint {
        std::string               callName;    // name of non-(assume/assert) call
        std::vector<std::string>  neededVars;  // base var names in its args
    };
    const std::vector<Checkpoint>& checkpoints() const { return cps; }
    void clearCheckpoints() { cps.clear(); }

    static bool isAssumeOrAssert(const FuncCallStmt& s) {
        const std::string& nm = s.call->name;
        return (nm == "assume" || nm == "assert");
    }

    /* =====  NEW helper: collect base vars in any statement ===== */
    static std::vector<std::string> collectVars(const Stmt& s) {
        std::vector<std::string> vars;
        std::function<void(const Expr&)> collect = [&](const Expr& e) {
            if (auto* v = dynamic_cast<const Var*>(&e)) {
                vars.push_back(v->name);
            } else if (auto* f = dynamic_cast<const FuncCall*>(&e)) {
                for (auto& a : f->args) collect(*a);
            } else if (auto* t = dynamic_cast<const Tuple*>(&e)) {
                for (auto& a : t->expr) collect(*a);
            } else if (auto* st = dynamic_cast<const Set*>(&e)) {
                for (auto& a : st->elements) collect(*a);
            } else if (auto* m = dynamic_cast<const Map*>(&e)) {
                for (auto& kv : m->value) {
                    collect(*kv.first);
                    collect(*kv.second);
                }
            }
        };

        if (auto* assign = dynamic_cast<const Assign*>(&s)) {
            collect(*assign->right);
        } else if (auto* call = dynamic_cast<const FuncCallStmt*>(&s)) {
            for (auto& a : call->call->args) collect(*a);
        }
        return vars;
    }

private:
    SymbolicEnv& sigma;
    bool         strictMode = false;

    // per-call-name counter to build stable "name#k" tags (matches driver)
    std::unordered_map<std::string,int> callCounts;
    std::vector<CallSnap>               snaps;

    // Back-compat storage (unused by default, but preserved for existing callers)
    std::vector<Checkpoint>             cps;
};
