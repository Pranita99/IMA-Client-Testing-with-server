// Symbolic/SEVisitor.cpp
#include "SEVisitor.hpp"
#include "smtlib_printer.hpp"
#include <sstream>
#include <functional>

/*
 
 * New additions:
 *  - For each non-(assume/assert) call, we:
 *      * snapshot arguments into CallSnap with arg→SSA or literal,
 *      * assign stable "name#k" tags via callCounts (matches driver),
 *      * also keep your legacy Checkpoint (collecting base vars).
 */

static std::string jsonQuote(const std::string& s) {
    std::ostringstream o; o << '"';
    for (char c : s) {
        switch (c) {
            case '"':  o << "\\\""; break;
            case '\\': o << "\\\\"; break;
            case '\n': o << "\\n";  break;
            case '\r': o << "\\r";  break;
            case '\t': o << "\\t";  break;
            default:   o << c;      break;
        }
    }
    o << '"';
    return o.str();
}

void SEVisitor::visit(const Assign& n)
{
    // SSA-bump the LHS variable in Sigma
    const std::string lhs = sigma.bumpScalar(n.left->name);

    // Lower the RHS expression to SMT-LIB via the shared printer
    const std::string rhs = smtOf(sigma, *n.right);

    // (= x' rhs)
    sigma.addPredicate("(= " + lhs + ' ' + (rhs.empty() ? "\"\"" : rhs) + ')');

    // If this was an input(), add the “non-empty string” side condition
    if (const auto* fc = dynamic_cast<const FuncCall*>(n.right.get())) {
        if (fc->name == "input" && fc->args.empty()) {
            sigma.addPredicate("(> (str.len " + lhs + ") 0)");
        }
    }
}

void SEVisitor::visit(const FuncCallStmt& n)
{
    const std::string& name = n.call->name;

    // Turn assume(e)/assert(e) into a path predicate for the solver
    if ((name=="assume" || name=="assert") && !n.call->args.empty()) {
        sigma.addPredicate( smtOf(sigma, *n.call->args[0]) );
        return;
    }

    // ─────────────────────────────────────────────────────────────
    // NEW: snapshot arguments for MAIN execution / mid-run support
    // ─────────────────────────────────────────────────────────────
    {
        int idx = ++callCounts[name];
        CallSnap snap;
        snap.at = name + "#" + std::to_string(idx);

        // Legacy checkpoint (back-compat)
        Checkpoint cp;
        cp.callName = name;

        auto handleArg = [&](size_t i, const Expr& e) {
            CallArgSnap a;
            a.name = "arg" + std::to_string(i+1);

            if (auto* v = dynamic_cast<const Var*>(&e)) {
                a.name        = v->name;
                a.ssa_or_lit  = sigma.symFor(v->name); // current SSA id for this var
                a.is_ssa      = true;
                cp.neededVars.push_back(v->name);
            } else if (auto* s = dynamic_cast<const String*>(&e)) {
                a.ssa_or_lit  = jsonQuote(s->value);   // literal JSON string
                a.is_ssa      = false;
            } else if (auto* num = dynamic_cast<const Num*>(&e)) {
                a.ssa_or_lit  = std::to_string(num->value); // numeric literal as JSON number
                a.is_ssa      = false;
            } else {
                // Fallback: lower to SMT and keep as JSON string literal (best-effort)
                a.ssa_or_lit  = jsonQuote( smtOf(sigma, e) );
                a.is_ssa      = false;
            }
            snap.args.push_back(std::move(a));
        };

        for (size_t i = 0; i < n.call->args.size(); ++i) {
            handleArg(i, *n.call->args[i]);
        }

        snaps.push_back(std::move(snap));
        if (!cp.callName.empty()) cps.push_back(std::move(cp));
    }
}

void SEVisitor::visit(const Program& n)
{
    // Clear any previous run state
    cps.clear();
    callCounts.clear();
    snaps.clear();

    for (auto& st : n.statements) {
        st->accept(*this);
    }
}
