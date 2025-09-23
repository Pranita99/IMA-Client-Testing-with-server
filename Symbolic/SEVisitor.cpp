
#include "SEVisitor.hpp"
#include "smtlib_printer.hpp"   
#include <sstream>

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
    // Turn assume(e)/assert(e) into a path predicate for the solver
    if ((n.call->name=="assume" || n.call->name=="assert") && !n.call->args.empty()) {
        sigma.addPredicate( smtOf(sigma, *n.call->args[0]) );
    }
}

void SEVisitor::visit(const Program& n)
{
    for (auto& st : n.statements) {
        st->accept(*this);
    }
}

void SEVisitor::visit(const Var&)      {}
void SEVisitor::visit(const FuncCall&) {}
void SEVisitor::visit(const Num&)      {}
void SEVisitor::visit(const String&)   {}
