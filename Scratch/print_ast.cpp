// Scratch/print_ast.cpp — print ABSTRACT + SYMBOLIC for any path (no visitors)

#include <iostream>
#include <sstream>
#include <vector>
#include <memory>
#include <unordered_map>
#include <string>

#include "../Symbolic/SymbolicEnv.hpp"
#include "../Symbolic/smtlib_printer.hpp"   // smtOf(SymbolicEnv&, Expr&)
#include "../IMA.hpp"
#include "../ast.hpp"


#ifndef PATH_FILE
#define PATH_FILE "../testPaths/webApp3/path1.cpp"
#endif
#include PATH_FILE


static std::string showExpr(const Expr& e) {
    if (auto* v = dynamic_cast<const Var*>(&e))    return v->name;
    if (auto* n = dynamic_cast<const Num*>(&e))    return std::to_string(n->value);
    if (auto* s = dynamic_cast<const String*>(&e)) return "\"" + s->value + "\"";

    if (auto* fc = dynamic_cast<const FuncCall*>(&e)) {
        std::ostringstream oss; oss << fc->name << "(";
        for (size_t i=0; i<fc->args.size(); ++i) {
            if (i) oss << ", ";
            oss << showExpr(*fc->args[i]);
        }
        oss << ")";
        return oss.str();
    }
    if (auto* set = dynamic_cast<const Set*>(&e)) {
        std::ostringstream oss; oss << "{";
        for (size_t i=0; i<set->elements.size(); ++i) {
            if (i) oss << ", ";
            oss << showExpr(*set->elements[i]);
        }
        oss << "}";
        return oss.str();
    }
    if (auto* mp = dynamic_cast<const Map*>(&e)) {
        std::ostringstream oss; oss << "{";
        for (size_t i=0; i<mp->value.size(); ++i) {
            if (i) oss << ", ";
            oss << mp->value[i].first->name << ": "
                << showExpr(*mp->value[i].second);
        }
        oss << "}";
        return oss.str();
    }
    if (auto* t = dynamic_cast<const Tuple*>(&e)) {
        std::ostringstream oss; oss << "(";
        for (size_t i=0; i<t->expr.size(); ++i) {
            if (i) oss << ", ";
            oss << showExpr(*t->expr[i]);
        }
        oss << ")";
        return oss.str();
    }
    return "<expr>";
}

static void printAbstract(const Program& p) {
    int i = 1;
    for (const auto& st : p.statements) {
        std::cout << i++ << ": ";
        if (auto* a = dynamic_cast<Assign*>(st.get())) {
            std::cout << a->left->name << " = " << showExpr(*a->right) << ";\n";
        } else if (auto* f = dynamic_cast<FuncCallStmt*>(st.get())) {
            std::cout << f->call->name << "(";
            for (size_t j=0; j<f->call->args.size(); ++j) {
                if (j) std::cout << ", ";
                std::cout << showExpr(*f->call->args[j]);
            }
            std::cout << ");\n";
        } else {
            std::cout << "<stmt>\n";
        }
    }
}

// ---------- build SMT using the same lowering the solver sees ----------
static void buildSymbolic(SymbolicEnv& sigma,
                          const Program& prog,
                          const TypeMap& tmap)
{
    // Predeclare arrays for all maps IMA discovered
    for (const auto& kv : tmap.mapping) {
        if (dynamic_cast<MapType*>(kv.second) != nullptr)
            sigma.declareMap(kv.first);
    }

    // Turn each assignment into an (= xN <smt-of-rhs>) predicate.
    // Also collect assume/assert predicates as-is.
    for (const auto& st : prog.statements) {
        if (auto* a = dynamic_cast<Assign*>(st.get())) {
            // Get a fresh SSA id for the LHS and lower RHS via smtOf(...)
            const std::string lhs = sigma.bumpScalar(a->left->name);
            const std::string rhs = smtOf(sigma, *a->right);
            const std::string eq  = "(= " + lhs + ' ' + (rhs.empty() ? "\"\"" : rhs) + ')';
            sigma.addPredicate(eq);
        } else if (auto* f = dynamic_cast<FuncCallStmt*>(st.get())) {
            const std::string& nm = f->call->name;
            if ((nm=="assume" || nm=="assert") && !f->call->args.empty())
                sigma.addPredicate( smtOf(sigma, *f->call->args[0]) );
        }
    }
}

int main() {
    SymbolTable sym;
    TypeMap     tmap;

    // Run IMA to obtain the mutated (instrumented) program + type info
    Program mutant = IMA(clientProgram, spec, sym, tmap);

    // 1) ABSTRACT
    std::cout << "\n=== Abstract test case ===\n";
    printAbstract(mutant);

    // 2) SYMBOLIC (body only; no (check-sat)/(get-value) here)
    SymbolicEnv sigma;
    buildSymbolic(sigma, mutant, tmap);

    std::cout << "\n=== Symbolic path constraints ===\n";
    std::cout << sigma.toSMTLib() << '\n';
    return 0;
}
