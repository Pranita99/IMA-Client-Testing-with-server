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

/* Select the path at compile time (or edit default below).
   Examples:
     g++ ... -DPATH_FILE="\"../testPaths/webApp1/path2.cpp\"" ...
     g++ ... -DPATH_FILE="\"../testPaths/webApp1/path4.cpp\"" ...
*/
#ifndef PATH_FILE
#define PATH_FILE "../testPaths/webApp1/path3.cpp"
#endif
#include PATH_FILE

// ---------------- tiny pretty-printer for the ABSTRACT TEST CASE ----------------
static std::string showExpr(const Expr& e) {
    if (auto* v = dynamic_cast<const Var*>(&e))    return v->name;
    if (auto* n = dynamic_cast<const Num*>(&e))    return std::to_string(n->value);
    if (auto* s = dynamic_cast<const String*>(&e)) return "\"" + s->value + "\"";

    if (auto* fc = dynamic_cast<const FuncCall*>(&e)) {
        std::ostringstream oss; oss << fc->name << "(";
        for (size_t i=0;i<fc->args.size();++i) {
            if (i) oss << ", ";
            oss << showExpr(*fc->args[i]);
        }
        oss << ")";
        return oss.str();
    }
    if (auto* set = dynamic_cast<const Set*>(&e)) {
        std::ostringstream oss; oss << "{";
        for (size_t i=0;i<set->elements.size();++i) {
            if (i) oss << ", ";
            oss << showExpr(*set->elements[i]);
        }
        oss << "}";
        return oss.str();
    }
    if (auto* mp = dynamic_cast<const Map*>(&e)) {
        std::ostringstream oss; oss << "{";
        for (size_t i=0;i<mp->value.size();++i) {
            if (i) oss << ", ";
            oss << mp->value[i].first->name << ": "
                << showExpr(*mp->value[i].second);
        }
        oss << "}";
        return oss.str();
    }
    if (auto* t = dynamic_cast<const Tuple*>(&e)) {
        std::ostringstream oss; oss << "(";
        for (size_t i=0;i<t->expr.size();++i) {
            if (i) oss << ", ";
            oss << showExpr(*t->expr[i]);
        }
        oss << ")";
        return oss.str();
    }
    return "<expr>";
}

static void printAbstract(const Program& p) {
    std::cout << "\n=== abstract test case ===\n";
    int i = 1;
    for (const auto& st : p.statements) {
        std::cout << i++ << ": ";
        if (auto* a = dynamic_cast<Assign*>(st.get())) {
            std::cout << a->left->name << " = " << showExpr(*a->right) << ";\n";
        } else if (auto* f = dynamic_cast<FuncCallStmt*>(st.get())) {
            std::cout << f->call->name << "(";
            for (size_t j=0;j<f->call->args.size();++j) {
                if (j) std::cout << ", ";
                std::cout << showExpr(*f->call->args[j]);
            }
            std::cout << ");\n";
        } else {
            std::cout << "<stmt>\n";
        }
    }
}

// ---------------- build SMT using the same lowering the solver sees --------------
static void buildSymbolic(SymbolicEnv& sigma,
                          const Program& prog,
                          const TypeMap& tmap)
{
    // Predeclare arrays for all maps IMA discovered
    for (const auto& kv : tmap)
        if (dynamic_cast<MapType*>(kv.second) != nullptr)
            sigma.declareMap(kv.first);

    for (const auto& st : prog.statements) {
        if (auto* a = dynamic_cast<Assign*>(st.get())) {
            const std::string lhs = sigma.bumpScalar(a->left->name);      // SSA
            const std::string rhs = smtOf(sigma, *a->right);              // shared lowerer
            sigma.addPredicate("(= " + lhs + ' ' + (rhs.empty() ? "\"\"" : rhs) + ')');
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

    Program mutant = IMA(clientProgram, spec, sym, tmap);

    // 1) ABSTRACT
    std::cout << "\n=== abstract test case ===\n";
    printAbstract(mutant);          // <-- this prints only the body

    // 2) SYMBOLIC
    SymbolicEnv sigma;
    buildSymbolic(sigma, mutant, tmap);
    std::cout << "\n=== symbolic path constraints ===\n";
    std::cout << sigma.toSMTLib(false) << '\n';
    return 0;
}