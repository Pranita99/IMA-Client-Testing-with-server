// Symbolic/SEVisitor.hpp
#pragma once
#include "../ASTVis.hpp"
#include "../ast.hpp"
#include "SymbolicEnv.hpp"
#include <string>

/*  Visitor that walks the mutated (IMA-enriched) client program
 *  and converts every concrete assignment / assume / assert into
 *  SMT-LIB predicates, storing them in a shared SymbolicEnv.
 */
class SEVisitor : public ASTVisitor {
public:
    explicit SEVisitor(SymbolicEnv& sigma) : sigma(sigma) {}

    /* =====  statements we translate  ===== */
    void visit(const Assign& n)       override;
    void visit(const FuncCallStmt& n) override;
    void visit(const Program& n)      override;   // definition lives in .cpp

    /* =====  expressions we translate via smtOf()  ===== */
    void visit(const Var& n)      override;
    void visit(const FuncCall& n) override;
    void visit(const Num& n)      override;
    void visit(const String& n)   override;

    /* =====  everything else is ignored for path-constraint generation ===== */
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

private:
    SymbolicEnv& sigma;               // shared environment that stores symbols & predicates
    std::string smtOf(const Expr& e); // helper: Expr → SMT-LIB snippet
};
