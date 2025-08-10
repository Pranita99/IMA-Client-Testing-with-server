#include "../ASTVis.hpp"
#include "../ast.hpp"

// complete the vtable
ExpoSEVisitor::~ExpoSEVisitor() {}

// expressions
void ExpoSEVisitor::visitExpr(Expr&)          {}
void ExpoSEVisitor::visitVar(Var&)            {}
void ExpoSEVisitor::visitNum(Num&)            {}
void ExpoSEVisitor::visitString(String&)      {}
void ExpoSEVisitor::visitFuncCall(FuncCall&)  {}
void ExpoSEVisitor::visitSet(Set&)            {}
void ExpoSEVisitor::visitMap(Map&)            {}

// statements / program
void ExpoSEVisitor::visitAssign(Assign&)             {}
void ExpoSEVisitor::visitFuncCallStmt(FuncCallStmt&) {}
void ExpoSEVisitor::visitProgram(Program&)           {}
