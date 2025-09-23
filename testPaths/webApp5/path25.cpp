#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *admin client* Program AST for
//  admin_login → view_all_orders → logout
// ─────────────────────────────────────────────────────────────
static Program buildAdminViewOrdersProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string adminId;
    decls.push_back(make_unique<Decl>("adminId",
                     make_unique<TypeConst>("string")));
    // adminId = input();
    {
        auto lhs = make_unique<Var>("adminId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                                make_unique<FuncCall>("input", move(args))));
    }

    // string adminPassword;
    decls.push_back(make_unique<Decl>("adminPassword",
                     make_unique<TypeConst>("string")));
    // adminPassword = input();
    {
        auto lhs = make_unique<Var>("adminPassword");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                                make_unique<FuncCall>("input", move(args))));
    }

    // admin_login(adminId, adminPassword);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminId"));
        a.push_back(make_unique<Var>("adminPassword"));
        stmts.push_back(make_unique<FuncCallStmt>(
                make_unique<FuncCall>("admin_login", move(a))));
    }

    // view_all_orders(adminId);
    decls.push_back(make_unique<Decl>("adminIdForOrders",
                     make_unique<TypeConst>("string")));
    // adminIdForOrders = adminId;  // reuse adminId or input again if desired
    {
        auto lhs = make_unique<Var>("adminIdForOrders");
        stmts.push_back(make_unique<Assign>(move(lhs), make_unique<Var>("adminId")));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminIdForOrders"));
        stmts.push_back(make_unique<FuncCallStmt>(
                make_unique<FuncCall>("view_all_orders", move(a))));
    }

    // logout(adminId);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminId"));
        stmts.push_back(make_unique<FuncCallStmt>(
                make_unique<FuncCall>("logout", move(a))));
    }

    return Program(std::move(stmts));
}


// ─────────────────────────────────────────────────────────────
//  Build the Admin Ecommerce API *Spec* AST (skeleton)
// ─────────────────────────────────────────────────────────────
static Spec buildAdminEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // You can add API blocks for admin_login, view_all_orders, logout
    // similar to your previous Spec examples.

    vector<unique_ptr<Decl>> globals;
    // ADMINS: Map<string, AdminRecord>
    globals.push_back(make_unique<Decl>(
        "ADMINS", make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("AdminRecord"))));
    // ADMIN_SESSIONS: Map<string, AdminSessionRecord>
    globals.push_back(make_unique<Decl>(
        "ADMIN_SESSIONS", make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("AdminSessionRecord"))));
    // ORDERS: Map<string, OrderRecord>
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "ADMINS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ADMIN_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}


/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildAdminViewOrdersProgram();
Spec    spec          = buildAdminEcommerceSpec();
