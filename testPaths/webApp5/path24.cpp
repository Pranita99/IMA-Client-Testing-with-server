#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *admin client* Program AST for
//  admin_login → update_product → logout
// ─────────────────────────────────────────────────────────────
static Program buildAdminClientProgram()
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

    // string productId;
    decls.push_back(make_unique<Decl>("productId",
                     make_unique<TypeConst>("string")));
    // productId = input();
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                                make_unique<FuncCall>("input", move(args))));
    }

    // string newProductName;
    decls.push_back(make_unique<Decl>("newProductName",
                     make_unique<TypeConst>("string")));
    // newProductName = input();
    {
        auto lhs = make_unique<Var>("newProductName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                                make_unique<FuncCall>("input", move(args))));
    }

    // update_product(adminId, productId, newProductName);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminId"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("newProductName"));
        stmts.push_back(make_unique<FuncCallStmt>(
                make_unique<FuncCall>("update_product", move(a))));
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
//  Build the Admin Ecommerce API *Spec* AST
//  (Similar to customer’s, but for admin functionality)
// ─────────────────────────────────────────────────────────────
static Spec buildAdminEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // You can add API blocks for admin_login, update_product, logout,
    // following the pattern shown in your customer spec.

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
    // PRODUCTS: Map<string, ProductRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("ProductRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "ADMINS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ADMIN_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildAdminClientProgram();
Spec    spec          = buildAdminEcommerceSpec();
