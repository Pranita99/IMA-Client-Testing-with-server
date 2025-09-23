#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for admin login → update_product
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string admin_username;
    decls.push_back(make_unique<Decl>("admin_username",
                     make_unique<TypeConst>("string")));
    // admin_username = input();
    {
        auto lhs = make_unique<Var>("admin_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string admin_password;
    decls.push_back(make_unique<Decl>("admin_password",
                     make_unique<TypeConst>("string")));
    // admin_password = input();
    {
        auto lhs = make_unique<Var>("admin_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // login(admin_username, admin_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_username"));
        a.push_back(make_unique<Var>("admin_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // string product_id;
    decls.push_back(make_unique<Decl>("product_id",
                     make_unique<TypeConst>("string")));
    // product_id = input();
    {
        auto lhs = make_unique<Var>("product_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string new_product_name;
    decls.push_back(make_unique<Decl>("new_product_name",
                     make_unique<TypeConst>("string")));
    // new_product_name = input();
    {
        auto lhs = make_unique<Var>("new_product_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string new_product_price;
    decls.push_back(make_unique<Decl>("new_product_price",
                     make_unique<TypeConst>("string")));
    // new_product_price = input();
    {
        auto lhs = make_unique<Var>("new_product_price");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // update_product(product_id, new_product_name, new_product_price);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("product_id"));
        a.push_back(make_unique<Var>("new_product_name"));
        a.push_back(make_unique<Var>("new_product_price"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("update_product", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin login and product update functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Login API block (for admin authentication) ---
    {
        /* pre: U[u] = p  &&  not_in(token, dom(T)) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("u"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("p"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domT;
                domT.push_back(make_unique<Var>("T"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(domT)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: T[token] = u */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("T"));
            idx.push_back(make_unique<Var>("token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Update Product API block ---
    {
        /* pre: token ∈ dom(T) && is_admin(T[token]) && product_id ∈ dom(P) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        
        vector<unique_ptr<Expr>> isAdminArgs;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            isAdminArgs.push_back(make_unique<FuncCall>("mapped_value", move(userIdx)));
        }
        
        vector<unique_ptr<Expr>> inDomP;
        inDomP.push_back(make_unique<Var>("product_id"));
        {
            vector<unique_ptr<Expr>> domP;
            domP.push_back(make_unique<Var>("P"));
            inDomP.push_back(make_unique<FuncCall>("dom", move(domP)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("is_admin", move(isAdminArgs)));
        land.push_back(make_unique<FuncCall>("in", move(inDomP)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("product_id"));
        callArgs.push_back(make_unique<Var>("new_product_name"));
        callArgs.push_back(make_unique<Var>("new_product_price"));
        auto callFn = make_unique<FuncCall>("update_product", move(callArgs));

        /* post: P[product_id] = {name: new_product_name, price: new_product_price} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("P"));
            idx.push_back(make_unique<Var>("product_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> productData;
            productData.push_back(make_unique<Var>("new_product_name"));
            productData.push_back(make_unique<Var>("new_product_price"));
            postArgs.push_back(make_unique<FuncCall>("product_object", move(productData)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials map (includes both regular users and admins)
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Token to user map
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Products map (product_id -> product_details)
    globals.push_back(make_unique<Decl>(
        "P", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin privileges map (user_id -> admin_status)
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "P", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();