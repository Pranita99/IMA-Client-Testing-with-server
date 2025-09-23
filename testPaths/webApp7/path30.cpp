#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup → login → get_menu → add_to_cart(valid_item) → delete_account → order
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string username;
    decls.push_back(make_unique<Decl>("username",
                     make_unique<TypeConst>("string")));
    // username = input();
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string password;
    decls.push_back(make_unique<Decl>("password",
                     make_unique<TypeConst>("string")));
    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // signup(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // username = input();   (again for login)
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input();   (again for login)
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // login(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // get_menu();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_menu", move(a))));
    }

    // string valid_item;
    decls.push_back(make_unique<Decl>("valid_item",
                     make_unique<TypeConst>("string")));
    // valid_item = input();
    {
        auto lhs = make_unique<Var>("valid_item");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string quantity;
    decls.push_back(make_unique<Decl>("quantity",
                     make_unique<TypeConst>("string")));
    // quantity = input();
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_to_cart(valid_item, quantity);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("valid_item"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // delete_account();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("delete_account", move(a))));
    }

    // order();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with restaurant functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Signup API block ---
    {
        /* pre: not_in(u, dom(U)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: U[u] = p */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("u"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Login API block ---
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
       
        vector<unique_ptr<Expr>> notInArgs;
        notInArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            notInArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInArgs)));
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

    // --- Get Menu API block ---
    {
        /* pre: in_dom(token, T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        inDom.push_back(make_unique<Var>("T"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_menu", move(callArgs));

        /* post: returns menu items (simplified as true condition) */
        auto post = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>{});

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add to Cart API block ---
    {
        /* pre: in_dom(token, T) && in_dom(item_id, M) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        inDomT.push_back(make_unique<Var>("T"));
       
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("item_id"));
        inDomM.push_back(make_unique<Var>("M"));
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_id"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[user_id][item_id] = quantity (where user_id = T[token]) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("C"));
            cartIdx.push_back(std::move(userId));
            cartIdx.push_back(make_unique<Var>("item_id"));
            postArgs.push_back(make_unique<FuncCall>("nested_mapped_value", move(cartIdx)));
        }
        postArgs.push_back(make_unique<Var>("quantity"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Delete Account API block ---
    {
        /* pre: in_dom(token, T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        inDom.push_back(make_unique<Var>("T"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("delete_account", move(callArgs));

        /* post: not_in(T[token], dom(U)) && not_in(token, dom(T)) */
        vector<unique_ptr<Expr>> userIdx;
        userIdx.push_back(make_unique<Var>("T"));
        userIdx.push_back(make_unique<Var>("token"));
        auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));

        vector<unique_ptr<Expr>> notInU;
        notInU.push_back(std::move(userId));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            notInU.push_back(make_unique<FuncCall>("dom", move(h)));
        }

        vector<unique_ptr<Expr>> notInT;
        notInT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            notInT.push_back(make_unique<FuncCall>("dom", move(h)));
        }

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("not_in", move(notInU)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInT)));
        auto post = make_unique<FuncCall>("and_operator", move(land));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Order API block ---
    {
        /* pre: not_in(token, dom(T)) (user deleted, invalid token) */
        vector<unique_ptr<Expr>> notInArgs;
        notInArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            notInArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("order", move(callArgs));

        /* post: false (order should fail due to deleted account) */
        auto post = make_unique<FuncCall>("false", vector<unique_ptr<Expr>>{});

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials map
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Token to user map
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Menu items map
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart data map (user_id -> item_id -> quantity)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("string")))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "M", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
