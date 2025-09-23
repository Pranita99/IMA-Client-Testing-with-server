#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: signup → login → add_item
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup → login → add_item flow
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

    // string item_name;
    decls.push_back(make_unique<Decl>("item_name",
                     make_unique<TypeConst>("string")));
    // item_name = input();
    {
        auto lhs = make_unique<Var>("item_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string item_price;
    decls.push_back(make_unique<Decl>("item_price",
                     make_unique<TypeConst>("string")));
    // item_price = input();
    {
        auto lhs = make_unique<Var>("item_price");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string item_description;
    decls.push_back(make_unique<Decl>("item_description",
                     make_unique<TypeConst>("string")));
    // item_description = input();
    {
        auto lhs = make_unique<Var>("item_description");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_item(item_name, item_price, item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_name"));
        a.push_back(make_unique<Var>("item_price"));
        a.push_back(make_unique<Var>("item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_item", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST for signup → login → add_item flow
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
        /* pre: U[u] = p  &&  token ∉ dom(T) */
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
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("T"));
            inDom.push_back(make_unique<Var>("token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
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

    // --- Add Item API block ---
    {
        /* pre: token ∈ dom(T) && item_id ∉ dom(M) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("T"));
        inDomT.push_back(make_unique<Var>("token"));
        
        vector<unique_ptr<Expr>> notInDomM;
        notInDomM.push_back(make_unique<Var>("item_id"));
        {
            vector<unique_ptr<Expr>> domM;
            domM.push_back(make_unique<Var>("M"));
            notInDomM.push_back(make_unique<FuncCall>("dom", move(domM)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_name"));
        callArgs.push_back(make_unique<Var>("item_price"));
        callArgs.push_back(make_unique<Var>("item_description"));
        auto callFn = make_unique<FuncCall>("add_item", move(callArgs));

        /* post: M[item_id] = item_details */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> itemDetails;
            itemDetails.push_back(make_unique<Var>("item_name"));
            itemDetails.push_back(make_unique<Var>("item_price"));
            itemDetails.push_back(make_unique<Var>("item_description"));
            postArgs.push_back(make_unique<FuncCall>("item_record", move(itemDetails)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
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
    // Restaurant data map
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Menu items map
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart map (user -> items map)
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
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
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