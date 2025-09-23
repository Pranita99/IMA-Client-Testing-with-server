// Flow 12:
// Login Without Signup → Should fail login precondition (should return UNSAT)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the client Program (imperative path)
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // username = input();
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // NOTE: NO signup_success() call here - this is the key missing step

    // login_success(username, password); - This should FAIL
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // getmenu(canteen_id); - This would never be reached
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("canteen_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getmenu", move(a))));
    }

    // add_to_cart(item_id); - This would never be reached
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // order(cart); - This would never be reached
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("cart"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("order", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API specification
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

    // --- signup_success (NOT CALLED in this flow, but spec still defines it) ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_success", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U", "u"));
        eq.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_success (STRICT preconditions - will FAIL) ---
    {
        vector<unique_ptr<Expr>> conj;

        // CRITICAL: User must exist in U (u ∈ dom(U))
        // This will FAIL because no signup was performed
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("u"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("U"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // CRITICAL: Password must match stored password (U[u] == p)
        // This will FAIL because U[u] is undefined (user doesn't exist)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Token must not already exist (reasonable constraint)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("T", "token"));
        eq.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- getmenu (will never be reached due to login failure) ---
    {
        vector<unique_ptr<Expr>> emptyArgs;
        auto pre = make_unique<FuncCall>("true", move(emptyArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("canteen_id"));
        auto callFn = make_unique<FuncCall>("getmenu", move(args));

        vector<unique_ptr<Expr>> postArgs;
        auto post = make_unique<FuncCall>("menu_visible", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart (will never be reached due to login failure) ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("item_id"));
        auto post = make_unique<FuncCall>("in_cart", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order (will never be reached due to login failure) ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("cart"));
        auto pre = make_unique<FuncCall>("not_empty", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("cart"));
        auto post = make_unique<FuncCall>("ordered", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- globals ---
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("cart", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("canteen_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("item_id", make_unique<TypeConst>("string")));

    // CRITICAL: Initialize with EMPTY maps - no pre-existing users
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();