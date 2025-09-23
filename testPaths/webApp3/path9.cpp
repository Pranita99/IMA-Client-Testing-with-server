// Flow 9:
// Signup → Login → Search Item → Add to Cart → Logout → Login → Order (Valid path, should return SAT)

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

    // signup_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(a))));
    }

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // search_query = input();
    {
        auto lhs = make_unique<Var>("search_query");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // search_item(search_query);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("search_query"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("search_item", move(a))));
    }

    // add_to_cart(item_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // logout(token);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
    }

    // login_success(username, password); // Second login
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // order(cart);
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

    // --- signup_success ---
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

    // --- login_success ---
    {
        vector<unique_ptr<Expr>> conj;

        // U[u] == p
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Generate new token (can be different from previous one)
        {
            vector<unique_ptr<Expr>> emptyArgs;
            conj.push_back(make_unique<FuncCall>("true", move(emptyArgs)));
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

    // --- search_item ---
    {
        vector<unique_ptr<Expr>> conj;

        // token ∈ dom(T) - user must be authenticated
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // search_query != empty
        {
            vector<unique_ptr<Expr>> ne;
            ne.push_back(make_unique<Var>("search_query"));
            ne.push_back(make_unique<Var>(""));
            conj.push_back(make_unique<FuncCall>("not_equals", move(ne)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("search_query"));
        auto callFn = make_unique<FuncCall>("search_item", move(args));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("search_query"));
        auto post = make_unique<FuncCall>("search_results_available", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart ---
    {
        vector<unique_ptr<Expr>> conj;

        // token ∈ dom(T) - user must be authenticated
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // item_id must be available from search results
        {
            vector<unique_ptr<Expr>> avail;
            avail.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("item_available", move(avail)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // item_id ∈ cart
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("item_id"));
            conj_post.push_back(make_unique<FuncCall>("in_cart", move(postArgs)));
        }

        // cart persists across sessions (stored server-side with user)
        {
            vector<unique_ptr<Expr>> persist;
            persist.push_back(make_unique<Var>("cart"));
            persist.push_back(mapVal("T", "token"));
            conj_post.push_back(make_unique<FuncCall>("cart_persisted", move(persist)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- logout ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        auto callFn = make_unique<FuncCall>("logout", move(args));

        // Token is removed from active sessions but cart data persists
        vector<unique_ptr<Expr>> conj_post;
        
        // token ∉ dom(T)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj_post.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        // cart data remains preserved
        {
            vector<unique_ptr<Expr>> preserve;
            preserve.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("cart_preserved", move(preserve)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order ---
    {
        vector<unique_ptr<Expr>> conj;

        // cart must not be empty
        {
            vector<unique_ptr<Expr>> ne;
            ne.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("not_empty", move(ne)));
        }

        // user must be authenticated (new token after re-login)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // cart must be accessible to the authenticated user
        {
            vector<unique_ptr<Expr>> access;
            access.push_back(make_unique<Var>("cart"));
            access.push_back(mapVal("T", "token"));
            conj.push_back(make_unique<FuncCall>("cart_accessible", move(access)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // order is placed successfully
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("ordered", move(postArgs)));
        }

        // cart is cleared after successful order
        {
            vector<unique_ptr<Expr>> clear;
            clear.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("cart_cleared", move(clear)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

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
    globals.push_back(make_unique<Decl>("search_query", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("item_id", make_unique<TypeConst>("string")));

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