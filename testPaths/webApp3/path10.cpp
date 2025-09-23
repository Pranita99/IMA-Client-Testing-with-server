// Flow 10:
// Login → Logout → Logout Again (Testing double logout - should return UNSAT)

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

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // logout(token); // First logout
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
    }

    // logout(token); // Second logout - this should fail
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
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

    // --- login_success ---
    {
        vector<unique_ptr<Expr>> conj;

        // User must exist in U (assuming pre-registered user)
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

        // U[u] == p (password must match)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // token ∉ dom(T) (user not already logged in with this token)
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

        // T[token] = u (token maps to user)
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("T", "token"));
        eq.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- logout (First instance) ---
    {
        // Precondition: token ∈ dom(T) - user must be currently logged in
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

        // Postcondition: token ∉ dom(T) - token is removed from active sessions
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            postArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto post = make_unique<FuncCall>("not_in", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- logout (Second instance - identical constraints) ---
    {
        // Precondition: token ∈ dom(T) - user must be currently logged in
        // This will FAIL because the first logout already removed the token
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

        // Postcondition: token ∉ dom(T) - token is removed from active sessions
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            postArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto post = make_unique<FuncCall>("not_in", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
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
    globals.push_back(make_unique<Decl>("username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));

    // Initialize with at least one user for testing
    vector<unique_ptr<Init>> inits;
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> userEntries;
        userEntries.push_back(make_pair(
            make_unique<Var>("testuser"),
            make_unique<Var>("testpass")
        ));
        inits.push_back(make_unique<Init>("U", make_unique<Map>(move(userEntries))));
    }
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