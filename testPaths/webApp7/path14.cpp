#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: signup → login → get_cart
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *user* Program AST for cart management
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string user_username;
    decls.push_back(make_unique<Decl>("user_username",
                     make_unique<TypeConst>("string")));
    // user_username = input();
    {
        auto lhs = make_unique<Var>("user_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string user_password;
    decls.push_back(make_unique<Decl>("user_password",
                     make_unique<TypeConst>("string")));
    // user_password = input();
    {
        auto lhs = make_unique<Var>("user_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string user_email;
    decls.push_back(make_unique<Decl>("user_email",
                     make_unique<TypeConst>("string")));
    // user_email = input();
    {
        auto lhs = make_unique<Var>("user_email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // signup(user_username, user_password, user_email);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_username"));
        a.push_back(make_unique<Var>("user_password"));
        a.push_back(make_unique<Var>("user_email"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // string login_username;
    decls.push_back(make_unique<Decl>("login_username",
                     make_unique<TypeConst>("string")));
    // login_username = input();
    {
        auto lhs = make_unique<Var>("login_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string login_password;
    decls.push_back(make_unique<Decl>("login_password",
                     make_unique<TypeConst>("string")));
    // login_password = input();
    {
        auto lhs = make_unique<Var>("login_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // login(login_username, login_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("login_username"));
        a.push_back(make_unique<Var>("login_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // string user_id;
    decls.push_back(make_unique<Decl>("user_id",
                     make_unique<TypeConst>("string")));
    // user_id = input();
    {
        auto lhs = make_unique<Var>("user_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // get_cart(user_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_cart", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with user cart functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- User Signup API block ---
    {
        /* pre: user_username ∉ dom(U) */
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("user_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_username"));
        callArgs.push_back(make_unique<Var>("user_password"));
        callArgs.push_back(make_unique<Var>("user_email"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: U[user_username] = UserRecord(user_password, user_email) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("user_username"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            recordArgs.push_back(make_unique<Var>("user_password"));
            recordArgs.push_back(make_unique<Var>("user_email"));
            postArgs.push_back(make_unique<FuncCall>("user_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- User Login API block ---
    {
        /* pre: U[login_username].password = login_password && user_token ∉ dom(UT) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("login_username"));
            auto userRecord = make_unique<FuncCall>("mapped_value", move(idx));
            
            vector<unique_ptr<Expr>> passwordAccess;
            passwordAccess.push_back(move(userRecord));
            passwordAccess.push_back(make_unique<Var>("password"));
            eq.push_back(make_unique<FuncCall>("field_access", move(passwordAccess)));
        }
        eq.push_back(make_unique<Var>("login_password"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("user_token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("UT"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("login_username"));
        callArgs.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: UT[user_token] = login_username */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("UT"));
            idx.push_back(make_unique<Var>("user_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("login_username"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Cart API block ---
    {
        /* pre: user_token ∈ dom(UT) && user_id ∈ dom(U) */
        vector<unique_ptr<Expr>> inDomUT;
        inDomUT.push_back(make_unique<Var>("UT"));
        inDomUT.push_back(make_unique<Var>("user_token"));
        
        vector<unique_ptr<Expr>> inDomU;
        inDomU.push_back(make_unique<Var>("U"));
        inDomU.push_back(make_unique<Var>("user_id"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomUT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomU)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_id"));
        auto callFn = make_unique<FuncCall>("get_cart", move(callArgs));

        /* post: cart_items = if user_id ∈ dom(C) then C[user_id] else [] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("cart_items"));
        
        // Build conditional expression: if user_id ∈ dom(C) then C[user_id] else []
        {
            // Condition: user_id ∈ dom(C)
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("user_id"));
            {
                vector<unique_ptr<Expr>> domC;
                domC.push_back(make_unique<Var>("C"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domC)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: C[user_id]
            vector<unique_ptr<Expr>> thenArgs;
            thenArgs.push_back(make_unique<Var>("C"));
            thenArgs.push_back(make_unique<Var>("user_id"));
            auto thenBranch = make_unique<FuncCall>("mapped_value", move(thenArgs));
            
            // Else branch: empty list []
            auto elseBranch = make_unique<FuncCall>("empty_list", vector<unique_ptr<Expr>>());
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials and data map
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("UserRecord"))));
    // User token to username map
    globals.push_back(make_unique<Decl>(
        "UT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart data map (user_id -> cart items)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CartList"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "UT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();