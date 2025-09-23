#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: admin_login → create_restaurant → get_restaurants
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *admin* Program AST for basic restaurant management
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

    // admin_login(admin_username, admin_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_username"));
        a.push_back(make_unique<Var>("admin_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("admin_login", move(a))));
    }

    // string restaurant_name;
    decls.push_back(make_unique<Decl>("restaurant_name",
                     make_unique<TypeConst>("string")));
    // restaurant_name = input();
    {
        auto lhs = make_unique<Var>("restaurant_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string restaurant_address;
    decls.push_back(make_unique<Decl>("restaurant_address",
                     make_unique<TypeConst>("string")));
    // restaurant_address = input();
    {
        auto lhs = make_unique<Var>("restaurant_address");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string restaurant_cuisine;
    decls.push_back(make_unique<Decl>("restaurant_cuisine",
                     make_unique<TypeConst>("string")));
    // restaurant_cuisine = input();
    {
        auto lhs = make_unique<Var>("restaurant_cuisine");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // create_restaurant(restaurant_name, restaurant_address, restaurant_cuisine);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_name"));
        a.push_back(make_unique<Var>("restaurant_address"));
        a.push_back(make_unique<Var>("restaurant_cuisine"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("create_restaurant", move(a))));
    }

    // get_restaurants();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_restaurants", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with basic restaurant functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Admin Login API block ---
    {
        /* pre: admin_username ∈ dom(A) && A[admin_username].password = admin_password && admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("admin_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("A"));
            inDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_username"));
            auto adminRecord = make_unique<FuncCall>("mapped_value", move(idx));
            
            vector<unique_ptr<Expr>> passwordAccess;
            passwordAccess.push_back(move(adminRecord));
            passwordAccess.push_back(make_unique<Var>("password"));
            eq.push_back(make_unique<FuncCall>("field_access", move(passwordAccess)));
        }
        eq.push_back(make_unique<Var>("admin_password"));
        
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDom)));
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_username"));
        callArgs.push_back(make_unique<Var>("admin_password"));
        auto callFn = make_unique<FuncCall>("admin_login", move(callArgs));

        /* post: AT[admin_token] = admin_username */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("AT"));
            idx.push_back(make_unique<Var>("admin_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("admin_username"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Create Restaurant API block ---
    {
        /* pre: admin_token ∈ dom(AT) && restaurant_name ∉ dom(R) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> notInDomR;
        notInDomR.push_back(make_unique<Var>("restaurant_name"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            notInDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_name"));
        callArgs.push_back(make_unique<Var>("restaurant_address"));
        callArgs.push_back(make_unique<Var>("restaurant_cuisine"));
        auto callFn = make_unique<FuncCall>("create_restaurant", move(callArgs));

        /* post: R[restaurant_name] = RestaurantRecord(restaurant_address, restaurant_cuisine) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("R"));
            idx.push_back(make_unique<Var>("restaurant_name"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            recordArgs.push_back(make_unique<Var>("restaurant_address"));
            recordArgs.push_back(make_unique<Var>("restaurant_cuisine"));
            postArgs.push_back(make_unique<FuncCall>("restaurant_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Restaurants API block ---
    {
        /* pre: true (no precondition - anyone can view restaurants) */
        auto pre = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>());

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_restaurants", move(callArgs));

        /* post: restaurant_list = values(R) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("restaurant_list"));
        {
            vector<unique_ptr<Expr>> valuesArgs;
            valuesArgs.push_back(make_unique<Var>("R"));
            postArgs.push_back(make_unique<FuncCall>("values", move(valuesArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Admin credentials map
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("AdminRecord"))));
    // Admin token to username map
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map (restaurant_name -> restaurant_record)
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("RestaurantRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();