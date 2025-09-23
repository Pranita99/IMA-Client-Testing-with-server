#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for register_student → authenticate → getStudentByUserId
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string student_username;
    decls.push_back(make_unique<Decl>("student_username",
                     make_unique<TypeConst>("string")));
    // student_username = input();
    {
        auto lhs = make_unique<Var>("student_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string student_password;
    decls.push_back(make_unique<Decl>("student_password",
                     make_unique<TypeConst>("string")));
    // student_password = input();
    {
        auto lhs = make_unique<Var>("student_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // register_student(student_username, student_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_username"));
        a.push_back(make_unique<Var>("student_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("register_student", move(a))));
    }

    // student_username = input();   (again for authentication)
    {
        auto lhs = make_unique<Var>("student_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // student_password = input();   (again for authentication)
    {
        auto lhs = make_unique<Var>("student_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // authenticate(student_username, student_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_username"));
        a.push_back(make_unique<Var>("student_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("authenticate", move(a))));
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
    
    // getStudentByUserId(user_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getStudentByUserId", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with student registration and retrieval functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Register Student API block ---
    {
        /* pre: not_in(student_u, dom(S)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("student_u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("S"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("student_u"));
        callArgs.push_back(make_unique<Var>("student_p"));
        auto callFn = make_unique<FuncCall>("register_student", move(callArgs));

        /* post: S[student_u] = student_p */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("S"));
            idx.push_back(make_unique<Var>("student_u"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("student_p"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Authenticate API block ---
    {
        /* pre: S[student_u] = student_p  &&  student_token ∉ dom(ST) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("S"));
            idx.push_back(make_unique<Var>("student_u"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("student_p"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("ST"));
            inDom.push_back(make_unique<Var>("student_token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("student_u"));
        callArgs.push_back(make_unique<Var>("student_p"));
        auto callFn = make_unique<FuncCall>("authenticate", move(callArgs));

        /* post: ST[student_token] = student_u */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ST"));
            idx.push_back(make_unique<Var>("student_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("student_u"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Student By User ID API block ---
    {
        /* pre: student_token ∈ dom(ST)  &&  user_id ∈ dom(SD) */
        vector<unique_ptr<Expr>> tokenInDom;
        tokenInDom.push_back(make_unique<Var>("ST"));
        tokenInDom.push_back(make_unique<Var>("student_token"));
        
        vector<unique_ptr<Expr>> userIdInDom;
        userIdInDom.push_back(make_unique<Var>("SD"));
        userIdInDom.push_back(make_unique<Var>("user_id"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(tokenInDom)));
        land.push_back(make_unique<FuncCall>("in_dom", move(userIdInDom)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_id"));
        auto callFn = make_unique<FuncCall>("getStudentByUserId", move(callArgs));

        /* post: returns student data SD[user_id] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("student_data"));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("SD"));
            idx.push_back(make_unique<Var>("user_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Student credentials map: S[student_username] = student_password
    globals.push_back(make_unique<Decl>(
        "S", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Student tokens map: ST[student_token] = student_username  
    globals.push_back(make_unique<Decl>(
        "ST", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Student data map: SD[user_id] = student_data
    globals.push_back(make_unique<Decl>(
        "SD", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "S", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ST", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "SD", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();