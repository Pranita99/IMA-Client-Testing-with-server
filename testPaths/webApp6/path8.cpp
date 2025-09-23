#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate(student) → getAllStudents
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

    // authenticate(student_username, student_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_username"));
        a.push_back(make_unique<Var>("student_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("authenticate", move(a))));
    }

    // string student_token;
    decls.push_back(make_unique<Decl>("student_token",
                     make_unique<TypeConst>("string")));
    // student_token = input(); // Assume token received from authentication
    {
        auto lhs = make_unique<Var>("student_token");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // getAllStudents(student_token);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_token"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getAllStudents", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with student authentication and getAllStudents operations
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate Student API block ---
    {
        /* pre: in(u, dom(S)) && S[u].password = p && token ∉ dom(T) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("u"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("S"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            {
                vector<unique_ptr<Expr>> passArgs;
                passArgs.push_back(make_unique<Var>("S"));
                passArgs.push_back(make_unique<Var>("u"));
                eq.push_back(make_unique<FuncCall>("get_password", move(passArgs)));
            }
            eq.push_back(make_unique<Var>("p"));
            land.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> notInArgs;
            notInArgs.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                notInArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("authenticate", move(callArgs));

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

    // --- Get All Students API block ---
    {
        /* pre: token ∈ dom(T) && T[token] ∈ dom(S) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> inArgs;
            {
                vector<unique_ptr<Expr>> tokenArgs;
                tokenArgs.push_back(make_unique<Var>("T"));
                tokenArgs.push_back(make_unique<Var>("token"));
                inArgs.push_back(make_unique<FuncCall>("mapped_value", move(tokenArgs)));
            }
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("S"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        auto callFn = make_unique<FuncCall>("getAllStudents", move(callArgs));

        /* post: returns all student records from S */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> allStudentsArgs;
            allStudentsArgs.push_back(make_unique<Var>("S"));
            postArgs.push_back(make_unique<FuncCall>("all_values", move(allStudentsArgs)));
        }
        postArgs.push_back(make_unique<Var>("all_student_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Students map: S[username] = {password, email}
    globals.push_back(make_unique<Decl>(
        "S", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("StudentRecord"))));
    // Tokens map: T[token] = username
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "S", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();