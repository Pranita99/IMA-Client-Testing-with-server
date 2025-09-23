#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate(admin) → getAllRequests → reject → getAllRequests
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

    // authenticate(admin_username, admin_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_username"));
        a.push_back(make_unique<Var>("admin_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("authenticate", move(a))));
    }

    // getAllRequests();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getAllRequests", move(a))));
    }
    
    // string request_id;
    decls.push_back(make_unique<Decl>("request_id",
                     make_unique<TypeConst>("string")));
    // request_id = input();
    {
        auto lhs = make_unique<Var>("request_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // reject(request_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("request_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("reject", move(a))));
    }

    // getAllRequests(); (again to see updated list)
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getAllRequests", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin request rejection functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate Admin API block ---
    {
        /* pre: A[admin_u] = admin_p  &&  admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_u"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("admin_p"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("AT"));
            inDom.push_back(make_unique<Var>("admin_token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_u"));
        callArgs.push_back(make_unique<Var>("admin_p"));
        auto callFn = make_unique<FuncCall>("authenticate", move(callArgs));

        /* post: AT[admin_token] = admin_u */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("AT"));
            idx.push_back(make_unique<Var>("admin_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("admin_u"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get All Requests API block ---
    {
        /* pre: admin_token ∈ dom(AT) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("AT"));
        inDom.push_back(make_unique<Var>("admin_token"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("getAllRequests", move(callArgs));

        /* post: returns all requests R */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("all_requests"));
        postArgs.push_back(make_unique<Var>("R"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Reject Request API block ---
    {
        /* pre: admin_token ∈ dom(AT) && request_id ∈ dom(R) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("AT"));
            inDom.push_back(make_unique<Var>("admin_token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("R"));
            inDom.push_back(make_unique<Var>("request_id"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("request_id"));
        auto callFn = make_unique<FuncCall>("reject", move(callArgs));

        /* post: request_id ∉ dom(R) && RR[request_id] = "rejected" */
        vector<unique_ptr<Expr>> land_post;
        {
            vector<unique_ptr<Expr>> notInArgs;
            notInArgs.push_back(make_unique<Var>("request_id"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("R"));
                notInArgs.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            land_post.push_back(make_unique<FuncCall>("not_in", move(notInArgs)));
        }
        {
            vector<unique_ptr<Expr>> rejectedArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("RR"));
                idx.push_back(make_unique<Var>("request_id"));
                rejectedArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            rejectedArgs.push_back(make_unique<StringLiteral>("rejected"));
            land_post.push_back(make_unique<FuncCall>("equals", move(rejectedArgs)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(land_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Admin credentials map: A[admin_username] = admin_password
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin tokens map: AT[admin_token] = admin_username  
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Requests map: R[request_id] = book_id
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Rejected Requests map: RR[request_id] = "rejected"
    globals.push_back(make_unique<Decl>(
        "RR", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "RR", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();