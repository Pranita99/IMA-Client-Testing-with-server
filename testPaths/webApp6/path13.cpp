#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate → save request → get all requests → delete request
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

    // string token;
    decls.push_back(make_unique<Decl>("token",
                     make_unique<TypeConst>("string")));

    // token = authenticate(username, password);
    {
        auto lhs = make_unique<Var>("token");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("authenticate", move(args))));
    }

    // string request_type;
    decls.push_back(make_unique<Decl>("request_type",
                     make_unique<TypeConst>("string")));
    // request_type = input();
    {
        auto lhs = make_unique<Var>("request_type");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string description;
    decls.push_back(make_unique<Decl>("description",
                     make_unique<TypeConst>("string")));
    // description = input();
    {
        auto lhs = make_unique<Var>("description");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string priority;
    decls.push_back(make_unique<Decl>("priority",
                     make_unique<TypeConst>("string")));
    // priority = input();
    {
        auto lhs = make_unique<Var>("priority");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // saveRequest(token, request_type, description, priority);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("request_type"));
        a.push_back(make_unique<Var>("description"));
        a.push_back(make_unique<Var>("priority"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveRequest", move(a))));
    }

    // string all_requests_data;
    decls.push_back(make_unique<Decl>("all_requests_data",
                     make_unique<TypeConst>("string")));
    
    // all_requests_data = getAllRequests(token);
    {
        auto lhs = make_unique<Var>("all_requests_data");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("getAllRequests", move(args))));
    }

    // string request_id_to_delete;
    decls.push_back(make_unique<Decl>("request_id_to_delete",
                     make_unique<TypeConst>("string")));
    // request_id_to_delete = input();
    {
        auto lhs = make_unique<Var>("request_id_to_delete");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    
    // deleteRequestById(token, request_id_to_delete);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("request_id_to_delete"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("deleteRequestById", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with student request system functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate API block ---
    {
        /* pre: username ∈ dom(STUDENTS)  &&  STUDENTS[username] = password */
        vector<unique_ptr<Expr>> inDomStudents;
        inDomStudents.push_back(make_unique<Var>("username"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("STUDENTS"));
            inDomStudents.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("STUDENTS"));
            idx.push_back(make_unique<Var>("username"));
            passwordMatch.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        passwordMatch.push_back(make_unique<Var>("password"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomStudents)));
        land.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("username"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("authenticate", move(callArgs));

        /* post: T[token] = username  &&  token is generated */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("T"));
            idx.push_back(make_unique<Var>("token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("username"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Save Request API block ---
    {
        /* pre: token ∈ dom(T)  &&  valid_request_type(request_type)  &&  valid_priority(priority) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> validTypeArgs;
        validTypeArgs.push_back(make_unique<Var>("request_type"));
        
        vector<unique_ptr<Expr>> validPriorityArgs;
        validPriorityArgs.push_back(make_unique<Var>("priority"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("valid_request_type", move(validTypeArgs)));
        land.push_back(make_unique<FuncCall>("valid_priority", move(validPriorityArgs)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("request_type"));
        callArgs.push_back(make_unique<Var>("description"));
        callArgs.push_back(make_unique<Var>("priority"));
        auto callFn = make_unique<FuncCall>("saveRequest", move(callArgs));

        /* post: REQUESTS[request_id] = {student: T[token], type: request_type, description: description, priority: priority, status: "pending"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("REQUESTS"));
            idx.push_back(make_unique<Var>("request_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            {
                vector<unique_ptr<Expr>> studentIdx;
                studentIdx.push_back(make_unique<Var>("T"));
                studentIdx.push_back(make_unique<Var>("token"));
                recordArgs.push_back(make_unique<FuncCall>("mapped_value", move(studentIdx)));
            }
            recordArgs.push_back(make_unique<Var>("request_type"));
            recordArgs.push_back(make_unique<Var>("description"));
            recordArgs.push_back(make_unique<Var>("priority"));
            recordArgs.push_back(make_unique<Var>("\"pending\""));
            postArgs.push_back(make_unique<FuncCall>("request_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get All Requests API block ---
    {
        /* pre: token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        auto callFn = make_unique<FuncCall>("getAllRequests", move(callArgs));

        /* post: returns all requests for authenticated student */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> studentIdx;
            studentIdx.push_back(make_unique<Var>("T"));
            studentIdx.push_back(make_unique<Var>("token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(studentIdx)));
        }
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("REQUESTS"));
            {
                vector<unique_ptr<Expr>> studentIdx;
                studentIdx.push_back(make_unique<Var>("T"));
                studentIdx.push_back(make_unique<Var>("token"));
                filterArgs.push_back(make_unique<FuncCall>("mapped_value", move(studentIdx)));
            }
            postArgs.push_back(make_unique<FuncCall>("filter_requests_by_student", move(filterArgs)));
        }
        auto post = make_unique<FuncCall>("returns_requests", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Delete Request By ID API block ---
    {
        /* pre: token ∈ dom(T)  &&  request_id ∈ dom(REQUESTS)  &&  REQUESTS[request_id].student = T[token] */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> inDomRequests;
        inDomRequests.push_back(make_unique<Var>("request_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("REQUESTS"));
            inDomRequests.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> ownershipCheck;
        {
            vector<unique_ptr<Expr>> requestOwnerArgs;
            requestOwnerArgs.push_back(make_unique<Var>("REQUESTS"));
            requestOwnerArgs.push_back(make_unique<Var>("request_id"));
            ownershipCheck.push_back(make_unique<FuncCall>("get_request_student", move(requestOwnerArgs)));
        }
        {
            vector<unique_ptr<Expr>> tokenOwnerIdx;
            tokenOwnerIdx.push_back(make_unique<Var>("T"));
            tokenOwnerIdx.push_back(make_unique<Var>("token"));
            ownershipCheck.push_back(make_unique<FuncCall>("mapped_value", move(tokenOwnerIdx)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomRequests)));
        land.push_back(make_unique<FuncCall>("equals", move(ownershipCheck)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("request_id"));
        auto callFn = make_unique<FuncCall>("deleteRequestById", move(callArgs));

        /* post: request_id ∉ dom(REQUESTS) */
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("request_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("REQUESTS"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto post = make_unique<FuncCall>("not_in", move(notInDom));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Token map: token -> username
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Students map: username -> password
    globals.push_back(make_unique<Decl>(
        "STUDENTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Requests map: request_id -> request_record
    globals.push_back(make_unique<Decl>(
        "REQUESTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "STUDENTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "REQUESTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();