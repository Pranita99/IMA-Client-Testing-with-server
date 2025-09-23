#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for register_student → authenticate → saveRequest(overlapping) → accept(fail)
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string student_id;
    decls.push_back(make_unique<Decl>("student_id",
                     make_unique<TypeConst>("string")));
    // student_id = input();
    {
        auto lhs = make_unique<Var>("student_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string student_name;
    decls.push_back(make_unique<Decl>("student_name",
                     make_unique<TypeConst>("string")));
    // student_name = input();
    {
        auto lhs = make_unique<Var>("student_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string student_email;
    decls.push_back(make_unique<Decl>("student_email",
                     make_unique<TypeConst>("string")));
    // student_email = input();
    {
        auto lhs = make_unique<Var>("student_email");
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

    // register_student(student_id, student_name, student_email, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_id"));
        a.push_back(make_unique<Var>("student_name"));
        a.push_back(make_unique<Var>("student_email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("register_student", move(a))));
    }

    // authenticate(student_id, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_id"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("authenticate", move(a))));
    }

    // string token;
    decls.push_back(make_unique<Decl>("token",
                     make_unique<TypeConst>("string")));
    // token = input(); // Assume token received from authentication
    {
        auto lhs = make_unique<Var>("token");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
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

    // string request_description;
    decls.push_back(make_unique<Decl>("request_description",
                     make_unique<TypeConst>("string")));
    // request_description = input();
    {
        auto lhs = make_unique<Var>("request_description");
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

    // string book_id;
    decls.push_back(make_unique<Decl>("book_id",
                     make_unique<TypeConst>("string")));
    // book_id = input();
    {
        auto lhs = make_unique<Var>("book_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // saveRequest(token, request_id, request_type, request_description, priority, book_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("request_id"));
        a.push_back(make_unique<Var>("request_type"));
        a.push_back(make_unique<Var>("request_description"));
        a.push_back(make_unique<Var>("priority"));
        a.push_back(make_unique<Var>("book_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveRequest", move(a))));
    }

    // string admin_token;
    decls.push_back(make_unique<Decl>("admin_token",
                     make_unique<TypeConst>("string")));
    // admin_token = input(); // Assume admin token for accepting request
    {
        auto lhs = make_unique<Var>("admin_token");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // accept(admin_token, request_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_token"));
        a.push_back(make_unique<Var>("request_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("accept", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with overlapping request handling and failing accept
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Register Student API block ---
    {
        /* pre: student_id ∉ dom(S) */
        vector<unique_ptr<Expr>> notInArgs;
        notInArgs.push_back(make_unique<Var>("student_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("S"));
            notInArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("student_id"));
        callArgs.push_back(make_unique<Var>("name"));
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("register_student", move(callArgs));

        /* post: S[student_id] = {name: name, email: email, password: password} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("S"));
            idx.push_back(make_unique<Var>("student_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> record;
            record.push_back(make_unique<Var>("name"));
            record.push_back(make_unique<Var>("email"));
            record.push_back(make_unique<Var>("password"));
            postArgs.push_back(make_unique<FuncCall>("student_record", move(record)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Authenticate API block ---
    {
        /* pre: in(student_id, dom(S)) && S[student_id].password = p && token ∉ dom(T) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("student_id"));
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
                passArgs.push_back(make_unique<Var>("student_id"));
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
        callArgs.push_back(make_unique<Var>("student_id"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("authenticate", move(callArgs));

        /* post: T[token] = student_id */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("T"));
            idx.push_back(make_unique<Var>("token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("student_id"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Save Request API block (handles overlapping requests) ---
    {
        /* pre: token ∈ dom(T) && T[token] ∈ dom(S) && not_in(request_id, dom(R)) && 
               has_overlapping_request(T[token], book_id, R) */
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
        {
            vector<unique_ptr<Expr>> notInArgs;
            notInArgs.push_back(make_unique<Var>("request_id"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("R"));
                notInArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInArgs)));
        }
        {
            vector<unique_ptr<Expr>> overlapArgs;
            {
                vector<unique_ptr<Expr>> tokenArgs;
                tokenArgs.push_back(make_unique<Var>("T"));
                tokenArgs.push_back(make_unique<Var>("token"));
                overlapArgs.push_back(make_unique<FuncCall>("mapped_value", move(tokenArgs)));
            }
            overlapArgs.push_back(make_unique<Var>("book_id"));
            overlapArgs.push_back(make_unique<Var>("R"));
            land.push_back(make_unique<FuncCall>("has_overlapping_request", move(overlapArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("request_id"));
        callArgs.push_back(make_unique<Var>("type"));
        callArgs.push_back(make_unique<Var>("description"));
        callArgs.push_back(make_unique<Var>("priority"));
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("saveRequest", move(callArgs));

        /* post: R[request_id] = {type: type, description: description, priority: priority, 
                                 student_id: T[token], book_id: book_id, status: "overlapping"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("R"));
            idx.push_back(make_unique<Var>("request_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> record;
            record.push_back(make_unique<Var>("type"));
            record.push_back(make_unique<Var>("description"));
            record.push_back(make_unique<Var>("priority"));
            {
                vector<unique_ptr<Expr>> tokenArgs;
                tokenArgs.push_back(make_unique<Var>("T"));
                tokenArgs.push_back(make_unique<Var>("token"));
                record.push_back(make_unique<FuncCall>("mapped_value", move(tokenArgs)));
            }
            record.push_back(make_unique<Var>("book_id"));
            record.push_back(make_unique<Var>("overlapping"));
            postArgs.push_back(make_unique<FuncCall>("overlapping_request_record", move(record)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());  // Changed from CONFLICT_409
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Accept API block (designed to fail) ---
    {
        /* pre: admin_token ∈ dom(A) && request_id ∈ dom(R) && R[request_id].status = "pending" && 
               book_id ∉ dom(BS) && book_available(R[request_id].book_id) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("admin_token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("A"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("request_id"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("R"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            {
                vector<unique_ptr<Expr>> statusArgs;
                statusArgs.push_back(make_unique<Var>("R"));
                statusArgs.push_back(make_unique<Var>("request_id"));
                eq.push_back(make_unique<FuncCall>("get_status", move(statusArgs)));
            }
            eq.push_back(make_unique<Var>("pending"));
            land.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> availableArgs;
            {
                vector<unique_ptr<Expr>> bookArgs;
                bookArgs.push_back(make_unique<Var>("R"));
                bookArgs.push_back(make_unique<Var>("request_id"));
                availableArgs.push_back(make_unique<FuncCall>("get_book_id", move(bookArgs)));
            }
            availableArgs.push_back(make_unique<Var>("BS"));
            land.push_back(make_unique<FuncCall>("book_available", move(availableArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_token"));
        callArgs.push_back(make_unique<Var>("request_id"));
        auto callFn = make_unique<FuncCall>("accept", move(callArgs));

        /* post: failure due to overlapping status - returns error */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("CANNOT_ACCEPT_OVERLAPPING_REQUEST"));
        {
            vector<unique_ptr<Expr>> statusArgs;
            statusArgs.push_back(make_unique<Var>("R"));
            statusArgs.push_back(make_unique<Var>("request_id"));
            errorArgs.push_back(make_unique<FuncCall>("get_status", move(statusArgs)));
        }
        auto post = make_unique<FuncCall>("error_response", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Alternative Accept API block (fails due to overlapping status) ---
    {
        /* pre: admin_token ∈ dom(A) && request_id ∈ dom(R) && R[request_id].status = "overlapping" */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("admin_token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("A"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("request_id"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("R"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            {
                vector<unique_ptr<Expr>> statusArgs;
                statusArgs.push_back(make_unique<Var>("R"));
                statusArgs.push_back(make_unique<Var>("request_id"));
                eq.push_back(make_unique<FuncCall>("get_status", move(statusArgs)));
            }
            eq.push_back(make_unique<Var>("overlapping"));
            land.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_token"));
        callArgs.push_back(make_unique<Var>("request_id"));
        auto callFn = make_unique<FuncCall>("accept", move(callArgs));

        /* post: failure response */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("CANNOT_ACCEPT_OVERLAPPING_REQUEST"));
        {
            vector<unique_ptr<Expr>> reasonArgs;
            reasonArgs.push_back(make_unique<Var>("R"));
            reasonArgs.push_back(make_unique<Var>("request_id"));
            errorArgs.push_back(make_unique<FuncCall>("get_overlap_reason", move(reasonArgs)));
        }
        auto post = make_unique<FuncCall>("error_response", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());  // Changed from CONFLICT_409
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Students map: S[student_id] = {name, email, password}
    globals.push_back(make_unique<Decl>(
        "S", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("StudentRecord"))));
    // Tokens map: T[token] = student_id
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Requests map: R[request_id] = {type, description, priority, student_id, book_id, status}
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("RequestRecord"))));
    // Admin tokens map: A[admin_token] = admin_id
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Books map: B[book_id] = {title, author, isbn, available_copies}
    globals.push_back(make_unique<Decl>(
        "B", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("BookRecord"))));
    // Book-Student assignments: BS[book_id] = {student_id, assignment_date, status}
    globals.push_back(make_unique<Decl>(
        "BS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("BookStudentRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "S", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "B", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "BS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();