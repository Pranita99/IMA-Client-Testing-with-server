#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate → saveBookStudent → getAllBooksOfStudent
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

    // string enrollment_date;
    decls.push_back(make_unique<Decl>("enrollment_date",
                     make_unique<TypeConst>("string")));
    // enrollment_date = input();
    {
        auto lhs = make_unique<Var>("enrollment_date");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string status;
    decls.push_back(make_unique<Decl>("status",
                     make_unique<TypeConst>("string")));
    // status = input();
    {
        auto lhs = make_unique<Var>("status");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // saveBookStudent(token, book_id, enrollment_date, status);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("book_id"));
        a.push_back(make_unique<Var>("enrollment_date"));
        a.push_back(make_unique<Var>("status"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveBookStudent", move(a))));
    }

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

    // string all_books_data;
    decls.push_back(make_unique<Decl>("all_books_data",
                     make_unique<TypeConst>("string")));
    
    // all_books_data = getAllBooksOfStudent(token, student_id);
    {
        auto lhs = make_unique<Var>("all_books_data");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        args.push_back(make_unique<Var>("student_id"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("getAllBooksOfStudent", move(args))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with book student management functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate API block ---
    {
        /* pre: username ∈ dom(USERS)  &&  USERS[username] = password */
        vector<unique_ptr<Expr>> inDomUsers;
        inDomUsers.push_back(make_unique<Var>("username"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("USERS"));
            inDomUsers.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("USERS"));
            idx.push_back(make_unique<Var>("username"));
            passwordMatch.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        passwordMatch.push_back(make_unique<Var>("password"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomUsers)));
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

    // --- Save Book Student API block ---
    {
        /* pre: token ∈ dom(T)  &&  book_id ∈ dom(BOOKS)  &&  valid_status(status) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> inDomBooks;
        inDomBooks.push_back(make_unique<Var>("book_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("BOOKS"));
            inDomBooks.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> validStatusArgs;
        validStatusArgs.push_back(make_unique<Var>("status"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomBooks)));
        land.push_back(make_unique<FuncCall>("valid_status", move(validStatusArgs)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("book_id"));
        callArgs.push_back(make_unique<Var>("enrollment_date"));
        callArgs.push_back(make_unique<Var>("status"));
        auto callFn = make_unique<FuncCall>("saveBookStudent", move(callArgs));

        /* post: BOOK_STUDENTS[book_student_id] = {student: T[token], book: book_id, enrollment_date: enrollment_date, status: status} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("BOOK_STUDENTS"));
            idx.push_back(make_unique<Var>("book_student_id"));
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
            recordArgs.push_back(make_unique<Var>("book_id"));
            recordArgs.push_back(make_unique<Var>("enrollment_date"));
            recordArgs.push_back(make_unique<Var>("status"));
            postArgs.push_back(make_unique<FuncCall>("book_student_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get All Books Of Student API block ---
    {
        /* pre: token ∈ dom(T)  &&  student_id ∈ dom(STUDENTS) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> inDomStudents;
        inDomStudents.push_back(make_unique<Var>("student_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("STUDENTS"));
            inDomStudents.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomStudents)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("student_id"));
        auto callFn = make_unique<FuncCall>("getAllBooksOfStudent", move(callArgs));

        /* post: returns all books for student_id */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("student_id"));
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("BOOK_STUDENTS"));
            filterArgs.push_back(make_unique<Var>("student_id"));
            postArgs.push_back(make_unique<FuncCall>("filter_books_by_student", move(filterArgs)));
        }
        auto post = make_unique<FuncCall>("returns_student_books", move(postArgs));

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
    // Users map: username -> password
    globals.push_back(make_unique<Decl>(
        "USERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Students map: student_id -> student_details
    globals.push_back(make_unique<Decl>(
        "STUDENTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Books map: book_id -> book_details
    globals.push_back(make_unique<Decl>(
        "BOOKS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Book Students map: book_student_id -> book_student_record
    globals.push_back(make_unique<Decl>(
        "BOOK_STUDENTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "USERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "STUDENTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "BOOKS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "BOOK_STUDENTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();