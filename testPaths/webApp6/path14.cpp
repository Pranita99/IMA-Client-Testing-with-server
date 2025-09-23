#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate(admin) → getBookStudentsByBookId → getBookStudentById
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

    // string book_students_data;
    decls.push_back(make_unique<Decl>("book_students_data",
                     make_unique<TypeConst>("string")));
    
    // book_students_data = getBookStudentsByBookId(token, book_id);
    {
        auto lhs = make_unique<Var>("book_students_data");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        args.push_back(make_unique<Var>("book_id"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("getBookStudentsByBookId", move(args))));
    }

    // string book_student_id;
    decls.push_back(make_unique<Decl>("book_student_id",
                     make_unique<TypeConst>("string")));
    // book_student_id = input();
    {
        auto lhs = make_unique<Var>("book_student_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string book_student_details;
    decls.push_back(make_unique<Decl>("book_student_details",
                     make_unique<TypeConst>("string")));
    
    // book_student_details = getBookStudentById(token, book_student_id);
    {
        auto lhs = make_unique<Var>("book_student_details");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        args.push_back(make_unique<Var>("book_student_id"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("getBookStudentById", move(args))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin book students management functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate Admin API block ---
    {
        /* pre: username ∈ dom(ADMINS)  &&  ADMINS[username] = password */
        vector<unique_ptr<Expr>> inDomAdmins;
        inDomAdmins.push_back(make_unique<Var>("username"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("ADMINS"));
            inDomAdmins.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ADMINS"));
            idx.push_back(make_unique<Var>("username"));
            passwordMatch.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        passwordMatch.push_back(make_unique<Var>("password"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAdmins)));
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

    // --- Get Book Students By Book ID API block ---
    {
        /* pre: token ∈ dom(T)  &&  book_id ∈ dom(BOOKS)  &&  is_admin(T[token]) */
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
        
        vector<unique_ptr<Expr>> adminCheck;
        {
            vector<unique_ptr<Expr>> tokenUserIdx;
            tokenUserIdx.push_back(make_unique<Var>("T"));
            tokenUserIdx.push_back(make_unique<Var>("token"));
            adminCheck.push_back(make_unique<FuncCall>("mapped_value", move(tokenUserIdx)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomBooks)));
        land.push_back(make_unique<FuncCall>("is_admin", move(adminCheck)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("getBookStudentsByBookId", move(callArgs));

        /* post: returns all book students for book_id */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("book_id"));
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("BOOK_STUDENTS"));
            filterArgs.push_back(make_unique<Var>("book_id"));
            postArgs.push_back(make_unique<FuncCall>("filter_book_students_by_book", move(filterArgs)));
        }
        auto post = make_unique<FuncCall>("returns_book_students", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Book Student By ID API block ---
    {
        /* pre: token ∈ dom(T)  &&  book_student_id ∈ dom(BOOK_STUDENTS)  &&  is_admin(T[token]) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> inDomBookStudents;
        inDomBookStudents.push_back(make_unique<Var>("book_student_id"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("BOOK_STUDENTS"));
            inDomBookStudents.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        
        vector<unique_ptr<Expr>> adminCheck;
        {
            vector<unique_ptr<Expr>> tokenUserIdx;
            tokenUserIdx.push_back(make_unique<Var>("T"));
            tokenUserIdx.push_back(make_unique<Var>("token"));
            adminCheck.push_back(make_unique<FuncCall>("mapped_value", move(tokenUserIdx)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomBookStudents)));
        land.push_back(make_unique<FuncCall>("is_admin", move(adminCheck)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("book_student_id"));
        auto callFn = make_unique<FuncCall>("getBookStudentById", move(callArgs));

        /* post: returns BOOK_STUDENTS[book_student_id] */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("BOOK_STUDENTS"));
            idx.push_back(make_unique<Var>("book_student_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("book_student_id"));
        auto post = make_unique<FuncCall>("returns_book_student_details", move(postArgs));

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
    // Admins map: username -> password
    globals.push_back(make_unique<Decl>(
        "ADMINS", make_unique<MapType>(
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
        "ADMINS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
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