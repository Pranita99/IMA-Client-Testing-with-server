#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for register_student → saveBook → getBook
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

    // register_student(student_username, student_password, student_email);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("student_username"));
        a.push_back(make_unique<Var>("student_password"));
        a.push_back(make_unique<Var>("student_email"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("register_student", move(a))));
    }

    // string book_title;
    decls.push_back(make_unique<Decl>("book_title",
                     make_unique<TypeConst>("string")));
    // book_title = input();
    {
        auto lhs = make_unique<Var>("book_title");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string book_author;
    decls.push_back(make_unique<Decl>("book_author",
                     make_unique<TypeConst>("string")));
    // book_author = input();
    {
        auto lhs = make_unique<Var>("book_author");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string book_isbn;
    decls.push_back(make_unique<Decl>("book_isbn",
                     make_unique<TypeConst>("string")));
    // book_isbn = input();
    {
        auto lhs = make_unique<Var>("book_isbn");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // saveBook(book_title, book_author, book_isbn);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("book_title"));
        a.push_back(make_unique<Var>("book_author"));
        a.push_back(make_unique<Var>("book_isbn"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveBook", move(a))));
    }

    // string search_isbn;
    decls.push_back(make_unique<Decl>("search_isbn",
                     make_unique<TypeConst>("string")));
    // search_isbn = input();
    {
        auto lhs = make_unique<Var>("search_isbn");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // getBook(search_isbn);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("search_isbn"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getBook", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with student registration and book management functionality
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
        callArgs.push_back(make_unique<Var>("student_e"));
        auto callFn = make_unique<FuncCall>("register_student", move(callArgs));

        /* post: S[student_u] = {password: student_p, email: student_e} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("S"));
            idx.push_back(make_unique<Var>("student_u"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> studentData;
            studentData.push_back(make_unique<Var>("student_p"));
            studentData.push_back(make_unique<Var>("student_e"));
            postArgs.push_back(make_unique<FuncCall>("student_object", move(studentData)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Save Book API block ---
    {
        /* pre: not_in(book_isbn, dom(B)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("book_isbn"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("B"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_title"));
        callArgs.push_back(make_unique<Var>("book_author"));
        callArgs.push_back(make_unique<Var>("book_isbn"));
        auto callFn = make_unique<FuncCall>("saveBook", move(callArgs));

        /* post: B[book_isbn] = {title: book_title, author: book_author} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_isbn"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> bookData;
            bookData.push_back(make_unique<Var>("book_title"));
            bookData.push_back(make_unique<Var>("book_author"));
            postArgs.push_back(make_unique<FuncCall>("book_object", move(bookData)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Book API block ---
    {
        /* pre: book_isbn ∈ dom(B) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("book_isbn"));
        {
            vector<unique_ptr<Expr>> domB;
            domB.push_back(make_unique<Var>("B"));
            inDom.push_back(make_unique<FuncCall>("dom", move(domB)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_isbn"));
        auto callFn = make_unique<FuncCall>("getBook", move(callArgs));

        /* post: returns book data B[book_isbn] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<FuncCall>("book_data", vector<unique_ptr<Expr>>{}));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_isbn"));
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
    // Students map: S[student_username] = student_data
    globals.push_back(make_unique<Decl>(
        "S", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Books map: B[book_isbn] = book_data
    globals.push_back(make_unique<Decl>(
        "B", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "S", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "B", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();