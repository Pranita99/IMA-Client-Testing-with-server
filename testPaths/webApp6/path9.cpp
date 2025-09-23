#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate → saveBook → getBook
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

    // authenticate(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
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

    // saveBook(token, book_id, book_title, book_author, book_isbn);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("book_id"));
        a.push_back(make_unique<Var>("book_title"));
        a.push_back(make_unique<Var>("book_author"));
        a.push_back(make_unique<Var>("book_isbn"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveBook", move(a))));
    }

    // getBook(token, book_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("token"));
        a.push_back(make_unique<Var>("book_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getBook", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with book management operations
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate API block ---
    {
        /* pre: in(u, dom(U)) && U[u].password = p && token ∉ dom(T) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("u"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("U"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            {
                vector<unique_ptr<Expr>> passArgs;
                passArgs.push_back(make_unique<Var>("U"));
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

    // --- Save Book API block ---
    {
        /* pre: token ∈ dom(T) && T[token] ∈ dom(U) && not_in(book_id, dom(B)) */
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
                domArgs.push_back(make_unique<Var>("U"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> notInArgs;
            notInArgs.push_back(make_unique<Var>("book_id"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("B"));
                notInArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("book_id"));
        callArgs.push_back(make_unique<Var>("title"));
        callArgs.push_back(make_unique<Var>("author"));
        callArgs.push_back(make_unique<Var>("isbn"));
        auto callFn = make_unique<FuncCall>("saveBook", move(callArgs));

        /* post: B[book_id] = {title: title, author: author, isbn: isbn} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> record;
            record.push_back(make_unique<Var>("title"));
            record.push_back(make_unique<Var>("author"));
            record.push_back(make_unique<Var>("isbn"));
            postArgs.push_back(make_unique<FuncCall>("book_record", move(record)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Book API block ---
    {
        /* pre: token ∈ dom(T) && T[token] ∈ dom(U) && book_id ∈ dom(B) */
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
                domArgs.push_back(make_unique<Var>("U"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("book_id"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("B"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            land.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("token"));
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("getBook", move(callArgs));

        /* post: returns B[book_id] */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> bookArgs;
            bookArgs.push_back(make_unique<Var>("B"));
            bookArgs.push_back(make_unique<Var>("book_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(bookArgs)));
        }
        postArgs.push_back(make_unique<Var>("book_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Users map: U[username] = {password, ...}
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("UserRecord"))));
    // Tokens map: T[token] = username
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Books map: B[book_id] = {title, author, isbn}
    globals.push_back(make_unique<Decl>(
        "B", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("BookRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "B", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();