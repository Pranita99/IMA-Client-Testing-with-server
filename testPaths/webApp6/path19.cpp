#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for authenticate(admin) → deleteBook(nonexistent_id) → getBook
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

    // string nonexistent_book_id;
    decls.push_back(make_unique<Decl>("nonexistent_book_id",
                     make_unique<TypeConst>("string")));
    // nonexistent_book_id = input();
    {
        auto lhs = make_unique<Var>("nonexistent_book_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    
    // deleteBook(nonexistent_book_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("nonexistent_book_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("deleteBook", move(a))));
    }

    // string search_book_id;
    decls.push_back(make_unique<Decl>("search_book_id",
                     make_unique<TypeConst>("string")));
    // search_book_id = input();
    {
        auto lhs = make_unique<Var>("search_book_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // getBook(search_book_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("search_book_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getBook", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin authentication, book deletion, and book retrieval functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Authenticate API block ---
    {
        /* pre: A[admin_u] = admin_p  &&  not_in(admin_token, dom(AT)) */
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
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("admin_token"));
            {
                vector<unique_ptr<Expr>> domAT;
                domAT.push_back(make_unique<Var>("AT"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(domAT)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
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

    // --- Delete Book API block (for nonexistent book) ---
    {
        /* pre: admin_token ∈ dom(AT)  &&  not_in(book_id, dom(B)) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> domAT;
            domAT.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(domAT)));
        }

        vector<unique_ptr<Expr>> notInDomB;
        notInDomB.push_back(make_unique<Var>("book_id"));
        {
            vector<unique_ptr<Expr>> domB;
            domB.push_back(make_unique<Var>("B"));
            notInDomB.push_back(make_unique<FuncCall>("dom", move(domB)));
        }

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomB)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("deleteBook", move(callArgs));

        /* post: error_response = "Book not found for deletion" */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("error_response"));
        postArgs.push_back(make_unique<Var>("book_delete_not_found"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Book API block ---
    {
        /* pre: admin_token ∈ dom(AT)  &&  book_id ∈ dom(B) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> domAT;
            domAT.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(domAT)));
        }

        vector<unique_ptr<Expr>> inDomB;
        inDomB.push_back(make_unique<Var>("book_id"));
        {
            vector<unique_ptr<Expr>> domB;
            domB.push_back(make_unique<Var>("B"));
            inDomB.push_back(make_unique<FuncCall>("dom", move(domB)));
        }

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomB)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("getBook", move(callArgs));

        /* post: returns book data B[book_id] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<FuncCall>("book_data", vector<unique_ptr<Expr>>{}));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_id"));
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
    // Books map: B[book_id] = book_data
    globals.push_back(make_unique<Decl>(
        "B", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "B", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();