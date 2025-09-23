#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for register_admin → authenticate → saveBook → updateBook → getBook
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

    // register_admin(admin_username, admin_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_username"));
        a.push_back(make_unique<Var>("admin_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("register_admin", move(a))));
    }

    // admin_username = input();   (again for authentication)
    {
        auto lhs = make_unique<Var>("admin_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // admin_password = input();   (again for authentication)
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

    // string book_data;
    decls.push_back(make_unique<Decl>("book_data",
                     make_unique<TypeConst>("string")));
    // book_data = input();
    {
        auto lhs = make_unique<Var>("book_data");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // saveBook(book_id, book_data);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("book_id"));
        a.push_back(make_unique<Var>("book_data"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("saveBook", move(a))));
    }

    // book_id = input();   (for update operation)
    {
        auto lhs = make_unique<Var>("book_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string updated_book_data;
    decls.push_back(make_unique<Decl>("updated_book_data",
                     make_unique<TypeConst>("string")));
    // updated_book_data = input();
    {
        auto lhs = make_unique<Var>("updated_book_data");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // updateBook(book_id, updated_book_data);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("book_id"));
        a.push_back(make_unique<Var>("updated_book_data"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("updateBook", move(a))));
    }

    // book_id = input();   (for get operation)
    {
        auto lhs = make_unique<Var>("book_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // getBook(book_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("book_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("getBook", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin book management functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Register Admin API block ---
    {
        /* pre: not_in(admin_u, dom(A)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("admin_u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("A"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_u"));
        callArgs.push_back(make_unique<Var>("admin_p"));
        auto callFn = make_unique<FuncCall>("register_admin", move(callArgs));

        /* post: A[admin_u] = admin_p */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_u"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("admin_p"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

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

    // --- Save Book API block ---
    {
        /* pre: admin_token ∈ dom(AT) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("AT"));
        inDom.push_back(make_unique<Var>("admin_token"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_id"));
        callArgs.push_back(make_unique<Var>("book_data"));
        auto callFn = make_unique<FuncCall>("saveBook", move(callArgs));

        /* post: B[book_id] = book_data */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("book_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Update Book API block ---
    {
        /* pre: admin_token ∈ dom(AT) && book_id ∈ dom(B) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("AT"));
            inDom.push_back(make_unique<Var>("admin_token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("B"));
            inDom.push_back(make_unique<Var>("book_id"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_id"));
        callArgs.push_back(make_unique<Var>("updated_book_data"));
        auto callFn = make_unique<FuncCall>("updateBook", move(callArgs));

        /* post: B[book_id] = updated_book_data */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("B"));
            idx.push_back(make_unique<Var>("book_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("updated_book_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Book API block ---
    {
        /* pre: admin_token ∈ dom(AT) && book_id ∈ dom(B) */
        vector<unique_ptr<Expr>> land;
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("AT"));
            inDom.push_back(make_unique<Var>("admin_token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        {
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("B"));
            inDom.push_back(make_unique<Var>("book_id"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("book_id"));
        auto callFn = make_unique<FuncCall>("getBook", move(callArgs));

        /* post: returns book data B[book_id] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("retrieved_book_data"));
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