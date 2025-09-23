#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup → login → add_to_cart → logout → login → view_cart → place_order
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

    // signup(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // username = input();   (again for login)
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input();   (again for login)
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // login(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // string item_id;
    decls.push_back(make_unique<Decl>("item_id",
                     make_unique<TypeConst>("string")));
    // item_id = input();
    {
        auto lhs = make_unique<Var>("item_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string quantity;
    decls.push_back(make_unique<Decl>("quantity",
                     make_unique<TypeConst>("string")));
    // quantity = input();
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_to_cart(item_id, quantity);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // logout();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    // username = input();   (again for second login)
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input();   (again for second login)
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // login(username, password);   (second login)
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // view_cart();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // string delivery_address;
    decls.push_back(make_unique<Decl>("delivery_address",
                     make_unique<TypeConst>("string")));
    // delivery_address = input();
    {
        auto lhs = make_unique<Var>("delivery_address");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // place_order(delivery_address);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("delivery_address"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with restaurant functionality including logout and place_order
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Signup API block ---
    {
        /* pre: not_in(u, dom(U)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: U[u] = p */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("u"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Login API block ---
    {
        /* pre: U[u] = p  &&  not_in(token, dom(T)) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("u"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("p"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domT;
                domT.push_back(make_unique<Var>("T"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(domT)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

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

    // --- Add to Cart API block ---
    {
        /* pre: token ∈ dom(T) && item_id ∈ dom(M) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
       
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("item_id"));
        {
            vector<unique_ptr<Expr>> domM;
            domM.push_back(make_unique<Var>("M"));
            inDomM.push_back(make_unique<FuncCall>("dom", move(domM)));
        }
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_id"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[T[token]][item_id] = quantity */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("C"));
            cartIdx.push_back(std::move(userId));
            cartIdx.push_back(make_unique<Var>("item_id"));
            postArgs.push_back(make_unique<FuncCall>("nested_mapped_value", move(cartIdx)));
        }
        postArgs.push_back(make_unique<Var>("quantity"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Logout API block ---
    {
        /* pre: token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDom.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("logout", move(callArgs));

        /* post: not_in(token, dom(T)) - token is removed from T */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            postArgs.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        auto post = make_unique<FuncCall>("not_in", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- View Cart API block ---
    {
        /* pre: token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDom.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: returns cart contents for current user C[T[token]] */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("C"));
            cartIdx.push_back(std::move(userId));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(cartIdx)));
        }
        postArgs.push_back(make_unique<FuncCall>("cart_data", vector<unique_ptr<Expr>>{}));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Place Order API block ---
    {
        /* pre: token ∈ dom(T) && not_empty(C[T[token]]) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDom.push_back(make_unique<FuncCall>("dom", move(domT)));
        }

        vector<unique_ptr<Expr>> notEmpty;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("C"));
            cartIdx.push_back(std::move(userId));
            notEmpty.push_back(make_unique<FuncCall>("mapped_value", move(cartIdx)));
        }

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDom)));
        land.push_back(make_unique<FuncCall>("not_empty", move(notEmpty)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("delivery_address"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: O[order_id] = {user: T[token], items: C[T[token]], address: delivery_address, status: "placed"} 
                 && C[T[token]] = {} (cart is cleared) */
        vector<unique_ptr<Expr>> orderPost;
        {
            vector<unique_ptr<Expr>> orderIdx;
            orderIdx.push_back(make_unique<Var>("O"));
            orderIdx.push_back(make_unique<Var>("order_id"));
            orderPost.push_back(make_unique<FuncCall>("mapped_value", move(orderIdx)));
        }
        {
            vector<unique_ptr<Expr>> orderData;
            // user field
            {
                vector<unique_ptr<Expr>> userIdx;
                userIdx.push_back(make_unique<Var>("T"));
                userIdx.push_back(make_unique<Var>("token"));
                orderData.push_back(make_unique<FuncCall>("mapped_value", move(userIdx)));
            }
            // items field (previous cart contents)
            orderData.push_back(make_unique<Var>("delivery_address"));
            orderData.push_back(make_unique<Var>("placed"));
            orderPost.push_back(make_unique<FuncCall>("order_object", move(orderData)));
        }

        vector<unique_ptr<Expr>> cartCleared;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("C"));
            cartIdx.push_back(std::move(userId));
            cartCleared.push_back(make_unique<FuncCall>("mapped_value", move(cartIdx)));
        }
        cartCleared.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>{}));

        vector<unique_ptr<Expr>> postCond;
        postCond.push_back(make_unique<FuncCall>("equals", move(orderPost)));
        postCond.push_back(make_unique<FuncCall>("equals", move(cartCleared)));
        auto post = make_unique<FuncCall>("and_operator", move(postCond));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials map
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Token to user map
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Menu items map
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart data map (user_id -> item_id -> quantity)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("string")))));
    // Orders map (order_id -> order_details)
    globals.push_back(make_unique<Decl>(
        "O", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "M", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "O", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();