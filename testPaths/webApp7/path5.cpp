#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup → login → get_restaurants → get_restaurant_menu → add_to_cart → place_order
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // ═══ SIGNUP FLOW ═══
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

    // ═══ LOGIN FLOW ═══
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
   
    // ═══ GET RESTAURANTS ═══
    // get_restaurants();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_restaurants", move(a))));
    }

    // ═══ GET RESTAURANT MENU ═══
    // string restaurant_id;
    decls.push_back(make_unique<Decl>("restaurant_id",
                     make_unique<TypeConst>("string")));
    // restaurant_id = input();
    {
        auto lhs = make_unique<Var>("restaurant_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // get_restaurant_menu(restaurant_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_restaurant_menu", move(a))));
    }

    // ═══ ADD TO CART ═══
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

    // ═══ PLACE ORDER ═══
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

    // string payment_method;
    decls.push_back(make_unique<Decl>("payment_method",
                     make_unique<TypeConst>("string")));
    // payment_method = input();
    {
        auto lhs = make_unique<Var>("payment_method");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // place_order(delivery_address, payment_method);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("delivery_address"));
        a.push_back(make_unique<Var>("payment_method"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with restaurant functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══ SIGNUP API BLOCK ═══
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

    // ═══ LOGIN API BLOCK ═══
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
        
        vector<unique_ptr<Expr>> notInToken;
        notInToken.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            notInToken.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInToken)));
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

    // ═══ GET RESTAURANTS API BLOCK ═══
    {
        /* pre: in_dom(token, T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("token"));
        inDom.push_back(make_unique<Var>("T"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_restaurants", move(callArgs));

        /* post: returns list of restaurants (simplified as true condition) */
        auto post = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>{});

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══ GET RESTAURANT MENU API BLOCK ═══
    {
        /* pre: in_dom(token, T) && in_dom(restaurant_id, R) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        inDomT.push_back(make_unique<Var>("T"));
       
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        inDomR.push_back(make_unique<Var>("R"));
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        auto callFn = make_unique<FuncCall>("get_restaurant_menu", move(callArgs));

        /* post: returns menu for restaurant_id */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("R"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<FuncCall>("menu", vector<unique_ptr<Expr>>{}));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══ ADD TO CART API BLOCK ═══
    {
        /* pre: in_dom(token, T) && in_dom(item_id, M) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        inDomT.push_back(make_unique<Var>("T"));
       
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("item_id"));
        inDomM.push_back(make_unique<Var>("M"));
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_id"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[user_id][item_id] = quantity (where user_id = T[token]) */
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

    // ═══ PLACE ORDER API BLOCK ═══
    {
        /* pre: in_dom(token, T) && cart_not_empty(user_id) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("token"));
        inDomT.push_back(make_unique<Var>("T"));
       
        // Check if user has items in cart (simplified)
        vector<unique_ptr<Expr>> cartNotEmpty;
        {
            vector<unique_ptr<Expr>> userIdx;
            userIdx.push_back(make_unique<Var>("T"));
            userIdx.push_back(make_unique<Var>("token"));
            auto userId = make_unique<FuncCall>("mapped_value", move(userIdx));
           
            vector<unique_ptr<Expr>> cartCheck;
            cartCheck.push_back(make_unique<Var>("C"));
            cartCheck.push_back(std::move(userId));
            cartNotEmpty.push_back(make_unique<FuncCall>("in_dom", move(cartCheck)));
        }
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("true", move(cartNotEmpty))); // Simplified check
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("delivery_address"));
        callArgs.push_back(make_unique<Var>("payment_method"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: O[order_id] = order_details && C[user_id] = empty */
        vector<unique_ptr<Expr>> postArgs;
        {
            // Create order entry
            vector<unique_ptr<Expr>> orderIdx;
            orderIdx.push_back(make_unique<Var>("O"));
            orderIdx.push_back(make_unique<Var>("order_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(orderIdx)));
            
            // Order details include user, items, address, payment
            vector<unique_ptr<Expr>> orderDetails;
            {
                vector<unique_ptr<Expr>> userIdx;
                userIdx.push_back(make_unique<Var>("T"));
                userIdx.push_back(make_unique<Var>("token"));
                orderDetails.push_back(make_unique<FuncCall>("mapped_value", move(userIdx)));
            }
            orderDetails.push_back(make_unique<Var>("delivery_address"));
            orderDetails.push_back(make_unique<Var>("payment_method"));
            postArgs.push_back(make_unique<FuncCall>("order_data", move(orderDetails)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══ GLOBALS & INITIALIZATIONS ═══
    vector<unique_ptr<Decl>> globals;
    // User credentials map: username -> password
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Token to user map: token -> username
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map: restaurant_id -> restaurant_data
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Menu items map: item_id -> item_data
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Orders map: order_id -> order_details
    globals.push_back(make_unique<Decl>(
        "O", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart data map: user_id -> (item_id -> quantity)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("string")))));

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
        "O", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── GLOBALS THE DRIVER EXPECTS ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();