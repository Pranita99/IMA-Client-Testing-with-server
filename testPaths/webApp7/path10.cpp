#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: signup → login → get_restaurants → get_restaurant_menu 
//        → add_to_cart → clear_cart → add_to_cart → place_order
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for complete restaurant ordering flow
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
    
    // get_restaurants();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_restaurants", move(a))));
    }

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

    // clear_cart();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("clear_cart", move(a))));
    }

    // string item_id2;
    decls.push_back(make_unique<Decl>("item_id2",
                     make_unique<TypeConst>("string")));
    // item_id2 = input();
    {
        auto lhs = make_unique<Var>("item_id2");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string quantity2;
    decls.push_back(make_unique<Decl>("quantity2",
                     make_unique<TypeConst>("string")));
    // quantity2 = input();
    {
        auto lhs = make_unique<Var>("quantity2");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_to_cart(item_id2, quantity2);  (second add_to_cart after clear)
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id2"));
        a.push_back(make_unique<Var>("quantity2"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
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
//  Build the API *Spec* AST with complete restaurant functionality
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
        /* pre: U[u] = p  &&  token ∉ dom(T) */
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
            vector<unique_ptr<Expr>> inDom;
            inDom.push_back(make_unique<Var>("T"));
            inDom.push_back(make_unique<Var>("token"));
            land.push_back(make_unique<FuncCall>("in_dom", move(inDom)));
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

    // --- Get Restaurants API block ---
    {
        /* pre: token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("T"));
        inDom.push_back(make_unique<Var>("token"));
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

    // --- Get Restaurant Menu API block ---
    {
        /* pre: token ∈ dom(T) && restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("T"));
        inDomT.push_back(make_unique<Var>("token"));
        
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("R"));
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        
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

    // --- Clear Cart API block ---
    {
        /* pre: token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("T"));
        inDomT.push_back(make_unique<Var>("token"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDomT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("clear_cart", move(callArgs));

        /* post: C[user] = empty_map */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userCart;
            userCart.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenLookup;
                tokenLookup.push_back(make_unique<Var>("T"));
                tokenLookup.push_back(make_unique<Var>("token"));
                userCart.push_back(make_unique<FuncCall>("mapped_value", move(tokenLookup)));
            }
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(userCart)));
        }
        postArgs.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>{}));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add to Cart API block (second instance) ---
    {
        /* pre: token ∈ dom(T) && item_id2 ∈ dom(M) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("T"));
        inDomT.push_back(make_unique<Var>("token"));
        
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("M"));
        inDomM.push_back(make_unique<Var>("item_id2"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_id2"));
        callArgs.push_back(make_unique<Var>("quantity2"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[user][item_id2] = quantity2 */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userCart;
            userCart.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenLookup;
                tokenLookup.push_back(make_unique<Var>("T"));
                tokenLookup.push_back(make_unique<Var>("token"));
                userCart.push_back(make_unique<FuncCall>("mapped_value", move(tokenLookup)));
            }
            vector<unique_ptr<Expr>> cartItem;
            cartItem.push_back(make_unique<FuncCall>("mapped_value", move(userCart)));
            cartItem.push_back(make_unique<Var>("item_id2"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(cartItem)));
        }
        postArgs.push_back(make_unique<Var>("quantity2"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Place Order API block ---
    {
        /* pre: token ∈ dom(T) && C[user] is not empty */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("T"));
        inDomT.push_back(make_unique<Var>("token"));
        
        vector<unique_ptr<Expr>> cartNotEmpty;
        {
            vector<unique_ptr<Expr>> userCart;
            userCart.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenLookup;
                tokenLookup.push_back(make_unique<Var>("T"));
                tokenLookup.push_back(make_unique<Var>("token"));
                userCart.push_back(make_unique<FuncCall>("mapped_value", move(tokenLookup)));
            }
            cartNotEmpty.push_back(make_unique<FuncCall>("mapped_value", move(userCart)));
            cartNotEmpty.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>{}));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomT)));
        land.push_back(make_unique<FuncCall>("not_equals", move(cartNotEmpty)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("delivery_address"));
        callArgs.push_back(make_unique<Var>("payment_method"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: order_id ∈ dom(O) && O[order_id] contains order details */
        vector<unique_ptr<Expr>> inDomO;
        inDomO.push_back(make_unique<Var>("O"));
        inDomO.push_back(make_unique<Var>("order_id"));
        auto post = make_unique<FuncCall>("in_dom", move(inDomO));

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
    // Cart map (user -> items map)
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
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();