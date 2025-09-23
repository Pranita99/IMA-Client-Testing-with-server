#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: signup → login → get_menu → add_to_cart(empty) → logout → order
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup → login → get_menu → add_to_cart(empty) → logout → order flow
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

    // string login_username;
    decls.push_back(make_unique<Decl>("login_username",
                     make_unique<TypeConst>("string")));
    // login_username = input();
    {
        auto lhs = make_unique<Var>("login_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string login_password;
    decls.push_back(make_unique<Decl>("login_password",
                     make_unique<TypeConst>("string")));
    // login_password = input();
    {
        auto lhs = make_unique<Var>("login_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // login(login_username, login_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("login_username"));
        a.push_back(make_unique<Var>("login_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // get_menu();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_menu", move(a))));
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

    // string order_delivery_address;
    decls.push_back(make_unique<Decl>("order_delivery_address",
                     make_unique<TypeConst>("string")));
    // order_delivery_address = input();
    {
        auto lhs = make_unique<Var>("order_delivery_address");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string order_payment_method;
    decls.push_back(make_unique<Decl>("order_payment_method",
                     make_unique<TypeConst>("string")));
    // order_payment_method = input();
    {
        auto lhs = make_unique<Var>("order_payment_method");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // place_order(order_delivery_address, order_payment_method);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("order_delivery_address"));
        a.push_back(make_unique<Var>("order_payment_method"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST for signup → login → get_menu → add_to_cart(empty) → logout → order flow
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Signup API block ---
    {
        /* pre: username ∉ dom(U) */
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("username"));
        {
            vector<unique_ptr<Expr>> domU;
            domU.push_back(make_unique<Var>("U"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(domU)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("username"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: U[username] = password */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("username"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("password"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Login API block ---
    {
        /* pre: U[login_username] = login_password && user_token ∉ dom(T) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("login_username"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("login_password"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("user_token"));
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
        callArgs.push_back(make_unique<Var>("login_username"));
        callArgs.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: T[user_token] = login_username */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("T"));
            idx.push_back(make_unique<Var>("user_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("login_username"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Menu API block ---
    {
        /* pre: user_token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_menu", move(callArgs));

        /* post: menu_retrieved = M */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("menu_retrieved"));
        postArgs.push_back(make_unique<Var>("M"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add to Cart API block (empty cart constraint) ---
    {
        /* pre: user_token ∈ dom(T) && item_id ∈ dom(M) && C[T[user_token]] = ∅ */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("user_token"));
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

        // Empty cart condition: C[T[user_token]] = ∅
        vector<unique_ptr<Expr>> emptyCartArgs;
        {
            vector<unique_ptr<Expr>> userCartIdx;
            userCartIdx.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenIdx;
                tokenIdx.push_back(make_unique<Var>("T"));
                tokenIdx.push_back(make_unique<Var>("user_token"));
                userCartIdx.push_back(make_unique<FuncCall>("mapped_value", move(tokenIdx)));
            }
            emptyCartArgs.push_back(make_unique<FuncCall>("mapped_value", move(userCartIdx)));
        }
        emptyCartArgs.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>()));

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomM)));
        land.push_back(make_unique<FuncCall>("equals", move(emptyCartArgs)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_id"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[T[user_token]][item_id] = quantity */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> cartItemIdx;
            {
                vector<unique_ptr<Expr>> userCartIdx;
                userCartIdx.push_back(make_unique<Var>("C"));
                {
                    vector<unique_ptr<Expr>> tokenIdx;
                    tokenIdx.push_back(make_unique<Var>("T"));
                    tokenIdx.push_back(make_unique<Var>("user_token"));
                    userCartIdx.push_back(make_unique<FuncCall>("mapped_value", move(tokenIdx)));
                }
                cartItemIdx.push_back(make_unique<FuncCall>("mapped_value", move(userCartIdx)));
            }
            cartItemIdx.push_back(make_unique<Var>("item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(cartItemIdx)));
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
        /* pre: user_token ∈ dom(T) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domT)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("logout", move(callArgs));

        /* post: user_token ∉ dom(T) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("user_token"));
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

    // --- Place Order API block (problematic after logout) ---
    {
        /* pre: user_token ∈ dom(T) && C[T[user_token]] ≠ ∅ && order_id ∉ dom(O) */
        vector<unique_ptr<Expr>> inDomT;
        inDomT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> domT;
            domT.push_back(make_unique<Var>("T"));
            inDomT.push_back(make_unique<FuncCall>("dom", move(domT)));
        }

        // Non-empty cart condition: C[T[user_token]] ≠ ∅
        vector<unique_ptr<Expr>> nonEmptyCartArgs;
        {
            vector<unique_ptr<Expr>> userCartIdx;
            userCartIdx.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenIdx;
                tokenIdx.push_back(make_unique<Var>("T"));
                tokenIdx.push_back(make_unique<Var>("user_token"));
                userCartIdx.push_back(make_unique<FuncCall>("mapped_value", move(tokenIdx)));
            }
            nonEmptyCartArgs.push_back(make_unique<FuncCall>("mapped_value", move(userCartIdx)));
        }
        nonEmptyCartArgs.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>()));

        vector<unique_ptr<Expr>> notInDomO;
        notInDomO.push_back(make_unique<Var>("order_id"));
        {
            vector<unique_ptr<Expr>> domO;
            domO.push_back(make_unique<Var>("O"));
            notInDomO.push_back(make_unique<FuncCall>("dom", move(domO)));
        }

        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomT)));
        land.push_back(make_unique<FuncCall>("not_equals", move(nonEmptyCartArgs)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomO)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("order_delivery_address"));
        callArgs.push_back(make_unique<Var>("order_payment_method"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: O[order_id] = order_details && C[T[user_token]] = ∅ */
        vector<unique_ptr<Expr>> postOrderArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("O"));
            idx.push_back(make_unique<Var>("order_id"));
            postOrderArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> orderDetails;
            orderDetails.push_back(make_unique<Var>("T[user_token]"));
            orderDetails.push_back(make_unique<Var>("order_delivery_address"));
            orderDetails.push_back(make_unique<Var>("order_payment_method"));
            {
                vector<unique_ptr<Expr>> userCartIdx;
                userCartIdx.push_back(make_unique<Var>("C"));
                {
                    vector<unique_ptr<Expr>> tokenIdx;
                    tokenIdx.push_back(make_unique<Var>("T"));
                    tokenIdx.push_back(make_unique<Var>("user_token"));
                    userCartIdx.push_back(make_unique<FuncCall>("mapped_value", move(tokenIdx)));
                }
                orderDetails.push_back(make_unique<FuncCall>("mapped_value", move(userCartIdx)));
            }
            postOrderArgs.push_back(make_unique<FuncCall>("order_record", move(orderDetails)));
        }

        vector<unique_ptr<Expr>> postCartArgs;
        {
            vector<unique_ptr<Expr>> userCartIdx;
            userCartIdx.push_back(make_unique<Var>("C"));
            {
                vector<unique_ptr<Expr>> tokenIdx;
                tokenIdx.push_back(make_unique<Var>("T"));
                tokenIdx.push_back(make_unique<Var>("user_token"));
                userCartIdx.push_back(make_unique<FuncCall>("mapped_value", move(tokenIdx)));
            }
            postCartArgs.push_back(make_unique<FuncCall>("mapped_value", move(userCartIdx)));
        }
        postCartArgs.push_back(make_unique<FuncCall>("empty_map", vector<unique_ptr<Expr>>()));

        vector<unique_ptr<Expr>> postLand;
        postLand.push_back(make_unique<FuncCall>("equals", move(postOrderArgs)));
        postLand.push_back(make_unique<FuncCall>("equals", move(postCartArgs)));
        auto post = make_unique<FuncCall>("and_operator", move(postLand));

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
    // Admin credentials map
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin token map
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
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
    // Orders map
    globals.push_back(make_unique<Decl>(
        "O", make_unique<MapType>(
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
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
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

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
