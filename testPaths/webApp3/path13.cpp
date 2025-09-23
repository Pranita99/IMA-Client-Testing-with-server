// Flow 13:
// Guest Add to Cart → Login → Order (Common e-commerce pattern - should return SAT)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the client Program (imperative path)
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // canteen_id = input(); // Guest selects canteen
    {
        auto lhs = make_unique<Var>("canteen_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // getmenu(canteen_id); // Guest browses menu without login
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("canteen_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getmenu", move(a))));
    }

    // item_id = input(); // Guest selects item
    {
        auto lhs = make_unique<Var>("item_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // guest_add_to_cart(item_id); // Guest adds to cart without authentication
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("guest_add_to_cart", move(a))));
    }

    // username = input(); // Now user decides to login
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // login_success(username, password); // Login with existing account
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // order(cart); // Order the guest cart items after login
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("cart"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("order", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API specification
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

    // --- getmenu (Guest access - no authentication required) ---
    {
        vector<unique_ptr<Expr>> conj;

        // canteen_id must be valid
        {
            vector<unique_ptr<Expr>> valid;
            valid.push_back(make_unique<Var>("canteen_id"));
            conj.push_back(make_unique<FuncCall>("valid_canteen", move(valid)));
        }

        // canteen must be operational
        {
            vector<unique_ptr<Expr>> operational;
            operational.push_back(make_unique<Var>("canteen_id"));
            conj.push_back(make_unique<FuncCall>("canteen_operational", move(operational)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("canteen_id"));
        auto callFn = make_unique<FuncCall>("getmenu", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // menu becomes visible
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("canteen_id"));
            conj_post.push_back(make_unique<FuncCall>("menu_visible", move(postArgs)));
        }

        // current_canteen is set for cart constraint checking
        {
            vector<unique_ptr<Expr>> setCanteen;
            setCanteen.push_back(make_unique<Var>("current_canteen"));
            setCanteen.push_back(make_unique<Var>("canteen_id"));
            conj_post.push_back(make_unique<FuncCall>("equals", move(setCanteen)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- guest_add_to_cart (No authentication required) ---
    {
        vector<unique_ptr<Expr>> conj;

        // item must be valid
        {
            vector<unique_ptr<Expr>> valid;
            valid.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("valid_item", move(valid)));
        }

        // item must be available
        {
            vector<unique_ptr<Expr>> available;
            available.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("item_available", move(available)));
        }

        // item must belong to currently browsed canteen
        {
            vector<unique_ptr<Expr>> belongs;
            belongs.push_back(make_unique<Var>("item_id"));
            belongs.push_back(make_unique<Var>("current_canteen"));
            conj.push_back(make_unique<FuncCall>("item_belongs_to_canteen", move(belongs)));
        }

        // guest cart must not have items from different canteen (PESUFOODS constraint)
        {
            vector<unique_ptr<Expr>> constraint;
            constraint.push_back(make_unique<Var>("guest_cart"));
            constraint.push_back(make_unique<Var>("current_canteen"));
            conj.push_back(make_unique<FuncCall>("guest_cart_single_canteen", move(constraint)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("guest_add_to_cart", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // item added to guest cart
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("item_id"));
            conj_post.push_back(make_unique<FuncCall>("in_guest_cart", move(postArgs)));
        }

        // guest cart associated with current canteen
        {
            vector<unique_ptr<Expr>> assoc;
            assoc.push_back(make_unique<Var>("guest_cart"));
            assoc.push_back(make_unique<Var>("current_canteen"));
            conj_post.push_back(make_unique<FuncCall>("guest_cart_canteen_set", move(assoc)));
        }

        // guest session ID created/maintained
        {
            vector<unique_ptr<Expr>> session;
            session.push_back(make_unique<Var>("guest_session_id"));
            conj_post.push_back(make_unique<FuncCall>("guest_session_active", move(session)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_success (Existing user login) ---
    {
        vector<unique_ptr<Expr>> conj;

        // User must exist in U (pre-registered user)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("u"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("U"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // Password must match
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Token must not already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // Token created for user
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("T", "token"));
            eq.push_back(make_unique<Var>("u"));
            conj_post.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Guest cart transferred to user account
        {
            vector<unique_ptr<Expr>> transfer;
            transfer.push_back(make_unique<Var>("guest_cart"));
            transfer.push_back(make_unique<Var>("cart"));
            transfer.push_back(make_unique<Var>("u"));
            conj_post.push_back(make_unique<FuncCall>("guest_cart_transferred", move(transfer)));
        }

        // Guest session invalidated
        {
            vector<unique_ptr<Expr>> invalid;
            invalid.push_back(make_unique<Var>("guest_session_id"));
            conj_post.push_back(make_unique<FuncCall>("guest_session_invalidated", move(invalid)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order (Authenticated user ordering transferred cart) ---
    {
        vector<unique_ptr<Expr>> conj;

        // User must be authenticated
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> domArgs;
                domArgs.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(domArgs)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // Cart must not be empty (contains transferred guest items)
        {
            vector<unique_ptr<Expr>> ne;
            ne.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("not_empty", move(ne)));
        }

        // Cart must belong to authenticated user
        {
            vector<unique_ptr<Expr>> belongs;
            belongs.push_back(make_unique<Var>("cart"));
            belongs.push_back(mapVal("T", "token"));
            conj.push_back(make_unique<FuncCall>("cart_belongs_to_user", move(belongs)));
        }

        // All cart items must be from single canteen (PESUFOODS constraint)
        {
            vector<unique_ptr<Expr>> single;
            single.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("cart_single_canteen", move(single)));
        }

        // Cart items must still be available
        {
            vector<unique_ptr<Expr>> available;
            available.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("cart_items_available", move(available)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // Order placed successfully
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("ordered", move(postArgs)));
        }

        // Order ID generated
        {
            vector<unique_ptr<Expr>> orderGen;
            orderGen.push_back(make_unique<Var>("order_id"));
            orderGen.push_back(mapVal("T", "token"));
            conj_post.push_back(make_unique<FuncCall>("order_id_generated", move(orderGen)));
        }

        // Cart cleared after successful order
        {
            vector<unique_ptr<Expr>> clear;
            clear.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("cart_cleared", move(clear)));
        }

        // Payment processing initiated (if applicable)
        {
            vector<unique_ptr<Expr>> payment;
            payment.push_back(make_unique<Var>("order_id"));
            conj_post.push_back(make_unique<FuncCall>("payment_initiated", move(payment)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- globals ---
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("cart", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("guest_cart", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("guest_session_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("current_canteen", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("canteen_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("item_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("order_id", make_unique<TypeConst>("string")));

    // Initialize with pre-existing user for login
    vector<unique_ptr<Init>> inits;
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> userEntries;
        userEntries.push_back(make_pair(
            make_unique<Var>("existing_user"),
            make_unique<Var>("userpass123")
        ));
        inits.push_back(make_unique<Init>("U", make_unique<Map>(move(userEntries))));
    }
    inits.push_back(make_unique<Init>("T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();