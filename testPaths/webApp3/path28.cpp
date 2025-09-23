// Path: Login → Get Menu → Add Item → Remove Item → Add Item Again → Place Order
// Valid path: User logs in, views menu, adds item, removes it, adds item again, and places order.

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

    // username = input();
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

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // getmenu(canteen_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("canteen_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getmenu", move(a))));
    }

    // add_item(item_id);  // First add
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_item", move(a))));
    }

    // remove_item(item_id);  // Remove the item
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("remove_item", move(a))));
    }

    // add_item(item_id);  // Add item again
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_item", move(a))));
    }

    // place_order(cart);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("cart"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("place_order", move(a))));
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

    // --- login_success ---
    {
        vector<unique_ptr<Expr>> conj;

        // Check if user exists and password matches
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Token should not already exist
        {
            vector<unique_ptr<Expr>> notIn;
            notIn.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("T"));
                notIn.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            conj.push_back(make_unique<FuncCall>("not_in", move(notIn)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        // Post-condition: token is mapped to user
        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T", "token"));
        eq2.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- getmenu ---
    {
        // Pre-condition: valid token required
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("canteen_id"));
        auto callFn = make_unique<FuncCall>("getmenu", move(args));

        // Post-condition: menu is visible
        vector<unique_ptr<Expr>> postArgs;
        auto post = make_unique<FuncCall>("menu_visible", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_item ---
    {
        // Pre-condition: valid token required
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_item", move(args));

        // Post-condition: item is in cart
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("item_id"));
        postArgs.push_back(make_unique<Var>("cart"));
        auto post = make_unique<FuncCall>("item_in_cart", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- remove_item ---
    {
        vector<unique_ptr<Expr>> conj;

        // Valid token required
        {
            vector<unique_ptr<Expr>> tokenArgs;
            tokenArgs.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("T"));
                tokenArgs.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(tokenArgs)));
        }

        // Item must be in cart to remove
        {
            vector<unique_ptr<Expr>> itemInCartArgs;
            itemInCartArgs.push_back(make_unique<Var>("item_id"));
            itemInCartArgs.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("item_in_cart", move(itemInCartArgs)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("remove_item", move(args));

        // Post-condition: item is not in cart
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("item_id"));
        postArgs.push_back(make_unique<Var>("cart"));
        auto post = make_unique<FuncCall>("item_not_in_cart", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- place_order ---
    {
        vector<unique_ptr<Expr>> conj;

        // Valid token required
        {
            vector<unique_ptr<Expr>> tokenArgs;
            tokenArgs.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("T"));
                tokenArgs.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(tokenArgs)));
        }

        // Cart must not be empty to place order
        {
            vector<unique_ptr<Expr>> cartArgs;
            cartArgs.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("not_empty", move(cartArgs)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("place_order", move(args));

        // Post-condition: order is placed and cart is cleared
        vector<unique_ptr<Expr>> postConj;
        
        {
            vector<unique_ptr<Expr>> orderArgs;
            orderArgs.push_back(make_unique<Var>("cart"));
            postConj.push_back(make_unique<FuncCall>("order_placed", move(orderArgs)));
        }
        
        {
            vector<unique_ptr<Expr>> emptyArgs;
            emptyArgs.push_back(make_unique<Var>("cart"));
            postConj.push_back(make_unique<FuncCall>("empty", move(emptyArgs)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- globals ---
    vector<unique_ptr<Decl>> globals;
    
    // User map: username -> password
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Token map: token -> username
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Current token
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    
    // Shopping cart
    globals.push_back(make_unique<Decl>("cart", make_unique<TypeConst>("string")));
    
    // Canteen ID
    globals.push_back(make_unique<Decl>("canteen_id", make_unique<TypeConst>("string")));
    
    // Item ID
    globals.push_back(make_unique<Decl>("item_id", make_unique<TypeConst>("string")));

    // Initialize global state
    vector<unique_ptr<Init>> inits;
    
    // Initialize empty user map
    inits.push_back(make_unique<Init>("U", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize empty token map
    inits.push_back(make_unique<Init>("T", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();