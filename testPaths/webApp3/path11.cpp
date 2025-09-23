// Flow 11:
// Signup → Login → Add ItemA → Add ItemA → Order (Testing duplicate item addition - should return SAT)

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

    // signup_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(a))));
    }

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // itemA = "pizza"; // Set specific item
    {
        auto lhs = make_unique<Var>("itemA");
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<Var>("pizza")));
    }

    // add_to_cart(itemA); // First addition of ItemA
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("itemA"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // add_to_cart(itemA); // Second addition of same ItemA
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("itemA"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // order(cart);
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

    // --- signup_success ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_success", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U", "u"));
        eq.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_success ---
    {
        vector<unique_ptr<Expr>> conj;

        // U[u] == p
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // token ∉ dom(T)
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

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("T", "token"));
        eq.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart (First instance) ---
    {
        vector<unique_ptr<Expr>> conj;

        // token ∈ dom(T) - user must be authenticated
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

        // item_id must be valid (assuming all items are valid for simplicity)
        {
            vector<unique_ptr<Expr>> valid;
            valid.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("valid_item", move(valid)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // item is added to cart
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("item_id"));
            conj_post.push_back(make_unique<FuncCall>("in_cart", move(postArgs)));
        }

        // cart quantity is updated (C[item_id] = C[item_id] + 1)
        {
            vector<unique_ptr<Expr>> qty;
            qty.push_back(make_unique<Var>("item_id"));
            qty.push_back(make_unique<Var>("1"));
            conj_post.push_back(make_unique<FuncCall>("quantity_incremented", move(qty)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart (Second instance - same item) ---
    {
        vector<unique_ptr<Expr>> conj;

        // token ∈ dom(T) - user must be authenticated
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

        // item_id must be valid
        {
            vector<unique_ptr<Expr>> valid;
            valid.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("valid_item", move(valid)));
        }

        // item is already in cart (from first addition)
        {
            vector<unique_ptr<Expr>> already;
            already.push_back(make_unique<Var>("item_id"));
            conj.push_back(make_unique<FuncCall>("in_cart", move(already)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // item remains in cart
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("item_id"));
            conj_post.push_back(make_unique<FuncCall>("in_cart", move(postArgs)));
        }

        // cart quantity is incremented again (C[item_id] = C[item_id] + 1)
        {
            vector<unique_ptr<Expr>> qty;
            qty.push_back(make_unique<Var>("item_id"));
            qty.push_back(make_unique<Var>("2"));
            conj_post.push_back(make_unique<FuncCall>("quantity_equals", move(qty)));
        }

        // cart size increased
        {
            vector<unique_ptr<Expr>> size;
            size.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("cart_size_increased", move(size)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(conj_post));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order ---
    {
        vector<unique_ptr<Expr>> conj;

        // cart must not be empty
        {
            vector<unique_ptr<Expr>> ne;
            ne.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("not_empty", move(ne)));
        }

        // user must be authenticated
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

        // cart must have valid total quantity
        {
            vector<unique_ptr<Expr>> total;
            total.push_back(make_unique<Var>("cart"));
            conj.push_back(make_unique<FuncCall>("valid_cart_total", move(total)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        vector<unique_ptr<Expr>> conj_post;
        
        // order is placed successfully with correct quantities
        {
            vector<unique_ptr<Expr>> postArgs;
            postArgs.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("ordered", move(postArgs)));
        }

        // order reflects duplicate item (quantity = 2 for itemA)
        {
            vector<unique_ptr<Expr>> dup;
            dup.push_back(make_unique<Var>("itemA"));
            dup.push_back(make_unique<Var>("2"));
            conj_post.push_back(make_unique<FuncCall>("order_quantity_correct", move(dup)));
        }

        // cart is cleared after successful order
        {
            vector<unique_ptr<Expr>> clear;
            clear.push_back(make_unique<Var>("cart"));
            conj_post.push_back(make_unique<FuncCall>("cart_cleared", move(clear)));
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
    globals.push_back(make_unique<Decl>("C", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("int"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("cart", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("itemA", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();