#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: signup → login → get_restaurants → get_restaurant_menu → add_to_cart → place_order → add_review → get_reviews
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *user* Program AST for complete food ordering journey
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string user_username;
    decls.push_back(make_unique<Decl>("user_username",
                     make_unique<TypeConst>("string")));
    // user_username = input();
    {
        auto lhs = make_unique<Var>("user_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string user_password;
    decls.push_back(make_unique<Decl>("user_password",
                     make_unique<TypeConst>("string")));
    // user_password = input();
    {
        auto lhs = make_unique<Var>("user_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string user_email;
    decls.push_back(make_unique<Decl>("user_email",
                     make_unique<TypeConst>("string")));
    // user_email = input();
    {
        auto lhs = make_unique<Var>("user_email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // signup(user_username, user_password, user_email);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_username"));
        a.push_back(make_unique<Var>("user_password"));
        a.push_back(make_unique<Var>("user_email"));
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

    // string user_id;
    decls.push_back(make_unique<Decl>("user_id",
                     make_unique<TypeConst>("string")));
    // user_id = input();
    {
        auto lhs = make_unique<Var>("user_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
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

    // add_to_cart(user_id, item_id, quantity);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_id"));
        a.push_back(make_unique<Var>("item_id"));
        a.push_back(make_unique<Var>("quantity"));
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

    // place_order(user_id, delivery_address, payment_method);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("user_id"));
        a.push_back(make_unique<Var>("delivery_address"));
        a.push_back(make_unique<Var>("payment_method"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // string order_id;
    decls.push_back(make_unique<Decl>("order_id",
                     make_unique<TypeConst>("string")));
    // order_id = input();
    {
        auto lhs = make_unique<Var>("order_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string rating;
    decls.push_back(make_unique<Decl>("rating",
                     make_unique<TypeConst>("string")));
    // rating = input();
    {
        auto lhs = make_unique<Var>("rating");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string comment;
    decls.push_back(make_unique<Decl>("comment",
                     make_unique<TypeConst>("string")));
    // comment = input();
    {
        auto lhs = make_unique<Var>("comment");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_review(order_id, user_id, restaurant_id, rating, comment);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("order_id"));
        a.push_back(make_unique<Var>("user_id"));
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("rating"));
        a.push_back(make_unique<Var>("comment"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_review", move(a))));
    }

    // get_reviews(restaurant_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_reviews", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with complete user journey functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- User Signup API block ---
    {
        /* pre: user_username ∉ dom(U) */
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("user_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_username"));
        callArgs.push_back(make_unique<Var>("user_password"));
        callArgs.push_back(make_unique<Var>("user_email"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: U[user_username] = UserRecord(user_password, user_email) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("user_username"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            recordArgs.push_back(make_unique<Var>("user_password"));
            recordArgs.push_back(make_unique<Var>("user_email"));
            postArgs.push_back(make_unique<FuncCall>("user_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- User Login API block ---
    {
        /* pre: U[login_username].password = login_password && user_token ∉ dom(UT) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("U"));
            idx.push_back(make_unique<Var>("login_username"));
            auto userRecord = make_unique<FuncCall>("mapped_value", move(idx));
            
            vector<unique_ptr<Expr>> passwordAccess;
            passwordAccess.push_back(move(userRecord));
            passwordAccess.push_back(make_unique<Var>("password"));
            eq.push_back(make_unique<FuncCall>("field_access", move(passwordAccess)));
        }
        eq.push_back(make_unique<Var>("login_password"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("user_token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("UT"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("login_username"));
        callArgs.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: UT[user_token] = login_username */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("UT"));
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

    // --- Get Restaurants API block ---
    {
        /* pre: true (no precondition - anyone can view restaurants) */
        auto pre = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>());

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_restaurants", move(callArgs));

        /* post: restaurant_list = values(R) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("restaurant_list"));
        {
            vector<unique_ptr<Expr>> valuesArgs;
            valuesArgs.push_back(make_unique<Var>("R"));
            postArgs.push_back(make_unique<FuncCall>("values", move(valuesArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Restaurant Menu API block ---
    {
        /* pre: restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            inDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomR));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        auto callFn = make_unique<FuncCall>("get_restaurant_menu", move(callArgs));

        /* post: menu_items = if restaurant_id ∈ dom(M) then M[restaurant_id] else [] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("menu_items"));
        
        // Build conditional expression: if restaurant_id ∈ dom(M) then M[restaurant_id] else []
        {
            // Condition: restaurant_id ∈ dom(M)
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("restaurant_id"));
            {
                vector<unique_ptr<Expr>> domM;
                domM.push_back(make_unique<Var>("M"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domM)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: M[restaurant_id]
            vector<unique_ptr<Expr>> thenArgs;
            thenArgs.push_back(make_unique<Var>("M"));
            thenArgs.push_back(make_unique<Var>("restaurant_id"));
            auto thenBranch = make_unique<FuncCall>("mapped_value", move(thenArgs));
            
            // Else branch: empty list []
            auto elseBranch = make_unique<FuncCall>("empty_list", vector<unique_ptr<Expr>>());
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add to Cart API block ---
    {
        /* pre: user_token ∈ dom(UT) && user_id ∈ dom(U) && item_id ∈ dom(I) */
        vector<unique_ptr<Expr>> inDomUT;
        inDomUT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("UT"));
            inDomUT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomU;
        inDomU.push_back(make_unique<Var>("user_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            inDomU.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomI;
        inDomI.push_back(make_unique<Var>("item_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("I"));
            inDomI.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomUT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomU)));
        land.push_back(make_unique<FuncCall>("in", move(inDomI)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_id"));
        callArgs.push_back(make_unique<Var>("item_id"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: C[user_id] = if user_id ∈ dom(C) then C[user_id] ∪ {CartItem(item_id, quantity)} else {CartItem(item_id, quantity)} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("C"));
            idx.push_back(make_unique<Var>("user_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            // Build conditional expression
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("user_id"));
            {
                vector<unique_ptr<Expr>> domC;
                domC.push_back(make_unique<Var>("C"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domC)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: C[user_id] ∪ {CartItem(item_id, quantity)}
            vector<unique_ptr<Expr>> unionArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("C"));
                idx.push_back(make_unique<Var>("user_id"));
                unionArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            {
                vector<unique_ptr<Expr>> itemArgs;
                itemArgs.push_back(make_unique<Var>("item_id"));
                itemArgs.push_back(make_unique<Var>("quantity"));
                auto cartItem = make_unique<FuncCall>("cart_item", move(itemArgs));
                
                vector<unique_ptr<Expr>> setArgs;
                setArgs.push_back(move(cartItem));
                unionArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
            }
            auto thenBranch = make_unique<FuncCall>("union", move(unionArgs));
            
            // Else branch: {CartItem(item_id, quantity)}
            vector<unique_ptr<Expr>> itemArgs2;
            itemArgs2.push_back(make_unique<Var>("item_id"));
            itemArgs2.push_back(make_unique<Var>("quantity"));
            auto cartItem2 = make_unique<FuncCall>("cart_item", move(itemArgs2));
            
            vector<unique_ptr<Expr>> setArgs2;
            setArgs2.push_back(move(cartItem2));
            auto elseBranch = make_unique<FuncCall>("singleton_set", move(setArgs2));
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Place Order API block ---
    {
        /* pre: user_token ∈ dom(UT) && user_id ∈ dom(U) && user_id ∈ dom(C) */
        vector<unique_ptr<Expr>> inDomUT;
        inDomUT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("UT"));
            inDomUT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomU;
        inDomU.push_back(make_unique<Var>("user_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            inDomU.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomC;
        inDomC.push_back(make_unique<Var>("user_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("C"));
            inDomC.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomUT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomU)));
        land.push_back(make_unique<FuncCall>("in", move(inDomC)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("user_id"));
        callArgs.push_back(make_unique<Var>("delivery_address"));
        callArgs.push_back(make_unique<Var>("payment_method"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: O[order_id] = OrderRecord(user_id, C[user_id], delivery_address, payment_method, "pending") && C[user_id] = [] */
        vector<unique_ptr<Expr>> land2;
        {
            vector<unique_ptr<Expr>> eq1;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("O"));
                idx.push_back(make_unique<Var>("order_id"));
                eq1.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            {
                vector<unique_ptr<Expr>> recordArgs;
                recordArgs.push_back(make_unique<Var>("user_id"));
                {
                    vector<unique_ptr<Expr>> idx;
                    idx.push_back(make_unique<Var>("C"));
                    idx.push_back(make_unique<Var>("user_id"));
                    recordArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
                }
                recordArgs.push_back(make_unique<Var>("delivery_address"));
                recordArgs.push_back(make_unique<Var>("payment_method"));
                recordArgs.push_back(make_unique<Var>("pending"));
                eq1.push_back(make_unique<FuncCall>("order_record", move(recordArgs)));
            }
            land2.push_back(make_unique<FuncCall>("equals", move(eq1)));
        }
        {
            vector<unique_ptr<Expr>> eq2;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("C"));
                idx.push_back(make_unique<Var>("user_id"));
                eq2.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            eq2.push_back(make_unique<FuncCall>("empty_list", vector<unique_ptr<Expr>>()));
            land2.push_back(make_unique<FuncCall>("equals", move(eq2)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(land2));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add Review API block ---
    {
        /* pre: user_token ∈ dom(UT) && order_id ∈ dom(O) && user_id ∈ dom(U) && restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomUT;
        inDomUT.push_back(make_unique<Var>("user_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("UT"));
            inDomUT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomO;
        inDomO.push_back(make_unique<Var>("order_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("O"));
            inDomO.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomU;
        inDomU.push_back(make_unique<Var>("user_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("U"));
            inDomU.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            inDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomUT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomO)));
        land.push_back(make_unique<FuncCall>("in", move(inDomU)));
        land.push_back(make_unique<FuncCall>("in", move(inDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("order_id"));
        callArgs.push_back(make_unique<Var>("user_id"));
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        callArgs.push_back(make_unique<Var>("rating"));
        callArgs.push_back(make_unique<Var>("comment"));
        auto callFn = make_unique<FuncCall>("add_review", move(callArgs));

        /* post: RV[restaurant_id] = if restaurant_id ∈ dom(RV) then RV[restaurant_id] ∪ {Review(user_id, rating, comment)} else {Review(user_id, rating, comment)} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("RV"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            // Build conditional expression
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("restaurant_id"));
            {
                vector<unique_ptr<Expr>> domRV;
                domRV.push_back(make_unique<Var>("RV"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domRV)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: RV[restaurant_id] ∪ {Review(user_id, rating, comment)}
            vector<unique_ptr<Expr>> unionArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("RV"));
                idx.push_back(make_unique<Var>("restaurant_id"));
                unionArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            {
                vector<unique_ptr<Expr>> reviewArgs;
                reviewArgs.push_back(make_unique<Var>("user_id"));
                reviewArgs.push_back(make_unique<Var>("rating"));
                reviewArgs.push_back(make_unique<Var>("comment"));
                auto review = make_unique<FuncCall>("review", move(reviewArgs));
                
                vector<unique_ptr<Expr>> setArgs;
                setArgs.push_back(move(review));
                unionArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
            }
            auto thenBranch = make_unique<FuncCall>("union", move(unionArgs));
            
            // Else branch: {Review(user_id, rating, comment)}
            vector<unique_ptr<Expr>> reviewArgs2;
            reviewArgs2.push_back(make_unique<Var>("user_id"));
            reviewArgs2.push_back(make_unique<Var>("rating"));
            reviewArgs2.push_back(make_unique<Var>("comment"));
            auto review2 = make_unique<FuncCall>("review", move(reviewArgs2));
            
            vector<unique_ptr<Expr>> setArgs2;
            setArgs2.push_back(move(review2));
            auto elseBranch = make_unique<FuncCall>("singleton_set", move(setArgs2));
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Reviews API block ---
    {
        /* pre: restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            inDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomR));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        auto callFn = make_unique<FuncCall>("get_reviews", move(callArgs));

        /* post: reviews = if restaurant_id ∈ dom(RV) then RV[restaurant_id] else [] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("reviews"));
        
        // Build conditional expression: if restaurant_id ∈ dom(RV) then RV[restaurant_id] else []
        {
            // Condition: restaurant_id ∈ dom(RV)
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("restaurant_id"));
            {
                vector<unique_ptr<Expr>> domRV;
                domRV.push_back(make_unique<Var>("RV"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domRV)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: RV[restaurant_id]
            vector<unique_ptr<Expr>> thenArgs;
            thenArgs.push_back(make_unique<Var>("RV"));
            thenArgs.push_back(make_unique<Var>("restaurant_id"));
            auto thenBranch = make_unique<FuncCall>("mapped_value", move(thenArgs));
            
            // Else branch: empty list []
            auto elseBranch = make_unique<FuncCall>("empty_list", vector<unique_ptr<Expr>>());
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials and data map
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("UserRecord"))));
    // User token to username map
    globals.push_back(make_unique<Decl>(
        "UT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map (restaurant_name -> restaurant_record)
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("RestaurantRecord"))));
    // Menu data map (restaurant_id -> menu_items_set)
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("MenuItemSet"))));
    // Cart data map (user_id -> cart_items)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CartItemSet"))));
    // Item data map (item_id -> item_record)
    globals.push_back(make_unique<Decl>(
        "I", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ItemRecord"))));
    // Order data map (order_id -> order_record)
    globals.push_back(make_unique<Decl>(
        "O", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));
    // Review data map (restaurant_id -> reviews_set)
    globals.push_back(make_unique<Decl>(
        "RV", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ReviewSet"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "UT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "M", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "I", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "O", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "RV", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();