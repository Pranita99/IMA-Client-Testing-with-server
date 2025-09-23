#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for complete e-commerce journey:
//  signup(success) → login(success) → view_products → view_product_details → 
//  add_to_cart → place_order → view_orders
// ─────────────────────────────────────────────────────────────
static Program buildExtendedEcommerceClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("fullName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("sessionToken", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity", make_unique<TypeConst>("int")));
    decls.push_back(make_unique<Decl>("orderId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("shippingAddress", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("paymentMethod", make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: signup(success) - New user registration
    // ══════════════════════════════════════════════════════════
    // email = input(); // new email
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // fullName = input();
    {
        auto lhs = make_unique<Var>("fullName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // signup(email, password, fullName); // SUCCESS
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        a.push_back(make_unique<Var>("fullName"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: login(success) - User authentication
    // ══════════════════════════════════════════════════════════
    // email = input(); // correct email
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input(); // correct password
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // sessionToken = login(email, password); // SUCCESS - returns session token
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: view_products - Browse available products
    // ══════════════════════════════════════════════════════════
    // view_products(sessionToken); // Get list of all products
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_products", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: view_product_details - Get details of specific product
    // ══════════════════════════════════════════════════════════
    // productId = input(); // select product ID
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_product_details(sessionToken, productId); // Get detailed product info
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("productId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_product_details", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: add_to_cart - Add product to shopping cart
    // ══════════════════════════════════════════════════════════
    // quantity = input(); // select quantity
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(sessionToken, productId, quantity); // Add to cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 6: place_order - Create order from cart
    // ══════════════════════════════════════════════════════════
    // shippingAddress = input(); // enter shipping address
    {
        auto lhs = make_unique<Var>("shippingAddress");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // paymentMethod = input(); // select payment method
    {
        auto lhs = make_unique<Var>("paymentMethod");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // orderId = place_order(sessionToken, shippingAddress, paymentMethod); // Place order
    {
        auto lhs = make_unique<Var>("orderId");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("shippingAddress"));
        a.push_back(make_unique<Var>("paymentMethod"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("place_order", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 7: view_orders - View order history
    // ══════════════════════════════════════════════════════════
    // view_orders(sessionToken); // Get user's order history
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_orders", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Extended Ecommerce API *Spec* AST with all functionality
// ─────────────────────────────────────────────────────────────
static Spec buildExtendedEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Signup API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not_in(email, dom(CUSTOMERS)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("email"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        callArgs.push_back(make_unique<Var>("fullName"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: CUSTOMERS[email] = {password: password, name: fullName, status: "active"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMERS"));
            idx.push_back(make_unique<Var>("email"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> customerRecord;
        customerRecord.push_back(make_unique<Var>("password"));
        customerRecord.push_back(make_unique<Var>("fullName"));
        customerRecord.push_back(make_unique<Var>("active"));
        postArgs.push_back(make_unique<FuncCall>("customer_record", move(customerRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Login API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: email ∈ dom(CUSTOMERS) && CUSTOMERS[email].password = password */
        vector<unique_ptr<Expr>> emailExists;
        emailExists.push_back(make_unique<Var>("email"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            emailExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMERS"));
            idx.push_back(make_unique<Var>("email"));
            vector<unique_ptr<Expr>> field;
            field.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            field.push_back(make_unique<Var>("password"));
            passwordMatch.push_back(make_unique<FuncCall>("get_field", move(field)));
        }
        passwordMatch.push_back(make_unique<Var>("password"));
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        andArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: SESSIONS[sessionToken] = {email: email, loginTime: currentTime} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("SESSIONS"));
            idx.push_back(make_unique<Var>("sessionToken"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> sessionRecord;
        sessionRecord.push_back(make_unique<Var>("email"));
        sessionRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        postArgs.push_back(make_unique<FuncCall>("session_record", move(sessionRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Products API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_products", move(callArgs));

        /* post: return_products(PRODUCTS) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("PRODUCTS"));
        auto post = make_unique<FuncCall>("return_products", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Product Details API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∈ dom(PRODUCTS) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("view_product_details", move(callArgs));

        /* post: return_product_details(PRODUCTS[productId]) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("PRODUCTS"));
            idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        auto post = make_unique<FuncCall>("return_product_details", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Add to Cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∈ dom(PRODUCTS) && quantity > 0 */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> quantityValid;
        quantityValid.push_back(make_unique<Var>("quantity"));
        quantityValid.push_back(make_unique<Var>("0"));
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        andArgs.push_back(make_unique<FuncCall>("greater_than", move(quantityValid)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: CARTS[email][productId] = quantity */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> email_lookup;
            {
                vector<unique_ptr<Expr>> session_idx;
                session_idx.push_back(make_unique<Var>("SESSIONS"));
                session_idx.push_back(make_unique<Var>("sessionToken"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(session_idx)));
                field.push_back(make_unique<Var>("email"));
                email_lookup.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            
            vector<unique_ptr<Expr>> cart_idx;
            cart_idx.push_back(make_unique<Var>("CARTS"));
            cart_idx.push_back(move(email_lookup[0]));
            vector<unique_ptr<Expr>> product_idx;
            product_idx.push_back(make_unique<FuncCall>("mapped_value", move(cart_idx)));
            product_idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(product_idx)));
        }
        postArgs.push_back(make_unique<Var>("quantity"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Place Order API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && cart_not_empty(email) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> cartNotEmpty;
        {
            vector<unique_ptr<Expr>> email_lookup;
            {
                vector<unique_ptr<Expr>> session_idx;
                session_idx.push_back(make_unique<Var>("SESSIONS"));
                session_idx.push_back(make_unique<Var>("sessionToken"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(session_idx)));
                field.push_back(make_unique<Var>("email"));
                email_lookup.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            cartNotEmpty.push_back(move(email_lookup[0]));
        }
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("cart_not_empty", move(cartNotEmpty)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("shippingAddress"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: ORDERS[orderId] = {email: email, items: CARTS[email], address: shippingAddress, payment: paymentMethod, status: "placed"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ORDERS"));
            idx.push_back(make_unique<Var>("orderId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> orderRecord;
        {
            vector<unique_ptr<Expr>> email_lookup;
            {
                vector<unique_ptr<Expr>> session_idx;
                session_idx.push_back(make_unique<Var>("SESSIONS"));
                session_idx.push_back(make_unique<Var>("sessionToken"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(session_idx)));
                field.push_back(make_unique<Var>("email"));
                email_lookup.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            orderRecord.push_back(move(email_lookup[0]));
        }
        {
            vector<unique_ptr<Expr>> cart_lookup;
            cart_lookup.push_back(make_unique<Var>("CARTS"));
            cart_lookup.push_back(make_unique<Var>("email"));
            orderRecord.push_back(make_unique<FuncCall>("mapped_value", move(cart_lookup)));
        }
        orderRecord.push_back(make_unique<Var>("shippingAddress"));
        orderRecord.push_back(make_unique<Var>("paymentMethod"));
        orderRecord.push_back(make_unique<Var>("placed"));
        postArgs.push_back(make_unique<FuncCall>("order_record", move(orderRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Orders API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_orders", move(callArgs));

        /* post: return_user_orders(email, ORDERS) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> email_lookup;
            {
                vector<unique_ptr<Expr>> session_idx;
                session_idx.push_back(make_unique<Var>("SESSIONS"));
                session_idx.push_back(make_unique<Var>("sessionToken"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(session_idx)));
                field.push_back(make_unique<Var>("email"));
                email_lookup.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            postArgs.push_back(move(email_lookup[0]));
        }
        postArgs.push_back(make_unique<Var>("ORDERS"));
        auto post = make_unique<FuncCall>("return_user_orders", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  globals & initialisations
    // ═══════════════════════════════════════════════════════════
    vector<unique_ptr<Decl>> globals;
    // CUSTOMERS: Map<string, CustomerRecord>
    globals.push_back(make_unique<Decl>(
        "CUSTOMERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CustomerRecord"))));
    // SESSIONS: Map<string, SessionRecord>
    globals.push_back(make_unique<Decl>(
        "SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("SessionRecord"))));
    // PRODUCTS: Map<string, ProductRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));
    // CARTS: Map<string, Map<string, int>> (email -> (productId -> quantity))
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("int")))));
    // ORDERS: Map<string, OrderRecord>
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize PRODUCTS with sample data
    {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productEntries;
        
        // Product 1: Laptop
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Gaming_Laptop"));
            productRecord.push_back(make_unique<Var>("1299.99"));
            productRecord.push_back(make_unique<Var>("High_performance_gaming_laptop"));
            productRecord.push_back(make_unique<Var>("50"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD001"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        // Product 2: Smartphone
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Smartphone_Pro"));
            productRecord.push_back(make_unique<Var>("899.99"));
            productRecord.push_back(make_unique<Var>("Latest_flagship_smartphone"));
            productRecord.push_back(make_unique<Var>("100"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD002"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        // Product 3: Headphones
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Wireless_Headphones"));
            productRecord.push_back(make_unique<Var>("299.99"));
            productRecord.push_back(make_unique<Var>("Premium_noise_cancelling_headphones"));
            productRecord.push_back(make_unique<Var>("75"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD003"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        inits.push_back(make_unique<Init>(
            "PRODUCTS", make_unique<Map>(move(productEntries))));
    }
    
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

// ─────────────────────────────────────────────────────────────
//  Build failure cases for comprehensive testing
// ─────────────────────────────────────────────────────────────
static Spec buildExtendedEcommerceSpecWithFailures()
{
    vector<unique_ptr<API>> apiBlocks;

    // Include all success cases from buildExtendedEcommerceSpec()
    // ... (success cases would be duplicated here)

    // ═══════════════════════════════════════════════════════════
    //  View Products API block - FAILURE case (invalid session)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∉ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_products", move(callArgs));

        /* post: error("Unauthorized access") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Unauthorized_access"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Product Details API block - FAILURE case (product not found)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∉ dom(PRODUCTS) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productNotExists;
        productNotExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("not_in", move(productNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("view_product_details", move(callArgs));

        /* post: error("Product not found") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Product_not_found"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Add to Cart API block - FAILURE case (invalid quantity)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∈ dom(PRODUCTS) && quantity <= 0 */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> quantityInvalid;
        quantityInvalid.push_back(make_unique<Var>("quantity"));
        quantityInvalid.push_back(make_unique<Var>("0"));
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        andArgs.push_back(make_unique<FuncCall>("less_than_or_equal", move(quantityInvalid)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: error("Invalid quantity") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Invalid_quantity"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Place Order API block - FAILURE case (empty cart)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && cart_empty(email) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> cartEmpty;
        {
            vector<unique_ptr<Expr>> email_lookup;
            {
                vector<unique_ptr<Expr>> session_idx;
                session_idx.push_back(make_unique<Var>("SESSIONS"));
                session_idx.push_back(make_unique<Var>("sessionToken"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(session_idx)));
                field.push_back(make_unique<Var>("email"));
                email_lookup.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            cartEmpty.push_back(move(email_lookup[0]));
        }
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("cart_empty", move(cartEmpty)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("shippingAddress"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: error("Cart is empty") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cart_is_empty"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // Add the same globals and inits as the success case
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>(
        "CUSTOMERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CustomerRecord"))));
    globals.push_back(make_unique<Decl>(
        "SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("SessionRecord"))));
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("int")))));
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildExtendedEcommerceClientProgram();
Spec    spec          = buildExtendedEcommerceSpec();
Spec    specWithFailures = buildExtendedEcommerceSpecWithFailures();