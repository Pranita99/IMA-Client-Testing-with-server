#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for the flow:
//  login → view_cart(empty) → add_to_cart → logout → login → view_cart → place_order → view_orders
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceCartPersistenceClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("customerId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity", make_unique<TypeConst>("int")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: login(success) - Login with existing credentials
    // ══════════════════════════════════════════════════════════
    // email = input(); // existing customer email
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
    // login(email, password); // This will SUCCESS - existing customer
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: view_cart(empty) - View empty cart after login
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (from login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_cart(customerId); // This will SUCCESS - cart is empty initially
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: add_to_cart(success) - Add product to cart
    // ══════════════════════════════════════════════════════════
    // productId = input(); // existing product ID
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity = input(); // valid quantity
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(customerId, productId, quantity); // This will SUCCESS
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: logout(success) - End user session
    // ══════════════════════════════════════════════════════════
    // logout(customerId); // This will SUCCESS - valid logout
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: login(success) - Login again with same credentials
    // ══════════════════════════════════════════════════════════
    // login(email, password); // This will SUCCESS - same customer logging back in
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 6: view_cart(with items) - View cart with persisted items
    // ══════════════════════════════════════════════════════════
    // view_cart(customerId); // This will SUCCESS - cart contains previously added items
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 7: place_order(success) - Create order from cart contents
    // ══════════════════════════════════════════════════════════
    // place_order(customerId); // This will SUCCESS - user is logged in and cart has items
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 8: view_orders(success) - View customer's order history
    // ══════════════════════════════════════════════════════════
    // view_orders(customerId); // This will SUCCESS - customer has orders
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_orders", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for cart persistence flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceCartPersistenceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Login API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> emailCheck;
            emailCheck.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                emailCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(emailCheck)));
        }
        {
            vector<unique_ptr<Expr>> passwordCheck;
            {
                vector<unique_ptr<Expr>> storedPass;
                storedPass.push_back(make_unique<Var>("CUSTOMERS"));
                storedPass.push_back(make_unique<Var>("email"));
                storedPass.push_back(make_unique<Var>("password"));
                passwordCheck.push_back(make_unique<FuncCall>("get_password", move(storedPass)));
            }
            passwordCheck.push_back(make_unique<Var>("password"));
            pArgs.push_back(make_unique<FuncCall>("equals", move(passwordCheck)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("email"));
        auto post = make_unique<FuncCall>("login_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_cart API block - SUCCESS case (empty cart)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(customerId, dom(ACTIVE_SESSIONS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: cart_contents(customerId, cart_items) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        postArgs.push_back(make_unique<Var>("cart_items"));
        auto post = make_unique<FuncCall>("cart_contents", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  add_to_cart API block - SUCCESS case (user logged in)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(productId, dom(PRODUCTS)), 
                    gt(quantity, 0), in(customerId, dom(ACTIVE_SESSIONS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> productCheck;
            productCheck.push_back(make_unique<Var>("productId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("PRODUCTS"));
                productCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(productCheck)));
        }
        {
            vector<unique_ptr<Expr>> quantityCheck;
            quantityCheck.push_back(make_unique<Var>("quantity"));
            quantityCheck.push_back(make_unique<Var>("0"));
            pArgs.push_back(make_unique<FuncCall>("gt", move(quantityCheck)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: cart_updated(customerId, productId, quantity) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        postArgs.push_back(make_unique<Var>("productId"));
        postArgs.push_back(make_unique<Var>("quantity"));
        auto post = make_unique<FuncCall>("cart_updated", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  logout API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(customerId, dom(ACTIVE_SESSIONS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("logout", move(callArgs));

        /* post: logout_success(customerId) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        auto post = make_unique<FuncCall>("logout_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  place_order API block - SUCCESS case (when user is logged in)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), not(empty(get_cart(CARTS, customerId))),
                    in(customerId, dom(ACTIVE_SESSIONS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> cartCheck;
            {
                vector<unique_ptr<Expr>> cartArgs;
                cartArgs.push_back(make_unique<Var>("CARTS"));
                cartArgs.push_back(make_unique<Var>("customerId"));
                cartCheck.push_back(make_unique<FuncCall>("get_cart", move(cartArgs)));
            }
            auto emptyCheck = make_unique<FuncCall>("empty", move(cartCheck));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(emptyCheck));
            pArgs.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: order_created(customerId, orderId) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        postArgs.push_back(make_unique<Var>("orderId"));
        auto post = make_unique<FuncCall>("order_created", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_orders API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(customerId, dom(ACTIVE_SESSIONS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> sessionCheck;
            sessionCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ACTIVE_SESSIONS"));
                sessionCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_orders", move(callArgs));

        /* post: orders_retrieved(customerId, order_list) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        postArgs.push_back(make_unique<Var>("order_list"));
        auto post = make_unique<FuncCall>("orders_retrieved", move(postArgs));

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
    
    // PRODUCTS: Map<string, ProductRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));
    
    // CARTS: Map<string, Map<string, int>> (customerId -> (productId -> quantity))
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

    // ACTIVE_SESSIONS: Map<string, SessionRecord> - tracks logged in users
    globals.push_back(make_unique<Decl>(
        "ACTIVE_SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("SessionRecord"))));

    vector<unique_ptr<Init>> inits;
    
    // Pre-populate CUSTOMERS with existing user for login
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> customerEntries;
        
        // Customer: "user@example.com" -> customer_record("password123", "Customer Name", "active")
        {
            vector<unique_ptr<Expr>> customerArgs;
            customerArgs.push_back(make_unique<Var>("password123"));
            customerArgs.push_back(make_unique<Var>("Customer_Name"));
            customerArgs.push_back(make_unique<Var>("active"));
            customerEntries.emplace_back(
                make_unique<Var>("user@example.com"),
                make_unique<FuncCall>("customer_record", move(customerArgs))
            );
        }
        
        inits.push_back(make_unique<Init>(
            "CUSTOMERS", make_unique<Map>(move(customerEntries))));
    }
    
    // Pre-populate PRODUCTS with available items
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> productEntries;
        
        // Product: "product1" -> product_record("Product Name 1", 999.99, 20)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Product_Name_1"));
            productArgs.push_back(make_unique<Var>("999.99"));
            productArgs.push_back(make_unique<Var>("20"));
            productEntries.emplace_back(
                make_unique<Var>("product1"),
                make_unique<FuncCall>("product_record", move(productArgs))
            );
        }
        
        inits.push_back(make_unique<Init>(
            "PRODUCTS", make_unique<Map>(move(productEntries))));
    }
    
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    inits.push_back(make_unique<Init>(
        "ACTIVE_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the cart persistence flow ─────── */
Program clientProgram = buildEcommerceCartPersistenceClientProgram();
Spec    spec          = buildEcommerceCartPersistenceSpec();

/*
 * Expected execution flow (CART PERSISTENCE SCENARIO):
 * 
 * 1. login(email, password) → HTTP 200 OK (success)
 *    - Authenticates existing customer with correct credentials
 *    - Precondition: Customer exists, password matches, not already logged in
 *    - Postcondition: login_success(email) + session created in ACTIVE_SESSIONS
 *    - User is now authenticated and can perform operations
 * 
 * 2. view_cart(customerId) → HTTP 200 OK (success - empty cart)
 *    - Views cart contents for newly logged in user
 *    - Precondition: Customer exists and has active session
 *    - Postcondition: cart_contents(customerId, cart_items) - cart_items is empty
 *    - Confirms cart is initially empty for this customer
 * 
 * 3. add_to_cart(customerId, productId, quantity) → HTTP 200 OK (success)
 *    - Adds product to cart while user is logged in
 *    - Precondition: Customer exists, product exists, quantity > 0, user in active session
 *    - Postcondition: cart_updated(customerId, productId, quantity)
 *    - Cart now contains the selected product
 * 
 * 4. logout(customerId) → HTTP 200 OK (success)
 *    - Ends user session gracefully
 *    - Precondition: Customer exists and has active session
 *    - Postcondition: logout_success(customerId) + session removed from ACTIVE_SESSIONS
 *    - User is no longer authenticated, but cart persists in system
 * 
 * 5. login(email, password) → HTTP 200 OK (success)
 *    - Re-authenticates same customer after logout
 *    - Precondition: Customer exists, password matches, not currently logged in
 *    - Postcondition: login_success(email) + new session created in ACTIVE_SESSIONS
 *    - User is authenticated again and can access their persisted cart
 * 
 * 6. view_cart(customerId) → HTTP 200 OK (success - with items)
 *    - Views cart contents after re-login
 *    - Precondition: Customer exists and has active session
 *    - Postcondition: cart_contents(customerId, cart_items) - cart_items contains previous items
 *    - Demonstrates cart persistence across login sessions
 * 
 * 7. place_order(customerId) → HTTP 201 CREATED (success)
 *    - Creates order from persisted cart contents
 *    - Precondition: Customer exists, cart not empty, user in active session
 *    - Postcondition: order_created(customerId, orderId) + new entry in ORDERS
 *    - Order is successfully placed from cart that survived logout/login cycle
 * 
 * 8. view_orders(customerId) → HTTP 200 OK (success)
 *    - Retrieves customer's order history
 *    - Precondition: Customer exists and is logged in
 *    - Postcondition: orders_retrieved(customerId, order_list)
 *    - Customer can see their complete order history
 * 
 * This scenario demonstrates critical e-commerce cart persistence behavior:
 * 
 * **Cart Persistence:**
 * - Cart contents survive user logout/login cycles
 * - Items added to cart remain available after re-authentication
 * - Cart state is independent of session state
 * - Provides better user experience by preserving shopping intent
 * 
 * **Session vs. Cart State:**
 * - ACTIVE_SESSIONS tracks authentication state
 * - CARTS tracks shopping cart state
 * - Authentication required for cart operations
 * - But cart data persists beyond session lifetime
 * 
 * **User Experience Flow:**
 * - User logs in and sees empty cart initially
 * - User adds items to cart while shopping
 * - User logs out (intentionally or due to timeout)
 * - User logs back in and finds cart preserved
 * - User can complete purchase with saved cart
 * 
 * **Technical Implementation:**
 * - Cart data stored independently of session data
 * - Authentication required for all cart operations
 * - Cart viewing shows current state regardless of when items were added
 * - Order creation works with persisted cart contents
 * 
 * **Business Value:**
 * - Reduces cart abandonment due to logout
 * - Improves customer experience with persistent shopping state
 * - Allows customers to continue shopping across sessions
 * - Supports multi-device shopping scenarios
 * 
 * **Security Considerations:**
 * - All operations require valid authentication
 * - Cart access is customer-specific and protected
 * - Session expiry doesn't affect cart data integrity
 * - Re-authentication required for sensitive operations
 * 
 * This flow models realistic e-commerce behavior where customers expect
 * their shopping carts to persist across login sessions, providing a
 * seamless and user-friendly shopping experience while maintaining
 * proper security through authentication requirements.
 */