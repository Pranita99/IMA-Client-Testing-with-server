#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for the flow:
//  login → add_to_cart → place_order → delete_cart → view_cart(empty)
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceOrderCartCleanupClientProgram()
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
    //  STEP 2: add_to_cart(success) - Add product to cart
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (from login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId = input(); // existing product
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
    //  STEP 3: place_order(success) - Create order from cart
    // ══════════════════════════════════════════════════════════
    // place_order(customerId); // This will SUCCESS and create order
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: delete_cart(success) - Clear cart after order
    // ══════════════════════════════════════════════════════════
    // delete_cart(customerId); // This will SUCCESS and clear cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("delete_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: view_cart(empty) - View now-empty cart
    // ══════════════════════════════════════════════════════════
    // view_cart(customerId); // This will SUCCESS but show empty cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for order→cleanup→view flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceOrderCartCleanupSpec()
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
    //  add_to_cart API block - SUCCESS case
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
    //  place_order API block - SUCCESS case
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
    //  delete_cart API block - SUCCESS case
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
        auto callFn = make_unique<FuncCall>("delete_cart", move(callArgs));

        /* post: cart_deleted(customerId) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        auto post = make_unique<FuncCall>("cart_deleted", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_cart API block - SUCCESS case (empty cart after deletion)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), empty(get_cart(CARTS, customerId))) */
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
            pArgs.push_back(make_unique<FuncCall>("empty", move(cartCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: cart_contents({}) - empty cart contents */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()));
        auto post = make_unique<FuncCall>("cart_contents", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Alternative view_cart API block - SUCCESS case (populated cart)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), not(empty(get_cart(CARTS, customerId)))) */
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
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: cart_contents(get_cart(CARTS, customerId)) - populated cart */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> cartArgs;
            cartArgs.push_back(make_unique<Var>("CARTS"));
            cartArgs.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("get_cart", move(cartArgs)));
        }
        auto post = make_unique<FuncCall>("cart_contents", move(postArgs));

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
        
        // Customer: "sarah@example.com" -> customer_record("password456", "Sarah Smith", "active")
        {
            vector<unique_ptr<Expr>> customerArgs;
            customerArgs.push_back(make_unique<Var>("password456"));
            customerArgs.push_back(make_unique<Var>("Sarah_Smith"));
            customerArgs.push_back(make_unique<Var>("active"));
            customerEntries.emplace_back(
                make_unique<Var>("sarah@example.com"),
                make_unique<FuncCall>("customer_record", move(customerArgs))
            );
        }
        
        inits.push_back(make_unique<Init>(
            "CUSTOMERS", make_unique<Map>(move(customerEntries))));
    }
    
    // Pre-populate PRODUCTS with available items
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> productEntries;
        
        // Product: "smartphone" -> product_record("iPhone 15", 899.99, 15)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("iPhone_15"));
            productArgs.push_back(make_unique<Var>("899.99"));
            productArgs.push_back(make_unique<Var>("15"));
            productEntries.emplace_back(
                make_unique<Var>("smartphone"),
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

/* ── globals the driver expects for the order→cleanup→view flow ─────── */
Program clientProgram = buildEcommerceOrderCartCleanupClientProgram();
Spec    spec          = buildEcommerceOrderCartCleanupSpec();

/*
 * Expected execution flow (COMPLETE ORDER AND CLEANUP SCENARIO):
 * 
 * 1. login(email, password) → HTTP 200 OK (success)
 *    - Authenticates existing customer with correct credentials
 *    - Precondition: Customer exists, password matches, not already logged in
 *    - Postcondition: login_success(email) + session created in ACTIVE_SESSIONS
 *    - User is now authenticated and ready to shop
 * 
 * 2. add_to_cart(customerId, productId, quantity) → HTTP 200 OK (success)
 *    - Adds product to cart while user is logged in
 *    - Precondition: Customer exists, product exists, quantity > 0, user has active session
 *    - Postcondition: cart_updated(customerId, productId, quantity)
 *    - Cart now contains the selected product (smartphone)
 * 
 * 3. place_order(customerId) → HTTP 201 CREATED (success)
 *    - Converts cart contents into a formal order
 *    - Precondition: Customer exists, cart not empty, user has active session
 *    - Postcondition: order_created(customerId, orderId)
 *    - Creates new order record in ORDERS map
 *    - Order contains all cart items with quantities and prices
 * 
 * 4. delete_cart(customerId) → HTTP 200 OK (success)
 *    - Clears customer's cart after successful order placement
 *    - Precondition: Customer exists and has active session
 *    - Postcondition: cart_deleted(customerId)
 *    - Removes all items from customer's cart in CARTS map
 *    - Common cleanup operation after order completion
 * 
 * 5. view_cart(customerId) → HTTP 200 OK (success, empty)
 *    - Views cart contents after deletion
 *    - Precondition: Customer exists and cart is empty
 *    - Postcondition: cart_contents({}) - returns empty cart
 *    - Confirms cart has been successfully cleared
 * 
 * This scenario demonstrates a complete e-commerce order workflow with cleanup:
 * 
 * **Order Lifecycle Management:**
 * - Cart → Order conversion preserves all product information
 * - Order creation triggers cart cleanup for fresh shopping experience
 * - Post-order cart state is properly managed
 * 
 * **State Transitions:**
 * - Cart: Empty → Populated → Ordered → Deleted → Empty
 * - Orders: None → New Order Created
 * - Session: Maintained throughout entire flow
 * 
 * **Business Logic Benefits:**
 * - Clean separation between cart (temporary) and orders (permanent)
 * - Cart cleanup prevents confusion about ordered vs. pending items
 * - Fresh cart state encourages additional purchases
 * 
 * **API Design Patterns:**
 * - Dual view_cart specifications handle both empty and populated states
 * - delete_cart requires authentication for security
 * - Proper HTTP status codes: 201 for order creation, 200 for operations
 * 
 * **User Experience:**
 * - Seamless flow from shopping to ordering
 * - Clear cart state after purchase completion
 * - Ready for next shopping session
 * 
 * This represents the "golden path" of e-commerce: a user logs in, shops,
 * successfully places
 */