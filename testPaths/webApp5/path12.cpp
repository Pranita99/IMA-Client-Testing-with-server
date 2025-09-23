#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for the flow:
//  login → add_to_cart → logout → place_order
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceLoginCartLogoutOrderClientProgram()
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
    //  STEP 2: add_to_cart(success) - Add product to cart while logged in
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
    //  STEP 3: logout(success) - End user session
    // ══════════════════════════════════════════════════════════
    // logout(customerId); // This will SUCCESS - valid logout
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: place_order(fail) - Attempt to place order after logout
    // ══════════════════════════════════════════════════════════
    // place_order(customerId); // This will FAIL - user is logged out
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for login→cart→logout→order flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceLoginCartLogoutOrderSpec()
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
    //  place_order API block - FAILURE case (user not logged in)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), not(empty(get_cart(CARTS, customerId))),
                    not_in(customerId, dom(ACTIVE_SESSIONS))) */
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
            pArgs.push_back(make_unique<FuncCall>("not_in", move(sessionCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: error("Cannot place order: user not authenticated") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_place_order_user_not_authenticated"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
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
        
        // Customer: "john@example.com" -> customer_record("password123", "John Doe", "active")
        {
            vector<unique_ptr<Expr>> customerArgs;
            customerArgs.push_back(make_unique<Var>("password123"));
            customerArgs.push_back(make_unique<Var>("John_Doe"));
            customerArgs.push_back(make_unique<Var>("active"));
            customerEntries.emplace_back(
                make_unique<Var>("john@example.com"),
                make_unique<FuncCall>("customer_record", move(customerArgs))
            );
        }
        
        inits.push_back(make_unique<Init>(
            "CUSTOMERS", make_unique<Map>(move(customerEntries))));
    }
    
    // Pre-populate PRODUCTS with available items
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> productEntries;
        
        // Product: "laptop" -> product_record("Gaming Laptop", 1299.99, 5)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Gaming_Laptop"));
            productArgs.push_back(make_unique<Var>("1299.99"));
            productArgs.push_back(make_unique<Var>("5"));
            productEntries.emplace_back(
                make_unique<Var>("laptop"),
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

/* ── globals the driver expects for the login→cart→logout→order flow ─────── */
Program clientProgram = buildEcommerceLoginCartLogoutOrderClientProgram();
Spec    spec          = buildEcommerceLoginCartLogoutOrderSpec();

/*
 * Expected execution flow (MIXED SUCCESS/FAILURE SCENARIO):
 * 
 * 1. login(email, password) → HTTP 200 OK (success)
 *    - Authenticates existing customer with correct credentials
 *    - Precondition: Customer exists, password matches, not already logged in
 *    - Postcondition: login_success(email) + session created in ACTIVE_SESSIONS
 *    - User is now authenticated and can perform cart operations
 * 
 * 2. add_to_cart(customerId, productId, quantity) → HTTP 200 OK (success)
 *    - Adds product to cart while user is logged in
 *    - Precondition: Customer exists, product exists, quantity > 0, user in active session
 *    - Postcondition: cart_updated(customerId, productId, quantity)
 *    - Cart now contains the selected product
 * 
 * 3. logout(customerId) → HTTP 200 OK (success)
 *    - Ends user session gracefully
 *    - Precondition: Customer exists and has active session
 *    - Postcondition: logout_success(customerId) + session removed from ACTIVE_SESSIONS
 *    - User is no longer authenticated, but cart persists
 * 
 * 4. place_order(customerId) → HTTP 401 UNAUTHORIZED (failure)
 *    - Attempts to place order after logout
 *    - Precondition: Customer exists, cart not empty, BUT user not in active session
 *    - Postcondition: error("Cannot place order: user not authenticated")
 *    - Order creation fails due to authentication requirement
 * 
 * This scenario demonstrates several important e-commerce security concepts:
 * 
 * **Session Management:**
 * - ACTIVE_SESSIONS map tracks authenticated users
 * - Login creates session, logout removes it
 * - Order operations require active authentication
 * 
 * **Cart Persistence vs. Authentication:**
 * - Cart contents persist after logout (common UX pattern)
 * - But order placement requires re-authentication
 * - This prevents unauthorized purchases while preserving shopping state
 * 
 * **Security by Design:**
 * - Sensitive operations (place_order) check authentication
 * - Non-sensitive operations (add_to_cart) succeed when logged in
 * - Clear error messages for authentication failures
 * 
 * **HTTP Status Codes:**
 * - 200 OK: Successful operations (login, add_to_cart, logout)
 * - 401 UNAUTHORIZED: Authentication required for sensitive operation
 * 
 * **Business Logic:**
 * - Users can shop while logged in
 * - Logout doesn't clear cart (good UX)
 * - But checkout requires re-authentication (security)
 * 
 * This flow models a realistic e-commerce scenario where users might:
 * - Add items to cart during a session
 * - Get logged out (timeout, manual logout, etc.)
 * - Need to re-authenticate before completing purchase
 * 
 * The formal specification precisely captures the authentication state
 * requirements and demonstrates how session management affects API behavior.
 */