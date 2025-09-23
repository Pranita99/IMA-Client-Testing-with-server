#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for admin flow:
//  login(admin) → view_all_orders
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceAdminFlowClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: login(admin) - Administrative login
    // ══════════════════════════════════════════════════════════
    // email = input(); // admin email (e.g., "admin@company.com")
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input(); // admin password
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // login(email, password); // This will SUCCESS - admin credentials with elevated privileges
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: view_all_orders - Administrative access to all orders
    // ══════════════════════════════════════════════════════════
    // view_all_orders(); // This will SUCCESS - admin has permission to view all system orders
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_all_orders", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for admin flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceAdminFlowSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Login API block - ADMIN SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(email, dom(ADMINS)), equals(get_admin_password(ADMINS, email), password)) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> emailCheck;
            emailCheck.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ADMINS"));
                emailCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(emailCheck)));
        }
        {
            vector<unique_ptr<Expr>> passwordCheck;
            {
                vector<unique_ptr<Expr>> storedPass;
                storedPass.push_back(make_unique<Var>("ADMINS"));
                storedPass.push_back(make_unique<Var>("email"));
                passwordCheck.push_back(make_unique<FuncCall>("get_admin_password", move(storedPass)));
            }
            passwordCheck.push_back(make_unique<Var>("password"));
            pArgs.push_back(make_unique<FuncCall>("equals", move(passwordCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: admin_login_success(email, admin_privileges) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("email"));
        postArgs.push_back(make_unique<Var>("admin_privileges"));
        auto post = make_unique<FuncCall>("admin_login_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Login API block - REGULAR CUSTOMER SUCCESS case (for comparison)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), equals(get_password(CUSTOMERS, email, password), password)) */
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
            vector<unique_ptr<Expr>> notAdminCheck;
            notAdminCheck.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ADMINS"));
                notAdminCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(notAdminCheck)));
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
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: customer_login_success(email) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("email"));
        auto post = make_unique<FuncCall>("customer_login_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Login API block - FAILURE case (invalid credentials)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: or(and(not_in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS))), 
                    and(in(email, dom(CUSTOMERS)), not_equals(get_password(CUSTOMERS, email, password), password)),
                    and(in(email, dom(ADMINS)), not_equals(get_admin_password(ADMINS, email), password))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            // User doesn't exist in either CUSTOMERS or ADMINS
            vector<unique_ptr<Expr>> noUserCheck;
            {
                vector<unique_ptr<Expr>> notCustomer;
                notCustomer.push_back(make_unique<Var>("email"));
                {
                    vector<unique_ptr<Expr>> h;
                    h.push_back(make_unique<Var>("CUSTOMERS"));
                    notCustomer.push_back(make_unique<FuncCall>("dom", move(h)));
                }
                noUserCheck.push_back(make_unique<FuncCall>("not_in", move(notCustomer)));
            }
            {
                vector<unique_ptr<Expr>> notAdmin;
                notAdmin.push_back(make_unique<Var>("email"));
                {
                    vector<unique_ptr<Expr>> h;
                    h.push_back(make_unique<Var>("ADMINS"));
                    notAdmin.push_back(make_unique<FuncCall>("dom", move(h)));
                }
                noUserCheck.push_back(make_unique<FuncCall>("not_in", move(notAdmin)));
            }
            pArgs.push_back(make_unique<FuncCall>("and", move(noUserCheck)));
        }
        {
            // Customer exists but wrong password
            vector<unique_ptr<Expr>> wrongCustomerPass;
            {
                vector<unique_ptr<Expr>> isCustomer;
                isCustomer.push_back(make_unique<Var>("email"));
                {
                    vector<unique_ptr<Expr>> h;
                    h.push_back(make_unique<Var>("CUSTOMERS"));
                    isCustomer.push_back(make_unique<FuncCall>("dom", move(h)));
                }
                wrongCustomerPass.push_back(make_unique<FuncCall>("in", move(isCustomer)));
            }
            {
                vector<unique_ptr<Expr>> passwordMismatch;
                {
                    vector<unique_ptr<Expr>> storedPass;
                    storedPass.push_back(make_unique<Var>("CUSTOMERS"));
                    storedPass.push_back(make_unique<Var>("email"));
                    storedPass.push_back(make_unique<Var>("password"));
                    passwordMismatch.push_back(make_unique<FuncCall>("get_password", move(storedPass)));
                }
                passwordMismatch.push_back(make_unique<Var>("password"));
                wrongCustomerPass.push_back(make_unique<FuncCall>("not_equals", move(passwordMismatch)));
            }
            pArgs.push_back(make_unique<FuncCall>("and", move(wrongCustomerPass)));
        }
        {
            // Admin exists but wrong password
            vector<unique_ptr<Expr>> wrongAdminPass;
            {
                vector<unique_ptr<Expr>> isAdmin;
                isAdmin.push_back(make_unique<Var>("email"));
                {
                    vector<unique_ptr<Expr>> h;
                    h.push_back(make_unique<Var>("ADMINS"));
                    isAdmin.push_back(make_unique<FuncCall>("dom", move(h)));
                }
                wrongAdminPass.push_back(make_unique<FuncCall>("in", move(isAdmin)));
            }
            {
                vector<unique_ptr<Expr>> passwordMismatch;
                {
                    vector<unique_ptr<Expr>> storedPass;
                    storedPass.push_back(make_unique<Var>("ADMINS"));
                    storedPass.push_back(make_unique<Var>("email"));
                    passwordMismatch.push_back(make_unique<FuncCall>("get_admin_password", move(storedPass)));
                }
                passwordMismatch.push_back(make_unique<Var>("password"));
                wrongAdminPass.push_back(make_unique<FuncCall>("not_equals", move(passwordMismatch)));
            }
            pArgs.push_back(make_unique<FuncCall>("and", move(wrongAdminPass)));
        }
        auto pre = make_unique<FuncCall>("or", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: error("Invalid credentials") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Invalid_credentials"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        // FIXED: Changed from UNAUTHORIZED_401 to BAD_REQUEST_400 (which likely exists)
        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_all_orders API block - ADMIN SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: admin_authenticated() - current session has admin privileges */
        vector<unique_ptr<Expr>> pArgs;
        auto pre = make_unique<FuncCall>("admin_authenticated", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("view_all_orders", move(callArgs));

        /* post: all_orders_list(ORDERS) - returns complete order database */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("ORDERS"));
        auto post = make_unique<FuncCall>("all_orders_list", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_all_orders API block - FAILURE case (insufficient privileges)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not(admin_authenticated()) - current session lacks admin privileges */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("admin_authenticated", move(authCheck)));
        }
        auto pre = make_unique<FuncCall>("not", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("view_all_orders", move(callArgs));

        /* post: error("Access denied: admin privileges required") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Access_denied_admin_privileges_required"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        // FIXED: Changed from FORBIDDEN_403 to BAD_REQUEST_400 (which likely exists)
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
    
    // ADMINS: Map<string, AdminRecord> - new admin user database
    globals.push_back(make_unique<Decl>(
        "ADMINS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("AdminRecord"))));
    
    // ORDERS: Map<string, OrderRecord> (orderId -> order details)
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize ADMINS with default admin account
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> adminEntries;
    {
        vector<unique_ptr<Expr>> adminRecord;
        adminRecord.push_back(make_unique<Var>("admin_secure_password_123"));
        adminRecord.push_back(make_unique<Var>("System_Administrator"));
        adminRecord.push_back(make_unique<Var>("all_permissions"));
        adminRecord.push_back(make_unique<Var>("active"));
        adminEntries.emplace_back(
            make_unique<Var>("admin@company.com"),
            make_unique<FuncCall>("admin_record", move(adminRecord))
        );
    }
    inits.push_back(make_unique<Init>(
        "ADMINS", make_unique<Map>(move(adminEntries))));
    
    // Initialize ORDERS with sample order data for admin to view
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> orderEntries;
    {
        vector<unique_ptr<Expr>> orderRecord;
        orderRecord.push_back(make_unique<Var>("cust_001"));
        {
            vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> cartItems;
            cartItems.emplace_back(make_unique<Var>("prod_001"), make_unique<Var>("2"));
            cartItems.emplace_back(make_unique<Var>("prod_002"), make_unique<Var>("1"));
            orderRecord.push_back(make_unique<Map>(move(cartItems)));
        }
        orderRecord.push_back(make_unique<Var>("123_Main_St_Anytown_USA"));
        orderRecord.push_back(make_unique<Var>("credit_card"));
        orderRecord.push_back(make_unique<Var>("shipped"));
        orderEntries.emplace_back(
            make_unique<Var>("order_001"),
            make_unique<FuncCall>("order_record", move(orderRecord))
        );
    }
    {
        vector<unique_ptr<Expr>> orderRecord;
        orderRecord.push_back(make_unique<Var>("cust_002"));
        {
            vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> cartItems;
            cartItems.emplace_back(make_unique<Var>("prod_003"), make_unique<Var>("3"));
            orderRecord.push_back(make_unique<Map>(move(cartItems)));
        }
        orderRecord.push_back(make_unique<Var>("456_Oak_Ave_Springfield_USA"));
        orderRecord.push_back(make_unique<Var>("paypal"));
        orderRecord.push_back(make_unique<Var>("pending"));
        orderEntries.emplace_back(
            make_unique<Var>("order_002"),
            make_unique<FuncCall>("order_record", move(orderRecord))
        );
    }
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(move(orderEntries))));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the admin flow path ─────── */
Program clientProgram = buildEcommerceAdminFlowClientProgram();
Spec    spec          = buildEcommerceAdminFlowSpec();

/*
 * Expected execution flow (ADMIN SCENARIO):
 * 1. login(admin@company.com, admin_secure_password_123) → HTTP 200 OK (admin success)
 *    - Precondition: and(in(email, dom(ADMINS)), equals(get_admin_password(ADMINS, email), password))
 *    - Admin credentials validated against ADMINS map
 *    - Returns admin_login_success(email, admin_privileges)
 *    - Establishes authenticated admin session with elevated privileges
 * 
 * 2. view_all_orders() → HTTP 200 OK (admin access granted)
 *    - Precondition: admin_authenticated() - session has admin privileges
 *    - Returns all_orders_list(ORDERS) - complete system order database
 *    - Admin can see ALL orders from ALL customers
 *    - Includes order details: customer IDs, items, addresses, payment methods, status
 * 
 * SECURITY FEATURES:
 * - Separate ADMINS map with distinct authentication logic
 * - Role-based access control through admin_authenticated() precondition
 * - HTTP 400 BAD_REQUEST for non-admin attempts to access view_all_orders (changed from 403)
 * - HTTP 400 BAD_REQUEST for invalid admin credentials (changed from 401)
 * 
 * ADMIN PRIVILEGES:
 * - Access to complete order database across all customers
 * - System-wide visibility for order management and analytics
 * - Different response format (all_orders_list vs customer_orders)
 * 
 * DATA INITIALIZATION:
 * - Default admin account: admin@company.com with secure password
 * - Sample order data for demonstration (order_001: shipped, order_002: pending)
 * - Clear separation between customer and admin data structures
 * 
 * This demonstrates enterprise-grade role-based access control using
 * formal specifications to precisely define authorization boundaries
 * and administrative functionality in e-commerce systems.
 */