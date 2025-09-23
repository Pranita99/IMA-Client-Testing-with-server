#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for customer flow:
//  signup(success) → login(success) → delete_cart(empty)
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceCustomerFlowClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("firstName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("lastName", make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: signup(success) - New customer registration
    // ══════════════════════════════════════════════════════════
    // email = input(); // new customer email (e.g., "customer@example.com")
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input(); // new customer password
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // firstName = input(); // customer first name
    {
        auto lhs = make_unique<Var>("firstName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // lastName = input(); // customer last name
    {
        auto lhs = make_unique<Var>("lastName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // signup(email, password, firstName, lastName); // This will SUCCESS - new customer registration
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        a.push_back(make_unique<Var>("firstName"));
        a.push_back(make_unique<Var>("lastName"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: login(success) - Customer login with new account
    // ══════════════════════════════════════════════════════════
    // login(email, password); // This will SUCCESS - newly registered customer credentials
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: delete_cart(empty) - Delete empty cart
    // ══════════════════════════════════════════════════════════
    // delete_cart(); // This will SUCCESS - cart is empty (new customer has no items)
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("delete_cart", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for customer flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceCustomerFlowSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Signup API block - SUCCESS case (new customer)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(not_in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), valid_email(email), valid_password(password)) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> notCustomer;
            notCustomer.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                notCustomer.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(notCustomer)));
        }
        {
            vector<unique_ptr<Expr>> notAdmin;
            notAdmin.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ADMINS"));
                notAdmin.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(notAdmin)));
        }
        {
            vector<unique_ptr<Expr>> emailValid;
            emailValid.push_back(make_unique<Var>("email"));
            pArgs.push_back(make_unique<FuncCall>("valid_email", move(emailValid)));
        }
        {
            vector<unique_ptr<Expr>> passwordValid;
            passwordValid.push_back(make_unique<Var>("password"));
            pArgs.push_back(make_unique<FuncCall>("valid_password", move(passwordValid)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        callArgs.push_back(make_unique<Var>("firstName"));
        callArgs.push_back(make_unique<Var>("lastName"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: customer_signup_success(email, new_customer_id) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("email"));
        postArgs.push_back(make_unique<Var>("new_customer_id"));
        auto post = make_unique<FuncCall>("customer_signup_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Signup API block - FAILURE case (email already exists)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: or(in(email, dom(CUSTOMERS)), in(email, dom(ADMINS))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> isCustomer;
            isCustomer.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                isCustomer.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(isCustomer)));
        }
        {
            vector<unique_ptr<Expr>> isAdmin;
            isAdmin.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("ADMINS"));
                isAdmin.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(isAdmin)));
        }
        auto pre = make_unique<FuncCall>("or", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        callArgs.push_back(make_unique<Var>("firstName"));
        callArgs.push_back(make_unique<Var>("lastName"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: error("Email already exists") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Email_already_exists"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Login API block - CUSTOMER SUCCESS case
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
                    and(in(email, dom(CUSTOMERS)), not_equals(get_password(CUSTOMERS, email, password), password))) */
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

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  delete_cart API block - SUCCESS case (empty cart)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(customer_authenticated(), empty_cart(current_user())) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        {
            vector<unique_ptr<Expr>> emptyCheck;
            {
                vector<unique_ptr<Expr>> userCheck;
                emptyCheck.push_back(make_unique<FuncCall>("current_user", move(userCheck)));
            }
            pArgs.push_back(make_unique<FuncCall>("empty_cart", move(emptyCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("delete_cart", move(callArgs));

        /* post: cart_deleted_success(current_user()) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userArg;
            postArgs.push_back(make_unique<FuncCall>("current_user", move(userArg)));
        }
        auto post = make_unique<FuncCall>("cart_deleted_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  delete_cart API block - FAILURE case (not authenticated)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not(customer_authenticated()) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        auto pre = make_unique<FuncCall>("not", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("delete_cart", move(callArgs));

        /* post: error("Authentication required") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Authentication_required"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  delete_cart API block - FAILURE case (cart not empty)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(customer_authenticated(), not(empty_cart(current_user()))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        {
            vector<unique_ptr<Expr>> notEmptyCheck;
            {
                vector<unique_ptr<Expr>> emptyCheck;
                {
                    vector<unique_ptr<Expr>> userCheck;
                    emptyCheck.push_back(make_unique<FuncCall>("current_user", move(userCheck)));
                }
                notEmptyCheck.push_back(make_unique<FuncCall>("empty_cart", move(emptyCheck)));
            }
            pArgs.push_back(make_unique<FuncCall>("not", move(notEmptyCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("delete_cart", move(callArgs));

        /* post: error("Cart not empty: clear items first") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cart_not_empty_clear_items_first"));
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
    
    // ADMINS: Map<string, AdminRecord>
    globals.push_back(make_unique<Decl>(
        "ADMINS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("AdminRecord"))));
    
    // CARTS: Map<string, CartRecord> (customerId -> cart details)
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CartRecord"))));

    vector<unique_ptr<Init>> inits;
    
    // Initialize empty CUSTOMERS map (will be populated during signup)
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
    
    // Initialize empty CARTS map (new customers start with empty carts)
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the customer flow path ─────── */
Program clientProgram = buildEcommerceCustomerFlowClientProgram();
Spec    spec          = buildEcommerceCustomerFlowSpec();

/*
 * Expected execution flow (CUSTOMER SCENARIO):
 * 1. signup(customer@example.com, secure_pass_456, John, Doe) → HTTP 200 OK (signup success)
 *    - Precondition: and(not_in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), valid_email(email), valid_password(password))
 *    - New customer registration with unique email
 *    - Returns customer_signup_success(email, new_customer_id)
 *    - Adds new customer record to CUSTOMERS map
 *    - Initializes empty cart for new customer
 * 
 * 2. login(customer@example.com, secure_pass_456) → HTTP 200 OK (login success)
 *    - Precondition: and(in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), equals(get_password(CUSTOMERS, email, password), password))
 *    - Customer credentials validated against newly created CUSTOMERS record
 *    - Returns customer_login_success(email)
 *    - Establishes authenticated customer session
 * 
 * 3. delete_cart() → HTTP 200 OK (cart deletion success)
 *    - Precondition: and(customer_authenticated(), empty_cart(current_user()))
 *    - Deletes empty cart (new customer has no items in cart)
 *    - Returns cart_deleted_success(current_user())
 *    - Cart removal for authenticated customer with empty cart
 * 
 * CUSTOMER FLOW FEATURES:
 * - New customer registration with email uniqueness validation
 * - Customer authentication separate from admin authentication
 * - Empty cart deletion (typical for new customers who haven't added items)
 * - HTTP 400 BAD_REQUEST for various error conditions
 * 
 * ERROR HANDLING:
 * - Signup failure: Email already exists (customer or admin)
 * - Login failure: Invalid credentials or non-existent user
 * - Delete cart failure: Not authenticated or cart contains items
 * 
 * DATA FLOW:
 * - Signup creates new CustomerRecord in CUSTOMERS map
 * - Login validates against newly created customer record
 * - Delete cart operates on empty cart (new customer scenario)
 * 
 * SECURITY CONSIDERATIONS:
 * - Email validation prevents duplicate registrations
 * - Authentication required for cart operations
 * - Clear separation between customer and admin domains
 * 
 * This demonstrates a typical new customer onboarding flow using
 * formal specifications to ensure proper validation, authentication,
 * and state management in e-commerce customer registration systems.
 */