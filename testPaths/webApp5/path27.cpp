#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for extended customer flow:
//  signup(success) → login(success) → add_to_cart → delete_cart → place_order
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceExtendedCustomerFlowClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("firstName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("lastName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity", make_unique<TypeConst>("int")));
    decls.push_back(make_unique<Decl>("address", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("paymentMethod", make_unique<TypeConst>("string")));

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
    //  STEP 3: add_to_cart - Add product to customer's cart
    // ══════════════════════════════════════════════════════════
    // productId = input(); // product to add (e.g., "prod_001")
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity = input(); // quantity to add (e.g., 2)
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(productId, quantity); // This will SUCCESS - adds item to cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: delete_cart - Clear all items from cart
    // ══════════════════════════════════════════════════════════
    // delete_cart(); // This will SUCCESS - removes all items from cart
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("delete_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: place_order - Place order with empty cart (should fail gracefully)
    // ══════════════════════════════════════════════════════════
    // address = input(); // shipping address
    {
        auto lhs = make_unique<Var>("address");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // paymentMethod = input(); // payment method (e.g., "credit_card")
    {
        auto lhs = make_unique<Var>("paymentMethod");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // place_order(address, paymentMethod); // This will FAIL - cart is empty after deletion
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("address"));
        a.push_back(make_unique<Var>("paymentMethod"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for extended customer flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceExtendedCustomerFlowSpec()
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
    //  add_to_cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(customer_authenticated(), in(productId, dom(PRODUCTS)), greater_than(quantity, 0), sufficient_stock(productId, quantity)) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        {
            vector<unique_ptr<Expr>> productExists;
            productExists.push_back(make_unique<Var>("productId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("PRODUCTS"));
                productExists.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        }
        {
            vector<unique_ptr<Expr>> quantityValid;
            quantityValid.push_back(make_unique<Var>("quantity"));
            quantityValid.push_back(make_unique<Var>("0"));
            pArgs.push_back(make_unique<FuncCall>("greater_than", move(quantityValid)));
        }
        {
            vector<unique_ptr<Expr>> stockCheck;
            stockCheck.push_back(make_unique<Var>("productId"));
            stockCheck.push_back(make_unique<Var>("quantity"));
            pArgs.push_back(make_unique<FuncCall>("sufficient_stock", move(stockCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: item_added_to_cart(current_user(), productId, quantity) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userArg;
            postArgs.push_back(make_unique<FuncCall>("current_user", move(userArg)));
        }
        postArgs.push_back(make_unique<Var>("productId"));
        postArgs.push_back(make_unique<Var>("quantity"));
        auto post = make_unique<FuncCall>("item_added_to_cart", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  add_to_cart API block - FAILURE case (not authenticated)
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
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: error("Authentication required") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Authentication_required"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  delete_cart API block - SUCCESS case (cart has items)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(customer_authenticated(), not(empty_cart(current_user()))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        {
            vector<unique_ptr<Expr>> hasItemsCheck;
            {
                vector<unique_ptr<Expr>> emptyCheck;
                {
                    vector<unique_ptr<Expr>> userCheck;
                    emptyCheck.push_back(make_unique<FuncCall>("current_user", move(userCheck)));
                }
                hasItemsCheck.push_back(make_unique<FuncCall>("empty_cart", move(emptyCheck)));
            }
            pArgs.push_back(make_unique<FuncCall>("not", move(hasItemsCheck)));
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
    //  place_order API block - SUCCESS case (cart has items)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(customer_authenticated(), not(empty_cart(current_user())), valid_address(address), valid_payment_method(paymentMethod)) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> authCheck;
            pArgs.push_back(make_unique<FuncCall>("customer_authenticated", move(authCheck)));
        }
        {
            vector<unique_ptr<Expr>> hasItemsCheck;
            {
                vector<unique_ptr<Expr>> emptyCheck;
                {
                    vector<unique_ptr<Expr>> userCheck;
                    emptyCheck.push_back(make_unique<FuncCall>("current_user", move(userCheck)));
                }
                hasItemsCheck.push_back(make_unique<FuncCall>("empty_cart", move(emptyCheck)));
            }
            pArgs.push_back(make_unique<FuncCall>("not", move(hasItemsCheck)));
        }
        {
            vector<unique_ptr<Expr>> addressValid;
            addressValid.push_back(make_unique<Var>("address"));
            pArgs.push_back(make_unique<FuncCall>("valid_address", move(addressValid)));
        }
        {
            vector<unique_ptr<Expr>> paymentValid;
            paymentValid.push_back(make_unique<Var>("paymentMethod"));
            pArgs.push_back(make_unique<FuncCall>("valid_payment_method", move(paymentValid)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("address"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: order_placed_success(current_user(), new_order_id, address, paymentMethod) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> userArg;
            postArgs.push_back(make_unique<FuncCall>("current_user", move(userArg)));
        }
        postArgs.push_back(make_unique<Var>("new_order_id"));
        postArgs.push_back(make_unique<Var>("address"));
        postArgs.push_back(make_unique<Var>("paymentMethod"));
        auto post = make_unique<FuncCall>("order_placed_success", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  place_order API block - FAILURE case (empty cart)
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
        callArgs.push_back(make_unique<Var>("address"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: error("Cannot place order: cart is empty") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_place_order_cart_is_empty"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  place_order API block - FAILURE case (not authenticated)
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
        callArgs.push_back(make_unique<Var>("address"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: error("Authentication required") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Authentication_required"));
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
    
    // PRODUCTS: Map<string, ProductRecord> (productId -> product details)
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));
    
    // ORDERS: Map<string, OrderRecord> (orderId -> order details)
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

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
    
    // Initialize PRODUCTS with sample product data
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productEntries;
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Wireless_Bluetooth_Headphones"));
        productRecord.push_back(make_unique<Var>("59.99"));
        productRecord.push_back(make_unique<Var>("Electronics"));
        productRecord.push_back(make_unique<Var>("100"));
        productRecord.push_back(make_unique<Var>("available"));
        productEntries.emplace_back(
            make_unique<Var>("prod_001"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Ergonomic_Office_Chair"));
        productRecord.push_back(make_unique<Var>("299.99"));
        productRecord.push_back(make_unique<Var>("Furniture"));
        productRecord.push_back(make_unique<Var>("25"));
        productRecord.push_back(make_unique<Var>("available"));
        productEntries.emplace_back(
            make_unique<Var>("prod_002"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Premium_Coffee_Beans_1kg"));
        productRecord.push_back(make_unique<Var>("24.99"));
        productRecord.push_back(make_unique<Var>("Food"));
        productRecord.push_back(make_unique<Var>("200"));
        productRecord.push_back(make_unique<Var>("available"));
        productEntries.emplace_back(
            make_unique<Var>("prod_003"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(move(productEntries))));
    
    // Initialize empty ORDERS map (will be populated when orders are placed)
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the extended customer flow path ─────── */
Program clientProgram = buildEcommerceExtendedCustomerFlowClientProgram();
Spec    spec          = buildEcommerceExtendedCustomerFlowSpec();

/*
 * Expected execution flow (EXTENDED CUSTOMER SCENARIO):
 * 1. signup(customer@example.com, secure_pass_456, John, Doe) → HTTP 200 OK (signup success)
 *    - Precondition: and(not_in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), valid_email(email), valid_password(password))
 *    - New customer registration with unique email validation
 *    - Returns customer_signup_success(email, new_customer_id)
 *    - Creates new CustomerRecord in CUSTOMERS map
 *    - Initializes empty cart for new customer
 * 
 * 2. login(customer@example.com, secure_pass_456) → HTTP 200 OK (login success)
 *    - Precondition: and(in(email, dom(CUSTOMERS)), not_in(email, dom(ADMINS)), equals(get_password(CUSTOMERS, email, password), password))
 *    - Customer credentials validated against newly created CUSTOMERS record
 *    - Returns customer_login_success(email)
 *    - Establishes authenticated customer session
 * 
 * 3. add_to_cart(prod_001, 2) → HTTP 200 OK (item added successfully)
 *    - Precondition: and(customer_authenticated(), in(productId, dom(PRODUCTS)), greater_than(quantity, 0), sufficient_stock(productId, quantity))
 *    - Adds 2 units of "Wireless_Bluetooth_Headphones" to cart
 *    - Returns item_added_to_cart(current_user(), productId, quantity)
 *    - Updates customer's cart with selected product and quantity
 * 
 * 4. delete_cart() → HTTP 200 OK (cart cleared successfully)
 *    - Precondition: and(customer_authenticated(), not(empty_cart(current_user())))
 *    - Deletes all items from cart (cart had items from previous step)
 *    - Returns cart_deleted_success(current_user())
 *    - Customer's cart is now empty
 * 
 * 5. place_order(123_Main_St_Anytown_USA, credit_card) → HTTP 400 BAD_REQUEST (failure - empty cart)
 *    - Precondition: and(customer_authenticated(), empty_cart(current_user()))
 *    - Attempts to place order but cart is empty after deletion
 *    - Returns error("Cannot place order: cart is empty")
 *    - Demonstrates proper validation of cart state before order placement
 * 
 * EXTENDED FLOW FEATURES:
 * - Complete customer journey from registration to order attempt
 * - Product inventory management with stock validation
 * - Shopping cart operations (add items, clear cart)
 * - Order placement with proper precondition validation
 * - Realistic failure scenario (empty cart order attempt)
 * 
 * BUSINESS LOGIC:
 * - Cart operations require authentication
 * - Product validation ensures valid items and sufficient stock
 * - Order placement requires non-empty cart and valid payment/address
 * - Clear separation between successful operations and expected failures
 * 
 * ERROR HANDLING:
 * - Authentication checks for all cart/order operations
 * - Product existence and stock validation for add_to_cart
 * - Empty cart validation for order placement
 * - Comprehensive error messages for different failure scenarios
 * 
 * DATA STRUCTURES:
 * - CUSTOMERS: User accounts with authentication data
 * - PRODUCTS: Product catalog with pricing and inventory
 * - CARTS: Customer shopping carts with items and quantities
 * - ORDERS: Completed order records (empty initially)
 * - ADMINS: Administrative accounts (separate from customers)
 * 
 * SECURITY MODEL:
 * - Role-based access control (customer vs admin)
 * - Session-based authentication for cart operations
 * - Input validation for all user-provided data
 * - Proper separation of customer and administrative domains
 * 
 * This demonstrates a comprehensive e-commerce customer flow with proper
 * state management, validation, and error handling using formal specifications
 * to ensure robust business logic implementation and security controls.
 */
 