#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for signup(success) → login(success) → place_order
// ─────────────────────────────────────────────────────────────
static Program buildEcommercePlaceOrderClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string email;
    decls.push_back(make_unique<Decl>("email",
                     make_unique<TypeConst>("string")));
    // string password;
    decls.push_back(make_unique<Decl>("password",
                     make_unique<TypeConst>("string")));
    // string fullName;
    decls.push_back(make_unique<Decl>("fullName",
                     make_unique<TypeConst>("string")));
    // string customerId;
    decls.push_back(make_unique<Decl>("customerId",
                     make_unique<TypeConst>("string")));
    // string shippingAddress;
    decls.push_back(make_unique<Decl>("shippingAddress",
                     make_unique<TypeConst>("string")));
    // string paymentMethod;
    decls.push_back(make_unique<Decl>("paymentMethod",
                     make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: signup(success) - Register new user
    // ══════════════════════════════════════════════════════════
    // email = input(); // new unique email
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
    // signup(email, password, fullName); // This will SUCCESS - new email
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        a.push_back(make_unique<Var>("fullName"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: login(success) - Login with registered credentials
    // ══════════════════════════════════════════════════════════
    // email = input(); // same email as signup
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
    // login(email, password); // This will SUCCESS - correct credentials
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: place_order - Create and place an order
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (derived from email after login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // shippingAddress = input(); // delivery address
    {
        auto lhs = make_unique<Var>("shippingAddress");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // paymentMethod = input(); // payment method (credit_card, paypal, etc.)
    {
        auto lhs = make_unique<Var>("paymentMethod");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // place_order(customerId, shippingAddress, paymentMethod); // This will SUCCESS - valid customer with cart items
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("shippingAddress"));
        a.push_back(make_unique<Var>("paymentMethod"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST with place_order functionality
// ─────────────────────────────────────────────────────────────
static Spec buildEcommercePlaceOrderSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Signup API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("email"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        callArgs.push_back(make_unique<Var>("fullName"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMERS"));
            idx.push_back(make_unique<Var>("email"));
            postArgs.push_back(
                make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> customerRecord;
        customerRecord.push_back(make_unique<Var>("password"));
        customerRecord.push_back(make_unique<Var>("fullName"));
        customerRecord.push_back(make_unique<Var>("active"));
        postArgs.push_back(make_unique<FuncCall>("customer_record", move(customerRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

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
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  place_order API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), not_empty(CARTS[customerId])) */
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
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("CARTS"));
                idx.push_back(make_unique<Var>("customerId"));
                cartCheck.push_back(
                    make_unique<FuncCall>("mapped_value", move(idx)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_empty", move(cartCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("shippingAddress"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: and(ORDERS[orderId] = {customerId: customerId, items: CARTS[customerId], 
                                       address: shippingAddress, payment: paymentMethod, 
                                       status: "pending"}, 
                     CARTS[customerId] = {}) */
        vector<unique_ptr<Expr>> postArgs;
        {
            // Create new order record
            vector<unique_ptr<Expr>> orderCreation;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("ORDERS"));
                idx.push_back(make_unique<Var>("orderId"));
                orderCreation.push_back(
                    make_unique<FuncCall>("mapped_value", move(idx)));
            }
            vector<unique_ptr<Expr>> orderRecord;
            orderRecord.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> cartItems;
                cartItems.push_back(make_unique<Var>("CARTS"));
                cartItems.push_back(make_unique<Var>("customerId"));
                orderRecord.push_back(make_unique<FuncCall>("mapped_value", move(cartItems)));
            }
            orderRecord.push_back(make_unique<Var>("shippingAddress"));
            orderRecord.push_back(make_unique<Var>("paymentMethod"));
            orderRecord.push_back(make_unique<Var>("pending"));
            orderCreation.push_back(make_unique<FuncCall>("order_record", move(orderRecord)));
            postArgs.push_back(make_unique<FuncCall>("equals", move(orderCreation)));
        }
        {
            // Clear customer cart
            vector<unique_ptr<Expr>> cartClear;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("CARTS"));
                idx.push_back(make_unique<Var>("customerId"));
                cartClear.push_back(
                    make_unique<FuncCall>("mapped_value", move(idx)));
            }
            cartClear.push_back(make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()));
            postArgs.push_back(make_unique<FuncCall>("equals", move(cartClear)));
        }
        auto post = make_unique<FuncCall>("and", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  place_order API block - FAILURE case (empty cart or invalid customer)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: or(not_in(customerId, dom(CUSTOMERS)), empty(CARTS[customerId])) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> customerCheck;
            customerCheck.push_back(make_unique<Var>("customerId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                customerCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(customerCheck)));
        }
        {
            vector<unique_ptr<Expr>> cartCheck;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("CARTS"));
                idx.push_back(make_unique<Var>("customerId"));
                cartCheck.push_back(
                    make_unique<FuncCall>("mapped_value", move(idx)));
            }
            pArgs.push_back(make_unique<FuncCall>("empty", move(cartCheck)));
        }
        auto pre = make_unique<FuncCall>("or", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("shippingAddress"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: error("Cannot place order: invalid customer or empty cart") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_place_order_invalid_customer_or_empty_cart"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
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
    
    // CARTS: Map<string, Map<string, int>> (customerId -> (productId -> quantity))
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("int")))));

    // ORDERS: Map<string, OrderRecord> (orderId -> order details)
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the place_order path ─────── */
Program clientProgram = buildEcommercePlaceOrderClientProgram();
Spec    spec          = buildEcommercePlaceOrderSpec();

/*
 * Expected execution flow:
 * 1. signup(email, password, fullName) → HTTP 201 CREATED (success)
 * 2. login(email, password) → HTTP 200 OK (success) 
 * 3. place_order(customerId, shippingAddress, paymentMethod) → HTTP 201 CREATED (success)
 *    - Creates new order record in ORDERS map
 *    - Clears customer's cart after successful order placement
 *    - Returns order confirmation with orderId
 * 
 * This demonstrates how ancient formal specification techniques (pre/post conditions)
 * can precisely define complex business logic in modern e-commerce systems,
 * bridging mathematical rigor with practical API design.
 */