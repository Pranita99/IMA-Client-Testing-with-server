#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *customer client* Program AST for login → view_cart → place_order → view_orders
// ─────────────────────────────────────────────────────────────
static Program buildCustomerClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string customerEmail;
    decls.push_back(make_unique<Decl>("customerEmail",
                     make_unique<TypeConst>("string")));
    // customerEmail = input();
    {
        auto lhs = make_unique<Var>("customerEmail");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string customerPassword;
    decls.push_back(make_unique<Decl>("customerPassword",
                     make_unique<TypeConst>("string")));
    // customerPassword = input();
    {
        auto lhs = make_unique<Var>("customerPassword");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // customer_login(customerEmail, customerPassword);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerEmail"));
        a.push_back(make_unique<Var>("customerPassword"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("customer_login", move(a))));
    }

    // string customerId;
    decls.push_back(make_unique<Decl>("customerId",
                     make_unique<TypeConst>("string")));
    // customerId = input();
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // view_cart(customerId);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // string shippingAddress;
    decls.push_back(make_unique<Decl>("shippingAddress",
                     make_unique<TypeConst>("string")));
    // shippingAddress = input();
    {
        auto lhs = make_unique<Var>("shippingAddress");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string paymentMethod;
    decls.push_back(make_unique<Decl>("paymentMethod",
                     make_unique<TypeConst>("string")));
    // paymentMethod = input();
    {
        auto lhs = make_unique<Var>("paymentMethod");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // place_order(customerId, shippingAddress, paymentMethod);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("shippingAddress"));
        a.push_back(make_unique<Var>("paymentMethod"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // view_orders(customerId);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_orders", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Customer Ecommerce API *Spec* AST with customer_login/view_cart/place_order/view_orders functionality
// ─────────────────────────────────────────────────────────────
static Spec buildCustomerEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Customer Login API block ---
    {
        /* pre: customerEmail ∈ dom(CUSTOMERS) && CUSTOMERS[customerEmail].password = customerPassword && customerSessionToken ∉ dom(CUSTOMER_SESSIONS) */
        vector<unique_ptr<Expr>> emailExists;
        emailExists.push_back(make_unique<Var>("customerEmail"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            emailExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMERS"));
            idx.push_back(make_unique<Var>("customerEmail"));
            vector<unique_ptr<Expr>> field;
            field.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            field.push_back(make_unique<Var>("password"));
            passwordMatch.push_back(make_unique<FuncCall>("get_field", move(field)));
        }
        passwordMatch.push_back(make_unique<Var>("customerPassword"));
        
        vector<unique_ptr<Expr>> sessionNotExists;
        sessionNotExists.push_back(make_unique<Var>("customerSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMER_SESSIONS"));
            sessionNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        landArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        landArgs.push_back(make_unique<FuncCall>("not_in", move(sessionNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerEmail"));
        callArgs.push_back(make_unique<Var>("customerPassword"));
        auto callFn = make_unique<FuncCall>("customer_login", move(callArgs));

        /* post: CUSTOMER_SESSIONS[customerSessionToken] = {email: customerEmail, loginTime: currentTime, role: "customer"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMER_SESSIONS"));
            idx.push_back(make_unique<Var>("customerSessionToken"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> sessionRecord;
        sessionRecord.push_back(make_unique<Var>("customerEmail"));
        sessionRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        sessionRecord.push_back(make_unique<Var>("customer"));
        postArgs.push_back(make_unique<FuncCall>("customer_session_record", move(sessionRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- View Cart API block ---
    {
        /* pre: customerId ∈ dom(CUSTOMERS) && customerSessionToken ∈ dom(CUSTOMER_SESSIONS) */
        vector<unique_ptr<Expr>> customerExists;
        customerExists.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            customerExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("customerSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMER_SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(customerExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: return CARTS[customerId] (cart remains unchanged) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("returned_cart_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Place Order API block ---
    {
        /* pre: customerId ∈ dom(CUSTOMERS) && customerSessionToken ∈ dom(CUSTOMER_SESSIONS) && CARTS[customerId] ≠ empty && orderId ∉ dom(ORDERS) */
        vector<unique_ptr<Expr>> customerExists;
        customerExists.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            customerExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("customerSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMER_SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> cartNotEmpty;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("customerId"));
            cartNotEmpty.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        cartNotEmpty.push_back(make_unique<Var>("empty_cart"));
        
        vector<unique_ptr<Expr>> orderNotExists;
        orderNotExists.push_back(make_unique<Var>("orderId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ORDERS"));
            orderNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(customerExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("not_equals", move(cartNotEmpty)));
        landArgs.push_back(make_unique<FuncCall>("not_in", move(orderNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("shippingAddress"));
        callArgs.push_back(make_unique<Var>("paymentMethod"));
        auto callFn = make_unique<FuncCall>("place_order", move(callArgs));

        /* post: ORDERS[orderId] = {customerId: customerId, items: CARTS[customerId], shippingAddress: shippingAddress, paymentMethod: paymentMethod, status: "pending", orderTime: currentTime} && CARTS[customerId] = empty */
        vector<unique_ptr<Expr>> orderCreated;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ORDERS"));
            idx.push_back(make_unique<Var>("orderId"));
            orderCreated.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> orderRecord;
        orderRecord.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("customerId"));
            orderRecord.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        orderRecord.push_back(make_unique<Var>("shippingAddress"));
        orderRecord.push_back(make_unique<Var>("paymentMethod"));
        orderRecord.push_back(make_unique<Var>("pending"));
        orderRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        orderCreated.push_back(make_unique<FuncCall>("order_record", move(orderRecord)));
        
        vector<unique_ptr<Expr>> cartCleared;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("customerId"));
            cartCleared.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        cartCleared.push_back(make_unique<Var>("empty_cart"));
        
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<FuncCall>("equals", move(orderCreated)));
        postArgs.push_back(make_unique<FuncCall>("equals", move(cartCleared)));
        auto post = make_unique<FuncCall>("and_operator", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- View Orders API block ---
    {
        /* pre: customerId ∈ dom(CUSTOMERS) && customerSessionToken ∈ dom(CUSTOMER_SESSIONS) */
        vector<unique_ptr<Expr>> customerExists;
        customerExists.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            customerExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("customerSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMER_SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(customerExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_orders", move(callArgs));

        /* post: return filtered ORDERS where customerId matches (orders remain unchanged) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("ORDERS"));
            filterArgs.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("filter_orders_by_customer", move(filterArgs)));
        }
        postArgs.push_back(make_unique<Var>("returned_orders_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // CUSTOMERS: Map<string, CustomerRecord>
    globals.push_back(make_unique<Decl>(
        "CUSTOMERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CustomerRecord"))));
    // CUSTOMER_SESSIONS: Map<string, CustomerSessionRecord>
    globals.push_back(make_unique<Decl>(
        "CUSTOMER_SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CustomerSessionRecord"))));
    // CARTS: Map<string, CartRecord>
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CartRecord"))));
    // ORDERS: Map<string, OrderRecord>
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "CUSTOMER_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildCustomerClientProgram();
Spec    spec          = buildCustomerEcommerceSpec();