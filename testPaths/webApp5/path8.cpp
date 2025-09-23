#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for complete e-commerce flow:
//  signup(success) → login(success) → get_products → add_to_cart → view_cart → place_order → view_orders
// ─────────────────────────────────────────────────────────────
static Program buildCompleteEcommerceClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("fullName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("customerId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity", make_unique<TypeConst>("int")));
    decls.push_back(make_unique<Decl>("shippingAddress", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("paymentMethod", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("orderId", make_unique<TypeConst>("string")));

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
    //  STEP 3: get_products - Retrieve available products
    // ══════════════════════════════════════════════════════════
    // get_products(); // This will SUCCESS - returns product catalog
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_products", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: add_to_cart - Add product to shopping cart
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (derived from email after login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId = input(); // product to add to cart
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity = input(); // quantity to add
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(customerId, productId, quantity); // This will SUCCESS - valid product and customer
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: view_cart - View current cart contents
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // same customer ID
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_cart(customerId); // This will SUCCESS - returns cart contents
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 6: place_order - Create and place an order
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // same customer ID
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

    // ══════════════════════════════════════════════════════════
    //  STEP 7: view_orders - View customer's order history
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // same customer ID
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_orders(customerId); // This will SUCCESS - returns customer's order history
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_orders", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Complete Ecommerce API *Spec* AST with all functionality
// ─────────────────────────────────────────────────────────────
static Spec buildCompleteEcommerceSpec()
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
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  get_products API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: true (always succeeds) */
        vector<unique_ptr<Expr>> pArgs;
        auto pre = make_unique<FuncCall>("true", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_products", move(callArgs));

        /* post: products_list(PRODUCTS) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("PRODUCTS"));
        auto post = make_unique<FuncCall>("products_list", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  add_to_cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(productId, dom(PRODUCTS)), gt(quantity, 0)) */
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
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: CARTS[customerId][productId] = quantity */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> cartUpdate;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("CARTS"));
                idx.push_back(make_unique<Var>("customerId"));
                idx.push_back(make_unique<Var>("productId"));
                cartUpdate.push_back(make_unique<FuncCall>("nested_mapped_value", move(idx)));
            }
            cartUpdate.push_back(make_unique<Var>("quantity"));
            postArgs.push_back(make_unique<FuncCall>("equals", move(cartUpdate)));
        }
        auto post = make_unique<FuncCall>("and", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  add_to_cart API block - FAILURE case (invalid product or customer)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: or(not_in(customerId, dom(CUSTOMERS)), not_in(productId, dom(PRODUCTS)), lte(quantity, 0)) */
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
            vector<unique_ptr<Expr>> productCheck;
            productCheck.push_back(make_unique<Var>("productId"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("PRODUCTS"));
                productCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(productCheck)));
        }
        {
            vector<unique_ptr<Expr>> quantityCheck;
            quantityCheck.push_back(make_unique<Var>("quantity"));
            quantityCheck.push_back(make_unique<Var>("0"));
            pArgs.push_back(make_unique<FuncCall>("lte", move(quantityCheck)));
        }
        auto pre = make_unique<FuncCall>("or", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: error("Cannot add to cart: invalid customer, product, or quantity") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_add_to_cart_invalid_customer_product_or_quantity"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: in(customerId, dom(CUSTOMERS)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: cart_contents(CARTS[customerId]) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        auto post = make_unique<FuncCall>("cart_contents", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_cart API block - FAILURE case (invalid customer)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not_in(customerId, dom(CUSTOMERS)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: error("Cannot view cart: invalid customer") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_view_cart_invalid_customer"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
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
                cartCheck.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
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
                orderCreation.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
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
                cartClear.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            cartClear.push_back(make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()));
            postArgs.push_back(make_unique<FuncCall>("equals", move(cartClear)));
        }
        auto post = make_unique<FuncCall>("and", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
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
                cartCheck.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
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
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_orders API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: in(customerId, dom(CUSTOMERS)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_orders", move(callArgs));

        /* post: customer_orders(filter_orders_by_customer(ORDERS, customerId)) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("ORDERS"));
            filterArgs.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("filter_orders_by_customer", move(filterArgs)));
        }
        auto post = make_unique<FuncCall>("customer_orders", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  view_orders API block - FAILURE case (invalid customer)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not_in(customerId, dom(CUSTOMERS)) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("customerId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        auto callFn = make_unique<FuncCall>("view_orders", move(callArgs));

        /* post: error("Cannot view orders: invalid customer") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Cannot_view_orders_invalid_customer"));
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

    // ORDERS: Map<string, OrderRecord> (orderId -> order details)
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize PRODUCTS with sample data
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productEntries;
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Laptop"));
        productRecord.push_back(make_unique<Var>("999.99"));
        productRecord.push_back(make_unique<Var>("High_performance_laptop"));
        productRecord.push_back(make_unique<Var>("10"));
        productEntries.emplace_back(
            make_unique<Var>("prod_001"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Smartphone"));
        productRecord.push_back(make_unique<Var>("699.99"));
        productRecord.push_back(make_unique<Var>("Latest_smartphone_model"));
        productRecord.push_back(make_unique<Var>("25"));
        productEntries.emplace_back(
            make_unique<Var>("prod_002"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Headphones"));
        productRecord.push_back(make_unique<Var>("199.99"));
        productRecord.push_back(make_unique<Var>("Wireless_noise_cancelling_headphones"));
        productRecord.push_back(make_unique<Var>("50"));
        productEntries.emplace_back(
            make_unique<Var>("prod_003"),
            make_unique<FuncCall>("product_record", move(productRecord))
        );
    }
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(move(productEntries))));
    
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ORDERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the complete e-commerce path ─────── */
Program clientProgram = buildCompleteEcommerceClientProgram();
Spec    spec          = buildCompleteEcommerceSpec();

/*
 * Expected execution flow:
 * 1. signup(email, password, fullName) → HTTP 201 CREATED (success)
 *    - Creates new customer account in CUSTOMERS map
 *    - Initializes empty cart for the customer
 * 
 * 2. login(email, password) → HTTP 200 OK (success) 
 *    - Validates credentials and establishes session
 *    - Returns customer authentication token/session
 * 
 * 3. get_products() → HTTP 200 OK (success)
 *    - Returns complete product catalog from PRODUCTS map
 *    - Shows available items with prices, descriptions, and stock
 * 
 * 4. add_to_cart(customerId, productId, quantity) → HTTP 200 OK (success)
 *    - Adds specified product and quantity to customer's cart
 *    - Updates CARTS[customerId][productId] with new quantity
 *    - Validates product exists and quantity is positive
 * 
 * 5. view_cart(customerId) → HTTP 200 OK (success)
 *    - Returns current contents of customer's shopping cart
 *    - Shows all products, quantities, and calculated totals
 * 
 * 6. place_order(customerId, shippingAddress, paymentMethod) → HTTP 201 CREATED (success)
 *    - Creates new order record in ORDERS map with unique orderId
 *    - Transfers cart contents to order items
 *    - Clears customer's cart after successful order placement
 *    - Sets initial order status to "pending"
 * 
 * 7. view_orders(customerId) → HTTP 200 OK (success)
 *    - Returns customer's complete order history
 *    - Filters ORDERS map by customerId to show only customer's orders
 *    - Includes order status, items, addresses, and payment methods
 * 
 * This demonstrates a complete e-commerce user journey from registration
 * to order completion, using formal specification techniques to precisely
 * define API contracts, state transitions, and business logic constraints.
 * Each step includes both success and failure cases with appropriate
 * HTTP response codes and error messages.
 */