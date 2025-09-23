#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for the flow:
//  signup → login → add_to_cart → remove_from_cart → add_to_cart → place_order → view_orders
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceSignupToViewOrdersClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("name", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("customerId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId1", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId2", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity1", make_unique<TypeConst>("int")));
    decls.push_back(make_unique<Decl>("quantity2", make_unique<TypeConst>("int")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: signup(success) - Register new customer
    // ══════════════════════════════════════════════════════════
    // email = input(); // new customer email
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input(); // new password
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // name = input(); // customer name
    {
        auto lhs = make_unique<Var>("name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // signup(email, password, name); // This will SUCCESS - new customer registration
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        a.push_back(make_unique<Var>("name"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("signup", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: login(success) - Login with newly created credentials
    // ══════════════════════════════════════════════════════════
    // login(email, password); // This will SUCCESS - newly registered customer
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: add_to_cart(success) - Add first product to cart
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (from login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId1 = input(); // first product ID
    {
        auto lhs = make_unique<Var>("productId1");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity1 = input(); // valid quantity
    {
        auto lhs = make_unique<Var>("quantity1");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(customerId, productId1, quantity1); // This will SUCCESS
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("productId1"));
        a.push_back(make_unique<Var>("quantity1"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: remove_from_cart(success) - Remove product from cart
    // ══════════════════════════════════════════════════════════
    // remove_from_cart(customerId, productId1); // This will SUCCESS - product is in cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("productId1"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("remove_from_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: add_to_cart(success) - Add different product to cart
    // ══════════════════════════════════════════════════════════
    // productId2 = input(); // second product ID
    {
        auto lhs = make_unique<Var>("productId2");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity2 = input(); // valid quantity
    {
        auto lhs = make_unique<Var>("quantity2");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(customerId, productId2, quantity2); // This will SUCCESS
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        a.push_back(make_unique<Var>("productId2"));
        a.push_back(make_unique<Var>("quantity2"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 6: place_order(success) - Create order with cart contents
    // ══════════════════════════════════════════════════════════
    // place_order(customerId); // This will SUCCESS - user is logged in and cart has items
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 7: view_orders(success) - View customer's order history
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
//  Build the Ecommerce API *Spec* AST for signup→login→cart operations→place_order→view_orders flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceSignupToViewOrdersSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Signup API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(not_in(email, dom(CUSTOMERS)), not(empty(password)), not(empty(name))) */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> emailCheck;
            emailCheck.push_back(make_unique<Var>("email"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("CUSTOMERS"));
                emailCheck.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            pArgs.push_back(make_unique<FuncCall>("not_in", move(emailCheck)));
        }
        {
            vector<unique_ptr<Expr>> passwordCheck;
            passwordCheck.push_back(make_unique<Var>("password"));
            pArgs.push_back(make_unique<FuncCall>("not_empty", move(passwordCheck)));
        }
        {
            vector<unique_ptr<Expr>> nameCheck;
            nameCheck.push_back(make_unique<Var>("name"));
            pArgs.push_back(make_unique<FuncCall>("not_empty", move(nameCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        callArgs.push_back(make_unique<Var>("name"));
        auto callFn = make_unique<FuncCall>("signup", move(callArgs));

        /* post: customer_created(email, name) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("email"));
        postArgs.push_back(make_unique<Var>("name"));
        auto post = make_unique<FuncCall>("customer_created", move(postArgs));

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
    //  remove_from_cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: and(in(customerId, dom(CUSTOMERS)), in(customerId, dom(ACTIVE_SESSIONS)),
                    in(productId, get_cart_products(CARTS, customerId))) */
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
        {
            vector<unique_ptr<Expr>> productInCartCheck;
            productInCartCheck.push_back(make_unique<Var>("productId"));
            {
                vector<unique_ptr<Expr>> cartProducts;
                cartProducts.push_back(make_unique<Var>("CARTS"));
                cartProducts.push_back(make_unique<Var>("customerId"));
                productInCartCheck.push_back(make_unique<FuncCall>("get_cart_products", move(cartProducts)));
            }
            pArgs.push_back(make_unique<FuncCall>("in", move(productInCartCheck)));
        }
        auto pre = make_unique<FuncCall>("and", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("customerId"));
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("remove_from_cart", move(callArgs));

        /* post: product_removed_from_cart(customerId, productId) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("customerId"));
        postArgs.push_back(make_unique<Var>("productId"));
        auto post = make_unique<FuncCall>("product_removed_from_cart", move(postArgs));

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
    
    // Pre-populate PRODUCTS with available items
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> productEntries;
        
        // Product: "product1" -> product_record("Product Name 1", 1299.99, 10)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Product_Name_1"));
            productArgs.push_back(make_unique<Var>("1299.99"));
            productArgs.push_back(make_unique<Var>("10"));
            productEntries.emplace_back(
                make_unique<Var>("product1"),
                make_unique<FuncCall>("product_record", move(productArgs))
            );
        }
        
        // Product: "product2" -> product_record("Product Name 2", 699.99, 15)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Product_Name_2"));
            productArgs.push_back(make_unique<Var>("699.99"));
            productArgs.push_back(make_unique<Var>("15"));
            productEntries.emplace_back(
                make_unique<Var>("product2"),
                make_unique<FuncCall>("product_record", move(productArgs))
            );
        }
        
        inits.push_back(make_unique<Init>(
            "PRODUCTS", make_unique<Map>(move(productEntries))));
    }
    
    // Initialize empty collections
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
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

/* ── globals the driver expects for the signup→login→cart operations→place_order→view_orders flow ─────── */
Program clientProgram = buildEcommerceSignupToViewOrdersClientProgram();
Spec    spec          = buildEcommerceSignupToViewOrdersSpec();

/*
 * Expected execution flow (ALL SUCCESS SCENARIO):
 * 
 * 1. signup(email, password, name) → HTTP 201 CREATED (success)
 *    - Registers a new customer account
 *    - Precondition: Email not already registered, password and name not empty
 *    - Postcondition: customer_created(email, name) + new entry in CUSTOMERS
 *    - Customer account is now available for login
 * 
 * 2. login(email, password) → HTTP 200 OK (success)
 *    - Authenticates with newly created credentials
 *    - Precondition: Customer exists, password matches, not already logged in
 *    - Postcondition: login_success(email) + session created in ACTIVE_SESSIONS
 *    - User is now authenticated and can perform operations
 * 
 * 3. add_to_cart(customerId, productId1, quantity1) → HTTP 200 OK (success)
 *    - Adds first product to cart while logged in
 *    - Precondition: Customer exists, product exists, quantity > 0, user in active session
 *    - Postcondition: cart_updated(customerId, productId1, quantity1)
 *    - Cart now contains the first selected product
 * 
 * 4. remove_from_cart(customerId, productId1) → HTTP 200 OK (success)
 *    - Removes the previously added product from cart
 *    - Precondition: Customer exists, user in active session, product exists in customer's cart
 *    - Postcondition: product_removed_from_cart(customerId, productId1)
 *    - Cart is now empty again
 * 
 * 5. add_to_cart(customerId, productId2, quantity2) → HTTP 200 OK (success)
 *    - Adds a different product to cart
 *    - Precondition: Customer exists, product exists, quantity > 0, user in active session
 *    - Postcondition: cart_updated(customerId, productId2, quantity2)
 *    - Cart now contains the second selected product
 * 
 * 6. place_order(customerId) → HTTP 201 CREATED (success)
 *    - Creates order from current cart contents
 *    - Precondition: Customer exists, cart not empty, user in active session
 *    - Postcondition: order_created(customerId, orderId) + new entry in ORDERS
 *    - Order is successfully placed and customer has order history
 * 
 * 7. view_orders(customerId) → HTTP 200 OK (success)
 *    - Retrieves customer's order history
 *    - Precondition: Customer exists and is logged in
 *    - Postcondition: orders_retrieved(customerId, order_list)
 *    - Customer can see their order history including the just-placed order
 * 
 * This scenario demonstrates a complete e-commerce customer journey:
 * 
 * **Customer Lifecycle:**
 * - Account creation (signup)
 * - Authentication (login)
 * - Shopping behavior (add/remove items)
 * - Purchase completion (place order)
 * - Order management (view order history)
 * 
 * **Cart Management:**
 * - Adding products to cart
 * - Removing unwanted products
 * - Adding different products
 * - Cart state affects order creation
 * 
 * **Session Management:**
 * - All operations require authentication after login
 * - ACTIVE_SESSIONS tracks logged-in users
 * - Session state affects API behavior
 * 
 * **Data Persistence:**
 * - Customer data persists after signup
 * - Cart operations modify CARTS map
 * - Orders are stored in ORDERS map
 * - Order history is retrievable
 * 
 * **HTTP Status Codes:**
 * - 201 CREATED: Resource creation (signup, place_order)
 * - 200 OK: Successful operations (login, cart ops, view_orders)
 * 
 * **Business Logic:**
 * - New customers can register and immediately login
 * - Cart modifications require authentication
 * - Order placement requires non-empty cart
 * - Order history is accessible to authenticated users
 * 
 * This flow models a realistic new customer experience where someone:
 * - Creates an account
 * - Logs in immediately
 * - Browses and modifies their cart
 * - Completes a purchase
 * - Views their order history
 * 
 * The formal specification precisely captures the state transitions
 * and demonstrates how authentication, cart state, and order management
 * work together in a complete e-commerce system.
 */