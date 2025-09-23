#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for complete success flow:
//  signup → login → get_products → add_to_cart(prod1) → add_to_cart(prod2) 
//  → view_cart → place_order → view_orders → logout
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceSuccessFlowClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("fullName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("customerId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId1", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId2", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("quantity1", make_unique<TypeConst>("int")));
    decls.push_back(make_unique<Decl>("quantity2", make_unique<TypeConst>("int")));
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
    //  STEP 3: get_products(success) - Retrieve populated product catalog
    // ══════════════════════════════════════════════════════════
    // get_products(); // This will SUCCESS and return available products
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_products", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: add_to_cart(prod1, success) - Add first product to cart
    // ══════════════════════════════════════════════════════════
    // customerId = input(); // customer ID (derived from email after login)
    {
        auto lhs = make_unique<Var>("customerId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId1 = input(); // first product that exists in catalog
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
    //  STEP 5: add_to_cart(prod2, success) - Add second product to cart
    // ══════════════════════════════════════════════════════════
    // productId2 = input(); // second product that exists in catalog
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
    //  STEP 6: view_cart(success) - View current cart contents
    // ══════════════════════════════════════════════════════════
    // view_cart(customerId); // This will SUCCESS and show cart items
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 7: place_order(success) - Create order from cart
    // ══════════════════════════════════════════════════════════
    // place_order(customerId); // This will SUCCESS and create order
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("place_order", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 8: view_orders(success) - View customer's order history
    // ══════════════════════════════════════════════════════════
    // view_orders(customerId); // This will SUCCESS and show order history
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_orders", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 9: logout(success) - End user session
    // ══════════════════════════════════════════════════════════
    // logout(customerId); // This will SUCCESS and end session
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customerId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST for complete success flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceSuccessFlowSpec()
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
    //  get_products API block - SUCCESS case (returns populated catalog)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: not(empty(PRODUCTS)) - product catalog has items */
        vector<unique_ptr<Expr>> pArgs;
        {
            vector<unique_ptr<Expr>> emptyCheck;
            emptyCheck.push_back(make_unique<Var>("PRODUCTS"));
            pArgs.push_back(make_unique<FuncCall>("empty", move(emptyCheck)));
        }
        auto pre = make_unique<FuncCall>("not", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("get_products", move(callArgs));

        /* post: products_list(PRODUCTS) - returns populated product list */
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

        /* post: cart_contents(get_cart(CARTS, customerId)) */
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
    //  place_order API block - SUCCESS case
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
            cartCheck.push_back(make_unique<FuncCall>("empty", move(cartCheck)));
            pArgs.push_back(make_unique<FuncCall>("not", move(pArgs)));
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

        /* post: order_history(get_orders(ORDERS, customerId)) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> orderArgs;
            orderArgs.push_back(make_unique<Var>("ORDERS"));
            orderArgs.push_back(make_unique<Var>("customerId"));
            postArgs.push_back(make_unique<FuncCall>("get_orders", move(orderArgs)));
        }
        auto post = make_unique<FuncCall>("order_history", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  logout API block - SUCCESS case
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
    //  globals & initialisations
    // ═══════════════════════════════════════════════════════════
    vector<unique_ptr<Decl>> globals;
    
    // CUSTOMERS: Map<string, CustomerRecord>
    globals.push_back(make_unique<Decl>(
        "CUSTOMERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CustomerRecord"))));
    
    // PRODUCTS: Map<string, ProductRecord> - populated with sample products
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

    // ORDERS: Map<string, OrderRecord> (orderId -> OrderRecord)
    globals.push_back(make_unique<Decl>(
        "ORDERS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("OrderRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // PRODUCTS initialized with sample products for success scenario
    {
        vector<pair<unique_ptr<Var>, unique_ptr<Expr>>> productEntries;
        
        // Product 1: "laptop" -> product_record("Laptop Computer", 999.99, 10)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Laptop_Computer"));
            productArgs.push_back(make_unique<Var>("999.99"));
            productArgs.push_back(make_unique<Var>("10"));
            productEntries.emplace_back(
                make_unique<Var>("laptop"),
                make_unique<FuncCall>("product_record", move(productArgs))
            );
        }
        
        // Product 2: "mouse" -> product_record("Wireless Mouse", 29.99, 25)
        {
            vector<unique_ptr<Expr>> productArgs;
            productArgs.push_back(make_unique<Var>("Wireless_Mouse"));
            productArgs.push_back(make_unique<Var>("29.99"));
            productArgs.push_back(make_unique<Var>("25"));
            productEntries.emplace_back(
                make_unique<Var>("mouse"),
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

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects for the success flow path ─────── */
Program clientProgram = buildEcommerceSuccessFlowClientProgram();
Spec    spec          = buildEcommerceSuccessFlowSpec();

/*
 * Expected execution flow (COMPLETE SUCCESS SCENARIO):
 * 
 * 1. signup(email, password, fullName) → HTTP 201 CREATED (success)
 *    - Creates new customer account in CUSTOMERS map
 *    - Customer registration succeeds with unique email
 *    - Postcondition: Customer record created with active status
 * 
 * 2. login(email, password) → HTTP 200 OK (success)
 *    - Validates credentials against stored customer data
 *    - Authentication succeeds with correct email/password pair
 *    - Postcondition: login_success(email) confirms authentication
 * 
 * 3. get_products() → HTTP 200 OK (success)
 *    - Returns populated product catalog with available items
 *    - PRODUCTS map contains sample products: laptop, mouse
 *    - Postcondition: products_list(PRODUCTS) shows available inventory
 * 
 * 4. add_to_cart(customerId, productId1, quantity1) → HTTP 200 OK (success)
 *    - Adds first product (laptop) to customer's shopping cart
 *    - Precondition: Customer exists, product exists, quantity > 0
 *    - Postcondition: cart_updated(customerId, productId1, quantity1)
 *    - Updates CARTS map with new item
 * 
 * 5. add_to_cart(customerId, productId2, quantity2) → HTTP 200 OK (success)
 *    - Adds second product (mouse) to customer's shopping cart
 *    - Same preconditions as step 4, different product
 *    - Postcondition: cart_updated(customerId, productId2, quantity2)
 *    - Cart now contains multiple products
 * 
 * 6. view_cart(customerId) → HTTP 200 OK (success)
 *    - Retrieves and displays current cart contents
 *    - Precondition: Customer exists in system
 *    - Postcondition: cart_contents(get_cart(CARTS, customerId))
 *    - Shows both products added in steps 4 and 5
 * 
 * 7. place_order(customerId) → HTTP 201 CREATED (success)
 *    - Converts cart contents into a formal order
 *    - Precondition: Customer exists and cart is not empty
 *    - Postcondition: order_created(customerId, orderId)
 *    - Creates new order record in ORDERS map
 *    - Clears customer's cart after successful order creation
 * 
 * 8. view_orders(customerId) → HTTP 200 OK (success)
 *    - Retrieves customer's order history
 *    - Precondition: Customer exists in system
 *    - Postcondition: order_history(get_orders(ORDERS, customerId))
 *    - Shows the order created in step 7
 * 
 * 9. logout(customerId) → HTTP 200 OK (success)
 *    - Ends customer session gracefully
 *    - Precondition: Customer exists and is logged in
 *    - Postcondition: logout_success(customerId)
 *    - Completes the full e-commerce transaction lifecycle
 * 
 * This complete success scenario demonstrates:
 * - Full user lifecycle: registration → authentication → shopping → ordering
 * - Proper state management across multiple API calls
 * - Successful cart operations with multiple products
 * - Order creation and history tracking
 * - Graceful session termination
 * 
 * The specification ensures all preconditions are met for success:
 * - PRODUCTS map is pre-populated with available inventory
 * - All customer validations pass
 * - Cart operations succeed with valid products
 * - Order creation succeeds with non-empty cart
 * 
 * HTTP status codes follow REST conventions:
 * - 201 CREATED: New resources (signup, place_order)
 * - 200 OK: Successful operations (login, get_products, cart ops, view ops, logout)
 * 
 * This represents the "happy path" through a complete e-commerce workflow,
 * showing how formal specifications can model complex multi-step business processes
 * with proper state transitions and validation at each step.
 */