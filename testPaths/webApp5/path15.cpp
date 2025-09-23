#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for login → add_to_cart(product1) → view_cart → success
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceCartClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string email;
    decls.push_back(make_unique<Decl>("email",
                     make_unique<TypeConst>("string")));
    // string password;
    decls.push_back(make_unique<Decl>("password",
                     make_unique<TypeConst>("string")));
    // string sessionToken;
    decls.push_back(make_unique<Decl>("sessionToken",
                     make_unique<TypeConst>("string")));
    // string productId;
    decls.push_back(make_unique<Decl>("productId",
                     make_unique<TypeConst>("string")));
    // string quantity;
    decls.push_back(make_unique<Decl>("quantity",
                     make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: login - Login with correct credentials
    // ══════════════════════════════════════════════════════════
    // email = input(); // correct email
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
    //  STEP 2: add_to_cart(product1) - Add product1 to cart
    // ══════════════════════════════════════════════════════════
    // sessionToken = input(); // session token from login
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId = input(); // product1 ID
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("product1"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // quantity = input(); // quantity to add (e.g., "1")
    {
        auto lhs = make_unique<Var>("quantity");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("1"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // add_to_cart(sessionToken, productId, quantity); // Add product1 to cart
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("quantity"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: view_cart - View current cart contents
    // ══════════════════════════════════════════════════════════
    // sessionToken = input(); // session token
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_cart(sessionToken); // View cart contents - should show product1
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_cart", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST with login/cart functionality
//  Including SUCCESS cases for the cart flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceCartSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Login API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: email ∈ dom(CUSTOMERS) && CUSTOMERS[email].password = password && sessionToken ∉ dom(SESSIONS) */
        vector<unique_ptr<Expr>> emailExists;
        emailExists.push_back(make_unique<Var>("email"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CUSTOMERS"));
            emailExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CUSTOMERS"));
            idx.push_back(make_unique<Var>("email"));
            vector<unique_ptr<Expr>> field;
            field.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            field.push_back(make_unique<Var>("password"));
            passwordMatch.push_back(make_unique<FuncCall>("get_field", move(field)));
        }
        passwordMatch.push_back(make_unique<Var>("password"));
        
        vector<unique_ptr<Expr>> sessionNotExists;
        sessionNotExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        landArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        landArgs.push_back(make_unique<FuncCall>("not_in", move(sessionNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("email"));
        callArgs.push_back(make_unique<Var>("password"));
        auto callFn = make_unique<FuncCall>("login", move(callArgs));

        /* post: SESSIONS[sessionToken] = {email: email, loginTime: currentTime} && CARTS[sessionToken] = {} */
        vector<unique_ptr<Expr>> sessionPostArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("SESSIONS"));
            idx.push_back(make_unique<Var>("sessionToken"));
            sessionPostArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> sessionRecord;
        sessionRecord.push_back(make_unique<Var>("email"));
        sessionRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        sessionPostArgs.push_back(make_unique<FuncCall>("session_record", move(sessionRecord)));
        
        vector<unique_ptr<Expr>> cartPostArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("sessionToken"));
            cartPostArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        cartPostArgs.push_back(make_unique<FuncCall>("empty_cart", vector<unique_ptr<Expr>>()));
        
        vector<unique_ptr<Expr>> postAndArgs;
        postAndArgs.push_back(make_unique<FuncCall>("equals", move(sessionPostArgs)));
        postAndArgs.push_back(make_unique<FuncCall>("equals", move(cartPostArgs)));
        auto post = make_unique<FuncCall>("and_operator", move(postAndArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Add to Cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∈ dom(PRODUCTS) && quantity > 0 */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> quantityValid;
        quantityValid.push_back(make_unique<Var>("quantity"));
        quantityValid.push_back(make_unique<Var>("0"));
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        landArgs.push_back(make_unique<FuncCall>("greater_than", move(quantityValid)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: CARTS[sessionToken][productId] = {quantity: quantity, addedTime: currentTime} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> cartIdx;
            cartIdx.push_back(make_unique<Var>("CARTS"));
            cartIdx.push_back(make_unique<Var>("sessionToken"));
            vector<unique_ptr<Expr>> productIdx;
            productIdx.push_back(make_unique<FuncCall>("mapped_value", move(cartIdx)));
            productIdx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(productIdx)));
        }
        vector<unique_ptr<Expr>> cartItemRecord;
        cartItemRecord.push_back(make_unique<Var>("quantity"));
        cartItemRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        postArgs.push_back(make_unique<FuncCall>("cart_item_record", move(cartItemRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Add to Cart API block - FAILURE case (invalid session)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∉ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: error("Invalid session") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Invalid_session"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::UNAUTHORIZED_401, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Add to Cart API block - FAILURE case (product not found)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∉ dom(PRODUCTS) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productNotExists;
        productNotExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("not_in", move(productNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(callArgs));

        /* post: error("Product not found") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Product_not_found"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::NOT_FOUND_404, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Cart API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && sessionToken ∈ dom(CARTS) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> cartExists;
        cartExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CARTS"));
            cartExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(cartExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: return cart_contents(CARTS[sessionToken]) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("CARTS"));
            idx.push_back(make_unique<Var>("sessionToken"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        auto post = make_unique<FuncCall>("cart_contents", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Cart API block - FAILURE case (invalid session)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∉ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_cart", move(callArgs));

        /* post: error("Invalid session") */
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("Invalid_session"));
        auto post = make_unique<FuncCall>("error", move(errorArgs));

        Response resp(HTTPResponseCode::UNAUTHORIZED_401, post->clone());
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
    // SESSIONS: Map<string, SessionRecord>
    globals.push_back(make_unique<Decl>(
        "SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("SessionRecord"))));
    // PRODUCTS: Map<string, ProductRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));
    // CARTS: Map<string, Map<string, CartItemRecord>>
    globals.push_back(make_unique<Decl>(
        "CARTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("CartItemRecord")))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize with sample products including product1
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productsData;
    // PRODUCTS["product1"] = {name: "Laptop", category: "electronics", price: 999, stock: 10}
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Laptop"));
        productRecord.push_back(make_unique<Var>("electronics"));
        productRecord.push_back(make_unique<Var>("999"));
        productRecord.push_back(make_unique<Var>("10"));
        productsData.push_back(make_pair(
            make_unique<Var>("product1"),
            make_unique<FuncCall>("product_record", move(productRecord))
        ));
    }
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(move(productsData))));
    
    inits.push_back(make_unique<Init>(
        "CARTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildEcommerceCartClientProgram();
Spec    spec          = buildEcommerceCartSpec();