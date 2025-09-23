#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for login(success) → browse_products → view_product_details
// ─────────────────────────────────────────────────────────────
static Program buildEcommerceBrowseClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string email;
    decls.push_back(make_unique<Decl>("email",
                     make_unique<TypeConst>("string")));
    // string password;
    decls.push_back(make_unique<Decl>("password",
                     make_unique<TypeConst>("string")));
    // string category;
    decls.push_back(make_unique<Decl>("category",
                     make_unique<TypeConst>("string")));
    // string productId;
    decls.push_back(make_unique<Decl>("productId",
                     make_unique<TypeConst>("string")));
    // string sessionToken;
    decls.push_back(make_unique<Decl>("sessionToken",
                     make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: login(success) - Login with correct credentials
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
    //  STEP 2: browse_products - Browse products by category
    // ══════════════════════════════════════════════════════════
    // sessionToken = input(); // session token from login
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // category = input(); // category to browse (e.g., "electronics", "books")
    {
        auto lhs = make_unique<Var>("category");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // browse_products(sessionToken, category); // Browse products in category
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("category"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("browse_products", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: view_product_details - View details of specific product
    // ══════════════════════════════════════════════════════════
    // sessionToken = input(); // session token
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productId = input(); // product ID to view details
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_product_details(sessionToken, productId); // View product details
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("productId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_product_details", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Ecommerce API *Spec* AST with login/browse/view functionality
//  Including SUCCESS cases for the browsing flow
// ─────────────────────────────────────────────────────────────
static Spec buildEcommerceBrowseSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Login API block - SUCCESS case (needed for session)
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

        /* post: SESSIONS[sessionToken] = {email: email, loginTime: currentTime} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("SESSIONS"));
            idx.push_back(make_unique<Var>("sessionToken"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> sessionRecord;
        sessionRecord.push_back(make_unique<Var>("email"));
        sessionRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        postArgs.push_back(make_unique<FuncCall>("session_record", move(sessionRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Browse Products API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && category ∈ dom(PRODUCT_CATEGORIES) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> categoryExists;
        categoryExists.push_back(make_unique<Var>("category"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCT_CATEGORIES"));
            categoryExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(categoryExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("category"));
        auto callFn = make_unique<FuncCall>("browse_products", move(callArgs));

        /* post: return product_list(filter_by_category(PRODUCTS, category)) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> filterArgs;
            filterArgs.push_back(make_unique<Var>("PRODUCTS"));
            filterArgs.push_back(make_unique<Var>("category"));
            postArgs.push_back(make_unique<FuncCall>("filter_by_category", move(filterArgs)));
        }
        auto post = make_unique<FuncCall>("product_list", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Browse Products API block - FAILURE case (invalid session)
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
        callArgs.push_back(make_unique<Var>("category"));
        auto callFn = make_unique<FuncCall>("browse_products", move(callArgs));

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
    //  View Product Details API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) && productId ∈ dom(PRODUCTS) */
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
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("view_product_details", move(callArgs));

        /* post: return PRODUCTS[productId] with view_count incremented */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("PRODUCTS"));
            idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> incrementArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("PRODUCTS"));
                idx.push_back(make_unique<Var>("productId"));
                vector<unique_ptr<Expr>> field;
                field.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
                field.push_back(make_unique<Var>("view_count"));
                incrementArgs.push_back(make_unique<FuncCall>("get_field", move(field)));
            }
            incrementArgs.push_back(make_unique<Var>("1"));
            postArgs.push_back(make_unique<FuncCall>("increment_view_count", move(incrementArgs)));
        }
        auto post = make_unique<FuncCall>("product_details_with_increment", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Product Details API block - FAILURE case (product not found)
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
        auto callFn = make_unique<FuncCall>("view_product_details", move(callArgs));

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
    // PRODUCT_CATEGORIES: Map<string, CategoryRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCT_CATEGORIES", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("CategoryRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "CUSTOMERS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize with some sample products
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productsData;
    // PRODUCTS["prod1"] = {name: "Laptop", category: "electronics", price: 999, view_count: 0}
    {
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("Laptop"));
        productRecord.push_back(make_unique<Var>("electronics"));
        productRecord.push_back(make_unique<Var>("999"));
        productRecord.push_back(make_unique<Var>("0"));
        productsData.push_back(make_pair(
            make_unique<Var>("prod1"),
            make_unique<FuncCall>("product_record", move(productRecord))
        ));
    }
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(move(productsData))));
    
    // Initialize with some sample categories
    vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> categoriesData;
    // PRODUCT_CATEGORIES["electronics"] = {name: "Electronics", description: "Electronic devices"}
    {
        vector<unique_ptr<Expr>> categoryRecord;
        categoryRecord.push_back(make_unique<Var>("Electronics"));
        categoryRecord.push_back(make_unique<Var>("Electronic_devices"));
        categoriesData.push_back(make_pair(
            make_unique<Var>("electronics"),
            make_unique<FuncCall>("category_record", move(categoryRecord))
        ));
    }
    inits.push_back(make_unique<Init>(
        "PRODUCT_CATEGORIES", make_unique<Map>(move(categoriesData))));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildEcommerceBrowseClientProgram();
Spec    spec          = buildEcommerceBrowseSpec();