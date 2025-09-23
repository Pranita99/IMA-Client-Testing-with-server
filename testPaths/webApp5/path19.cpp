#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for admin and user journey:
//  admin_login → update_product → logout → login → view_products → view_product_details → logout
// ─────────────────────────────────────────────────────────────
static Program buildAdminUserEcommerceClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // Variable declarations
    decls.push_back(make_unique<Decl>("adminEmail", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("adminPassword", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("adminSessionToken", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("email", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("password", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("sessionToken", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productId", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productName", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productPrice", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productDescription", make_unique<TypeConst>("string")));
    decls.push_back(make_unique<Decl>("productStock", make_unique<TypeConst>("string")));

    // ══════════════════════════════════════════════════════════
    //  STEP 1: admin_login(success) - Admin authentication
    // ══════════════════════════════════════════════════════════
    // adminEmail = input(); // admin email
    {
        auto lhs = make_unique<Var>("adminEmail");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // adminPassword = input(); // admin password
    {
        auto lhs = make_unique<Var>("adminPassword");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // adminSessionToken = admin_login(adminEmail, adminPassword); // SUCCESS - returns admin session token
    {
        auto lhs = make_unique<Var>("adminSessionToken");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminEmail"));
        a.push_back(make_unique<Var>("adminPassword"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("admin_login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 2: update_product - Admin updates product information
    // ══════════════════════════════════════════════════════════
    // productId = input(); // product ID to update
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productName = input(); // new product name
    {
        auto lhs = make_unique<Var>("productName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productPrice = input(); // new product price
    {
        auto lhs = make_unique<Var>("productPrice");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productDescription = input(); // new product description
    {
        auto lhs = make_unique<Var>("productDescription");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // productStock = input(); // new product stock
    {
        auto lhs = make_unique<Var>("productStock");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // update_product(adminSessionToken, productId, productName, productPrice, productDescription, productStock); // Update product
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminSessionToken"));
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("productName"));
        a.push_back(make_unique<Var>("productPrice"));
        a.push_back(make_unique<Var>("productDescription"));
        a.push_back(make_unique<Var>("productStock"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("update_product", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 3: logout - Admin ends session
    // ══════════════════════════════════════════════════════════
    // logout(adminSessionToken); // End admin session
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminSessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 4: login(success) - Regular user authentication
    // ══════════════════════════════════════════════════════════
    // email = input(); // user email
    {
        auto lhs = make_unique<Var>("email");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // password = input(); // user password
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // sessionToken = login(email, password); // SUCCESS - returns user session token
    {
        auto lhs = make_unique<Var>("sessionToken");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("email"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("login", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 5: view_products - Browse available products
    // ══════════════════════════════════════════════════════════
    // view_products(sessionToken); // Get list of all products
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_products", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 6: view_product_details - Get details of specific product
    // ══════════════════════════════════════════════════════════
    // productId = input(); // select product ID to view details
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    // view_product_details(sessionToken, productId); // Get detailed product info
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        a.push_back(make_unique<Var>("productId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_product_details", move(a))));
    }

    // ══════════════════════════════════════════════════════════
    //  STEP 7: logout - User ends session
    // ══════════════════════════════════════════════════════════
    // logout(sessionToken); // End user session
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("sessionToken"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Admin-User Ecommerce API *Spec* AST
// ─────────────────────────────────────────────────────────────
static Spec buildAdminUserEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // ═══════════════════════════════════════════════════════════
    //  Admin Login API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: adminEmail ∈ dom(ADMINS) && ADMINS[adminEmail].password = adminPassword */
        vector<unique_ptr<Expr>> emailExists;
        emailExists.push_back(make_unique<Var>("adminEmail"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMINS"));
            emailExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> passwordMatch;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ADMINS"));
            idx.push_back(make_unique<Var>("adminEmail"));
            vector<unique_ptr<Expr>> field;
            field.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            field.push_back(make_unique<Var>("password"));
            passwordMatch.push_back(make_unique<FuncCall>("get_field", move(field)));
        }
        passwordMatch.push_back(make_unique<Var>("adminPassword"));
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        andArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("adminEmail"));
        callArgs.push_back(make_unique<Var>("adminPassword"));
        auto callFn = make_unique<FuncCall>("admin_login", move(callArgs));

        /* post: ADMIN_SESSIONS[adminSessionToken] = {email: adminEmail, loginTime: currentTime, role: "admin"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            idx.push_back(make_unique<Var>("adminSessionToken"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> sessionRecord;
        sessionRecord.push_back(make_unique<Var>("adminEmail"));
        sessionRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        sessionRecord.push_back(make_unique<Var>("admin"));
        postArgs.push_back(make_unique<FuncCall>("admin_session_record", move(sessionRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Update Product API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: adminSessionToken ∈ dom(ADMIN_SESSIONS) && productId ∈ dom(PRODUCTS) */
        vector<unique_ptr<Expr>> sessionExists;
        sessionExists.push_back(make_unique<Var>("adminSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            sessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("adminSessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("productName"));
        callArgs.push_back(make_unique<Var>("productPrice"));
        callArgs.push_back(make_unique<Var>("productDescription"));
        callArgs.push_back(make_unique<Var>("productStock"));
        auto callFn = make_unique<FuncCall>("update_product", move(callArgs));

        /* post: PRODUCTS[productId] = {name: productName, price: productPrice, description: productDescription, stock: productStock, status: "available"} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("PRODUCTS"));
            idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        vector<unique_ptr<Expr>> productRecord;
        productRecord.push_back(make_unique<Var>("productName"));
        productRecord.push_back(make_unique<Var>("productPrice"));
        productRecord.push_back(make_unique<Var>("productDescription"));
        productRecord.push_back(make_unique<Var>("productStock"));
        productRecord.push_back(make_unique<Var>("available"));
        postArgs.push_back(make_unique<FuncCall>("product_record", move(productRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  Logout API block - SUCCESS case (works for both admin and user sessions)
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) || sessionToken ∈ dom(ADMIN_SESSIONS) */
        vector<unique_ptr<Expr>> userSessionExists;
        userSessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            userSessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> adminSessionExists;
        adminSessionExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            adminSessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> orArgs;
        orArgs.push_back(make_unique<FuncCall>("in", move(userSessionExists)));
        orArgs.push_back(make_unique<FuncCall>("in", move(adminSessionExists)));
        auto pre = make_unique<FuncCall>("or_operator", move(orArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("logout", move(callArgs));

        /* post: sessionToken ∉ dom(SESSIONS) && sessionToken ∉ dom(ADMIN_SESSIONS) */
        vector<unique_ptr<Expr>> userSessionNotExists;
        userSessionNotExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            userSessionNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> adminSessionNotExists;
        adminSessionNotExists.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            adminSessionNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> andPostArgs;
        andPostArgs.push_back(make_unique<FuncCall>("not_in", move(userSessionNotExists)));
        andPostArgs.push_back(make_unique<FuncCall>("not_in", move(adminSessionNotExists)));
        auto post = make_unique<FuncCall>("and_operator", move(andPostArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  User Login API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: email ∈ dom(CUSTOMERS) && CUSTOMERS[email].password = password */
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
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        andArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

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
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  View Products API block - SUCCESS case
    // ═══════════════════════════════════════════════════════════
    {
        /* pre: sessionToken ∈ dom(SESSIONS) */
        vector<unique_ptr<Expr>> pArgs;
        pArgs.push_back(make_unique<Var>("sessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("SESSIONS"));
            pArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(pArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        auto callFn = make_unique<FuncCall>("view_products", move(callArgs));

        /* post: return_products(PRODUCTS) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("PRODUCTS"));
        auto post = make_unique<FuncCall>("return_products", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
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
        
        vector<unique_ptr<Expr>> andArgs;
        andArgs.push_back(make_unique<FuncCall>("in", move(sessionExists)));
        andArgs.push_back(make_unique<FuncCall>("in", move(productExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(andArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("sessionToken"));
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("view_product_details", move(callArgs));

        /* post: return_product_details(PRODUCTS[productId]) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("PRODUCTS"));
            idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        auto post = make_unique<FuncCall>("return_product_details", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // ═══════════════════════════════════════════════════════════
    //  globals & initialisations
    // ═══════════════════════════════════════════════════════════
    vector<unique_ptr<Decl>> globals;
    // ADMINS: Map<string, AdminRecord>
    globals.push_back(make_unique<Decl>(
        "ADMINS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("AdminRecord"))));
    // ADMIN_SESSIONS: Map<string, AdminSessionRecord>
    globals.push_back(make_unique<Decl>(
        "ADMIN_SESSIONS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("AdminSessionRecord"))));
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

    vector<unique_ptr<Init>> inits;
    
    // Initialize ADMINS with default admin
    {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> adminEntries;
        
        vector<unique_ptr<Expr>> adminRecord;
        adminRecord.push_back(make_unique<Var>("admin123"));
        adminRecord.push_back(make_unique<Var>("Administrator"));
        adminRecord.push_back(make_unique<Var>("active"));
        
        adminEntries.push_back(make_pair(
            make_unique<Var>("admin@ecommerce.com"),
            make_unique<FuncCall>("admin_record", move(adminRecord))
        ));
        
        inits.push_back(make_unique<Init>(
            "ADMINS", make_unique<Map>(move(adminEntries))));
    }
    
    inits.push_back(make_unique<Init>(
        "ADMIN_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize CUSTOMERS with sample user
    {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> customerEntries;
        
        vector<unique_ptr<Expr>> customerRecord;
        customerRecord.push_back(make_unique<Var>("user123"));
        customerRecord.push_back(make_unique<Var>("John_Doe"));
        customerRecord.push_back(make_unique<Var>("active"));
        
        customerEntries.push_back(make_pair(
            make_unique<Var>("user@example.com"),
            make_unique<FuncCall>("customer_record", move(customerRecord))
        ));
        
        inits.push_back(make_unique<Init>(
            "CUSTOMERS", make_unique<Map>(move(customerEntries))));
    }
    
    inits.push_back(make_unique<Init>(
        "SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize PRODUCTS with sample data
    {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> productEntries;
        
        // Product 1: Laptop
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Gaming_Laptop"));
            productRecord.push_back(make_unique<Var>("1299.99"));
            productRecord.push_back(make_unique<Var>("High_performance_gaming_laptop"));
            productRecord.push_back(make_unique<Var>("50"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD001"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        // Product 2: Smartphone
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Smartphone_Pro"));
            productRecord.push_back(make_unique<Var>("899.99"));
            productRecord.push_back(make_unique<Var>("Latest_flagship_smartphone"));
            productRecord.push_back(make_unique<Var>("100"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD002"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        // Product 3: Headphones
        {
            vector<unique_ptr<Expr>> productRecord;
            productRecord.push_back(make_unique<Var>("Wireless_Headphones"));
            productRecord.push_back(make_unique<Var>("299.99"));
            productRecord.push_back(make_unique<Var>("Premium_noise_cancelling_headphones"));
            productRecord.push_back(make_unique<Var>("75"));
            productRecord.push_back(make_unique<Var>("available"));
            
            productEntries.push_back(make_pair(
                make_unique<Var>("PROD003"),
                make_unique<FuncCall>("product_record", move(productRecord))
            ));
        }
        
        inits.push_back(make_unique<Init>(
            "PRODUCTS", make_unique<Map>(move(productEntries))));
    }

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildAdminUserEcommerceClientProgram();
Spec    spec          = buildAdminUserEcommerceSpec();