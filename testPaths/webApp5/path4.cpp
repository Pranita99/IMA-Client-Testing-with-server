#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  Build the *admin client* Program AST for login → add product → view product → logout
// ─────────────────────────────────────────────────────────────
static Program buildAdminClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string adminEmail;
    decls.push_back(make_unique<Decl>("adminEmail",
                     make_unique<TypeConst>("string")));
    // adminEmail = input();
    {
        auto lhs = make_unique<Var>("adminEmail");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string adminPassword;
    decls.push_back(make_unique<Decl>("adminPassword",
                     make_unique<TypeConst>("string")));
    // adminPassword = input();
    {
        auto lhs = make_unique<Var>("adminPassword");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // admin_login(adminEmail, adminPassword);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("adminEmail"));
        a.push_back(make_unique<Var>("adminPassword"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("admin_login", move(a))));
    }

    // string productId;
    decls.push_back(make_unique<Decl>("productId",
                     make_unique<TypeConst>("string")));
    // productId = input();
    {
        auto lhs = make_unique<Var>("productId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string productName;
    decls.push_back(make_unique<Decl>("productName",
                     make_unique<TypeConst>("string")));
    // productName = input();
    {
        auto lhs = make_unique<Var>("productName");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string productPrice;
    decls.push_back(make_unique<Decl>("productPrice",
                     make_unique<TypeConst>("string")));
    // productPrice = input();
    {
        auto lhs = make_unique<Var>("productPrice");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string productCategory;
    decls.push_back(make_unique<Decl>("productCategory",
                     make_unique<TypeConst>("string")));
    // productCategory = input();
    {
        auto lhs = make_unique<Var>("productCategory");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_product(productId, productName, productPrice, productCategory);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("productId"));
        a.push_back(make_unique<Var>("productName"));
        a.push_back(make_unique<Var>("productPrice"));
        a.push_back(make_unique<Var>("productCategory"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_product", move(a))));
    }

    // string viewProductId;
    decls.push_back(make_unique<Decl>("viewProductId",
                     make_unique<TypeConst>("string")));
    // viewProductId = input();
    {
        auto lhs = make_unique<Var>("viewProductId");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // view_product(viewProductId);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("viewProductId"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_product", move(a))));
    }
    
    // admin_logout();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("admin_logout", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the Admin Ecommerce API *Spec* AST with admin_login/add_product/view_product/admin_logout functionality
// ─────────────────────────────────────────────────────────────
static Spec buildAdminEcommerceSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Admin Login API block ---
    {
        /* pre: adminEmail ∈ dom(ADMINS) && ADMINS[adminEmail].password = adminPassword && adminSessionToken ∉ dom(ADMIN_SESSIONS) */
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
        
        vector<unique_ptr<Expr>> sessionNotExists;
        sessionNotExists.push_back(make_unique<Var>("adminSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            sessionNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("in", move(emailExists)));
        landArgs.push_back(make_unique<FuncCall>("equals", move(passwordMatch)));
        landArgs.push_back(make_unique<FuncCall>("not_in", move(sessionNotExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

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
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add Product API block ---
    {
        /* pre: productId ∉ dom(PRODUCTS) && adminSessionToken ∈ dom(ADMIN_SESSIONS) */
        vector<unique_ptr<Expr>> productNotExists;
        productNotExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productNotExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> adminSessionExists;
        adminSessionExists.push_back(make_unique<Var>("adminSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            adminSessionExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> landArgs;
        landArgs.push_back(make_unique<FuncCall>("not_in", move(productNotExists)));
        landArgs.push_back(make_unique<FuncCall>("in", move(adminSessionExists)));
        auto pre = make_unique<FuncCall>("and_operator", move(landArgs));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("productId"));
        callArgs.push_back(make_unique<Var>("productName"));
        callArgs.push_back(make_unique<Var>("productPrice"));
        callArgs.push_back(make_unique<Var>("productCategory"));
        auto callFn = make_unique<FuncCall>("add_product", move(callArgs));

        /* post: PRODUCTS[productId] = {name: productName, price: productPrice, category: productCategory, status: "active", createdTime: currentTime} */
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
        productRecord.push_back(make_unique<Var>("productCategory"));
        productRecord.push_back(make_unique<Var>("active"));
        productRecord.push_back(make_unique<FuncCall>("current_time", vector<unique_ptr<Expr>>()));
        postArgs.push_back(make_unique<FuncCall>("product_record", move(productRecord)));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- View Product API block ---
    {
        /* pre: productId ∈ dom(PRODUCTS) */
        vector<unique_ptr<Expr>> productExists;
        productExists.push_back(make_unique<Var>("productId"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("PRODUCTS"));
            productExists.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(productExists));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("productId"));
        auto callFn = make_unique<FuncCall>("view_product", move(callArgs));

        /* post: return PRODUCTS[productId] (product details remain unchanged) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("PRODUCTS"));
            idx.push_back(make_unique<Var>("productId"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("returned_product_data"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Admin Logout API block ---
    {
        /* pre: adminSessionToken ∈ dom(ADMIN_SESSIONS) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("adminSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            inDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDom));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("admin_logout", move(callArgs));

        /* post: adminSessionToken ∉ dom(ADMIN_SESSIONS) */
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("adminSessionToken"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ADMIN_SESSIONS"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto post = make_unique<FuncCall>("not_in", move(notInDom));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
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
    // PRODUCTS: Map<string, ProductRecord>
    globals.push_back(make_unique<Decl>(
        "PRODUCTS", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("ProductRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "ADMINS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "ADMIN_SESSIONS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "PRODUCTS", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildAdminClientProgram();
Spec    spec          = buildAdminEcommerceSpec();