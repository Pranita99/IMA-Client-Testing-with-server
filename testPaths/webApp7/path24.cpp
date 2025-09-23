#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: admin_login → add_item → update_item → view_menu → logout
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *client* Program AST for admin_login → add_item → update_item → view_menu → logout flow
// ─────────────────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;
    vector<unique_ptr<Decl>> decls;

    // string admin_username;
    decls.push_back(make_unique<Decl>("admin_username",
                     make_unique<TypeConst>("string")));
    // admin_username = input();
    {
        auto lhs = make_unique<Var>("admin_username");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string admin_password;
    decls.push_back(make_unique<Decl>("admin_password",
                     make_unique<TypeConst>("string")));
    // admin_password = input();
    {
        auto lhs = make_unique<Var>("admin_password");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // admin_login(admin_username, admin_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("admin_username"));
        a.push_back(make_unique<Var>("admin_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("admin_login", move(a))));
    }

    // string item_name;
    decls.push_back(make_unique<Decl>("item_name",
                     make_unique<TypeConst>("string")));
    // item_name = input();
    {
        auto lhs = make_unique<Var>("item_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string item_price;
    decls.push_back(make_unique<Decl>("item_price",
                     make_unique<TypeConst>("string")));
    // item_price = input();
    {
        auto lhs = make_unique<Var>("item_price");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string item_description;
    decls.push_back(make_unique<Decl>("item_description",
                     make_unique<TypeConst>("string")));
    // item_description = input();
    {
        auto lhs = make_unique<Var>("item_description");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // add_item(item_name, item_price, item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_name"));
        a.push_back(make_unique<Var>("item_price"));
        a.push_back(make_unique<Var>("item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_item", move(a))));
    }

    // string update_item_id;
    decls.push_back(make_unique<Decl>("update_item_id",
                     make_unique<TypeConst>("string")));
    // update_item_id = input();
    {
        auto lhs = make_unique<Var>("update_item_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string new_item_name;
    decls.push_back(make_unique<Decl>("new_item_name",
                     make_unique<TypeConst>("string")));
    // new_item_name = input();
    {
        auto lhs = make_unique<Var>("new_item_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string new_item_price;
    decls.push_back(make_unique<Decl>("new_item_price",
                     make_unique<TypeConst>("string")));
    // new_item_price = input();
    {
        auto lhs = make_unique<Var>("new_item_price");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string new_item_description;
    decls.push_back(make_unique<Decl>("new_item_description",
                     make_unique<TypeConst>("string")));
    // new_item_description = input();
    {
        auto lhs = make_unique<Var>("new_item_description");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // update_item(update_item_id, new_item_name, new_item_price, new_item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("update_item_id"));
        a.push_back(make_unique<Var>("new_item_name"));
        a.push_back(make_unique<Var>("new_item_price"));
        a.push_back(make_unique<Var>("new_item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("update_item", move(a))));
    }

    // view_menu();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("view_menu", move(a))));
    }

    // logout();
    {
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("logout", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST for admin_login → add_item → update_item → view_menu → logout flow
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Admin Login API block ---
    {
        /* pre: A[admin_u] = admin_p  &&  admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_u"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("admin_p"));
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> notInDom;
            notInDom.push_back(make_unique<Var>("admin_token"));
            {
                vector<unique_ptr<Expr>> h;
                h.push_back(make_unique<Var>("AT"));
                notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
            }
            land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("admin_u"));
        callArgs.push_back(make_unique<Var>("admin_p"));
        auto callFn = make_unique<FuncCall>("admin_login", move(callArgs));

        /* post: AT[admin_token] = admin_u */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("AT"));
            idx.push_back(make_unique<Var>("admin_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("admin_u"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && item_id ∉ dom(M) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
       
        vector<unique_ptr<Expr>> notInDomM;
        notInDomM.push_back(make_unique<Var>("item_id"));
        {
            vector<unique_ptr<Expr>> domM;
            domM.push_back(make_unique<Var>("M"));
            notInDomM.push_back(make_unique<FuncCall>("dom", move(domM)));
        }
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("item_name"));
        callArgs.push_back(make_unique<Var>("item_price"));
        callArgs.push_back(make_unique<Var>("item_description"));
        auto callFn = make_unique<FuncCall>("add_item", move(callArgs));

        /* post: M[item_id] = item_details */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> itemDetails;
            itemDetails.push_back(make_unique<Var>("item_name"));
            itemDetails.push_back(make_unique<Var>("item_price"));
            itemDetails.push_back(make_unique<Var>("item_description"));
            postArgs.push_back(make_unique<FuncCall>("item_record", move(itemDetails)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Update Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && update_item_id ∈ dom(M) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
       
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("M"));
        inDomM.push_back(make_unique<Var>("update_item_id"));
       
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("update_item_id"));
        callArgs.push_back(make_unique<Var>("new_item_name"));
        callArgs.push_back(make_unique<Var>("new_item_price"));
        callArgs.push_back(make_unique<Var>("new_item_description"));
        auto callFn = make_unique<FuncCall>("update_item", move(callArgs));

        /* post: M[update_item_id] = new_item_details */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("update_item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> newItemDetails;
            newItemDetails.push_back(make_unique<Var>("new_item_name"));
            newItemDetails.push_back(make_unique<Var>("new_item_price"));
            newItemDetails.push_back(make_unique<Var>("new_item_description"));
            postArgs.push_back(make_unique<FuncCall>("item_record", move(newItemDetails)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- View Menu API block ---
    {
        /* pre: admin_token ∈ dom(AT) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDomAT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("view_menu", move(callArgs));

        /* post: menu_retrieved = M */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("menu_retrieved"));
        postArgs.push_back(make_unique<Var>("M"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Logout API block ---
    {
        /* pre: admin_token ∈ dom(AT) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
        auto pre = make_unique<FuncCall>("in_dom", move(inDomAT));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        auto callFn = make_unique<FuncCall>("logout", move(callArgs));

        /* post: admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> domAT;
            domAT.push_back(make_unique<Var>("AT"));
            postArgs.push_back(make_unique<FuncCall>("dom", move(domAT)));
        }
        auto post = make_unique<FuncCall>("not_in", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // User credentials map
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Token to user map
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin credentials map
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin token map
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
                  make_unique<TypeConst>("string"),
                  make_unique<TypeConst>("string"))));
    // Restaurant data map
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Menu items map
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Orders map
    globals.push_back(make_unique<Decl>(
        "O", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Cart map (user -> items map)
    globals.push_back(make_unique<Decl>(
        "C", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<MapType>(
                     make_unique<TypeConst>("string"),
                     make_unique<TypeConst>("string")))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "M", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "O", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "C", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();

