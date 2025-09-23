#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: admin_login → create_restaurant → add_menu_item → update_menu_item
// ─────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────
//  Build the *admin* Program AST for restaurant management
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

    // string restaurant_name;
    decls.push_back(make_unique<Decl>("restaurant_name",
                     make_unique<TypeConst>("string")));
    // restaurant_name = input();
    {
        auto lhs = make_unique<Var>("restaurant_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string restaurant_address;
    decls.push_back(make_unique<Decl>("restaurant_address",
                     make_unique<TypeConst>("string")));
    // restaurant_address = input();
    {
        auto lhs = make_unique<Var>("restaurant_address");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string restaurant_cuisine;
    decls.push_back(make_unique<Decl>("restaurant_cuisine",
                     make_unique<TypeConst>("string")));
    // restaurant_cuisine = input();
    {
        auto lhs = make_unique<Var>("restaurant_cuisine");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // create_restaurant(restaurant_name, restaurant_address, restaurant_cuisine);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_name"));
        a.push_back(make_unique<Var>("restaurant_address"));
        a.push_back(make_unique<Var>("restaurant_cuisine"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("create_restaurant", move(a))));
    }

    // string restaurant_id;
    decls.push_back(make_unique<Decl>("restaurant_id",
                     make_unique<TypeConst>("string")));
    // restaurant_id = input();
    {
        auto lhs = make_unique<Var>("restaurant_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
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

    // add_menu_item(restaurant_id, item_name, item_description, item_price);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("item_name"));
        a.push_back(make_unique<Var>("item_description"));
        a.push_back(make_unique<Var>("item_price"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_menu_item", move(a))));
    }

    // string menu_item_id;
    decls.push_back(make_unique<Decl>("menu_item_id",
                     make_unique<TypeConst>("string")));
    // menu_item_id = input();
    {
        auto lhs = make_unique<Var>("menu_item_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string updated_item_name;
    decls.push_back(make_unique<Decl>("updated_item_name",
                     make_unique<TypeConst>("string")));
    // updated_item_name = input();
    {
        auto lhs = make_unique<Var>("updated_item_name");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string updated_item_description;
    decls.push_back(make_unique<Decl>("updated_item_description",
                     make_unique<TypeConst>("string")));
    // updated_item_description = input();
    {
        auto lhs = make_unique<Var>("updated_item_description");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // string updated_item_price;
    decls.push_back(make_unique<Decl>("updated_item_price",
                     make_unique<TypeConst>("string")));
    // updated_item_price = input();
    {
        auto lhs = make_unique<Var>("updated_item_price");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // update_menu_item(menu_item_id, updated_item_name, updated_item_description, updated_item_price);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("menu_item_id"));
        a.push_back(make_unique<Var>("updated_item_name"));
        a.push_back(make_unique<Var>("updated_item_description"));
        a.push_back(make_unique<Var>("updated_item_price"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("update_menu_item", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with admin restaurant management functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Admin Login API block ---
    {
        /* pre: A[admin_username] = admin_password && admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_username"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        eq.push_back(make_unique<Var>("admin_password"));
        
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
        callArgs.push_back(make_unique<Var>("admin_username"));
        callArgs.push_back(make_unique<Var>("admin_password"));
        auto callFn = make_unique<FuncCall>("admin_login", move(callArgs));

        /* post: AT[admin_token] = admin_username */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("AT"));
            idx.push_back(make_unique<Var>("admin_token"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        postArgs.push_back(make_unique<Var>("admin_username"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Create Restaurant API block ---
    {
        /* pre: admin_token ∈ dom(AT) && restaurant_id ∉ dom(R) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
        
        vector<unique_ptr<Expr>> notInDomR;
        notInDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            notInDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_name"));
        callArgs.push_back(make_unique<Var>("restaurant_address"));
        callArgs.push_back(make_unique<Var>("restaurant_cuisine"));
        auto callFn = make_unique<FuncCall>("create_restaurant", move(callArgs));

        /* post: R[restaurant_id] = RestaurantRecord(name, address, cuisine) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("R"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            recordArgs.push_back(make_unique<Var>("restaurant_name"));
            recordArgs.push_back(make_unique<Var>("restaurant_address"));
            recordArgs.push_back(make_unique<Var>("restaurant_cuisine"));
            postArgs.push_back(make_unique<FuncCall>("restaurant_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Add Menu Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && restaurant_id ∈ dom(R) && menu_item_id ∉ dom(M) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
        
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("R"));
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        
        vector<unique_ptr<Expr>> notInDomM;
        notInDomM.push_back(make_unique<Var>("menu_item_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("M"));
            notInDomM.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomR)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        callArgs.push_back(make_unique<Var>("item_name"));
        callArgs.push_back(make_unique<Var>("item_description"));
        callArgs.push_back(make_unique<Var>("item_price"));
        auto callFn = make_unique<FuncCall>("add_menu_item", move(callArgs));

        /* post: M[menu_item_id] = MenuItemRecord(restaurant_id, name, description, price) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("menu_item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            recordArgs.push_back(make_unique<Var>("restaurant_id"));
            recordArgs.push_back(make_unique<Var>("item_name"));
            recordArgs.push_back(make_unique<Var>("item_description"));
            recordArgs.push_back(make_unique<Var>("item_price"));
            postArgs.push_back(make_unique<FuncCall>("menu_item_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Update Menu Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && menu_item_id ∈ dom(M) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("AT"));
        inDomAT.push_back(make_unique<Var>("admin_token"));
        
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("M"));
        inDomM.push_back(make_unique<Var>("menu_item_id"));
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in_dom", move(inDomM)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("menu_item_id"));
        callArgs.push_back(make_unique<Var>("updated_item_name"));
        callArgs.push_back(make_unique<Var>("updated_item_description"));
        callArgs.push_back(make_unique<Var>("updated_item_price"));
        auto callFn = make_unique<FuncCall>("update_menu_item", move(callArgs));

        /* post: M[menu_item_id] = MenuItemRecord(existing_restaurant_id, updated_name, updated_description, updated_price) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("menu_item_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
            // Keep existing restaurant_id from the original record
            {
                vector<unique_ptr<Expr>> origRecord;
                origRecord.push_back(make_unique<Var>("M"));
                origRecord.push_back(make_unique<Var>("menu_item_id"));
                vector<unique_ptr<Expr>> fieldAccess;
                fieldAccess.push_back(make_unique<FuncCall>("mapped_value", move(origRecord)));
                fieldAccess.push_back(make_unique<Var>("restaurant_id"));
                recordArgs.push_back(make_unique<FuncCall>("field_access", move(fieldAccess)));
            }
            recordArgs.push_back(make_unique<Var>("updated_item_name"));
            recordArgs.push_back(make_unique<Var>("updated_item_description"));
            recordArgs.push_back(make_unique<Var>("updated_item_price"));
            postArgs.push_back(make_unique<FuncCall>("menu_item_record", move(recordArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- globals & initialisations ---
    vector<unique_ptr<Decl>> globals;
    // Admin credentials map
    globals.push_back(make_unique<Decl>(
        "A", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Admin token to admin username map
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("RestaurantRecord"))));
    // Menu items map
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("MenuItemRecord"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "A", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "AT", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "R", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "M", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apiBlocks));
}

/* ── globals the driver expects ───────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();