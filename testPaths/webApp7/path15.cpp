#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ─────────────────────────────────────────────────────────────
//  PATH: admin_login → create_restaurant → add_menu_item → get_menu → delete_menu_item → add_menu_item → update_menu_item
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

    // add_menu_item(restaurant_id, item_name, item_price, item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("item_name"));
        a.push_back(make_unique<Var>("item_price"));
        a.push_back(make_unique<Var>("item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_menu_item", move(a))));
    }

    // get_menu(restaurant_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("get_menu", move(a))));
    }

    // string item_id_to_delete;
    decls.push_back(make_unique<Decl>("item_id_to_delete",
                     make_unique<TypeConst>("string")));
    // item_id_to_delete = input();
    {
        auto lhs = make_unique<Var>("item_id_to_delete");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }

    // delete_menu_item(restaurant_id, item_id_to_delete);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("item_id_to_delete"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("delete_menu_item", move(a))));
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

    // add_menu_item(restaurant_id, new_item_name, new_item_price, new_item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("new_item_name"));
        a.push_back(make_unique<Var>("new_item_price"));
        a.push_back(make_unique<Var>("new_item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("add_menu_item", move(a))));
    }

    // string item_id_to_update;
    decls.push_back(make_unique<Decl>("item_id_to_update",
                     make_unique<TypeConst>("string")));
    // item_id_to_update = input();
    {
        auto lhs = make_unique<Var>("item_id_to_update");
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

    // update_menu_item(restaurant_id, item_id_to_update, updated_item_name, updated_item_price, updated_item_description);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("restaurant_id"));
        a.push_back(make_unique<Var>("item_id_to_update"));
        a.push_back(make_unique<Var>("updated_item_name"));
        a.push_back(make_unique<Var>("updated_item_price"));
        a.push_back(make_unique<Var>("updated_item_description"));
        stmts.push_back(make_unique<FuncCallStmt>(
              make_unique<FuncCall>("update_menu_item", move(a))));
    }

    return Program(std::move(stmts));
}

// ─────────────────────────────────────────────────────────────
//  Build the API *Spec* AST with restaurant management functionality
// ─────────────────────────────────────────────────────────────
static Spec buildSpec()
{
    vector<unique_ptr<API>> apiBlocks;

    // --- Admin Login API block ---
    {
        /* pre: admin_username ∈ dom(A) && A[admin_username].password = admin_password && admin_token ∉ dom(AT) */
        vector<unique_ptr<Expr>> inDom;
        inDom.push_back(make_unique<Var>("admin_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("A"));
            inDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> eq;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("A"));
            idx.push_back(make_unique<Var>("admin_username"));
            auto adminRecord = make_unique<FuncCall>("mapped_value", move(idx));
            
            vector<unique_ptr<Expr>> passwordAccess;
            passwordAccess.push_back(move(adminRecord));
            passwordAccess.push_back(make_unique<Var>("password"));
            eq.push_back(make_unique<FuncCall>("field_access", move(passwordAccess)));
        }
        eq.push_back(make_unique<Var>("admin_password"));
        
        vector<unique_ptr<Expr>> notInDom;
        notInDom.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            notInDom.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDom)));
        land.push_back(make_unique<FuncCall>("equals", move(eq)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDom)));
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
        /* pre: admin_token ∈ dom(AT) && restaurant_name ∉ dom(R) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> notInDomR;
        notInDomR.push_back(make_unique<Var>("restaurant_name"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            notInDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("not_in", move(notInDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_name"));
        callArgs.push_back(make_unique<Var>("restaurant_address"));
        callArgs.push_back(make_unique<Var>("restaurant_cuisine"));
        auto callFn = make_unique<FuncCall>("create_restaurant", move(callArgs));

        /* post: R[restaurant_name] = RestaurantRecord(restaurant_address, restaurant_cuisine) */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("R"));
            idx.push_back(make_unique<Var>("restaurant_name"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> recordArgs;
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
        /* pre: admin_token ∈ dom(AT) && restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            inDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomR)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        callArgs.push_back(make_unique<Var>("item_name"));
        callArgs.push_back(make_unique<Var>("item_price"));
        callArgs.push_back(make_unique<Var>("item_description"));
        auto callFn = make_unique<FuncCall>("add_menu_item", move(callArgs));

        /* post: M[restaurant_id] = M[restaurant_id] ∪ {MenuItem(item_name, item_price, item_description)} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> unionArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("M"));
                idx.push_back(make_unique<Var>("restaurant_id"));
                unionArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            {
                vector<unique_ptr<Expr>> itemArgs;
                itemArgs.push_back(make_unique<Var>("item_name"));
                itemArgs.push_back(make_unique<Var>("item_price"));
                itemArgs.push_back(make_unique<Var>("item_description"));
                auto menuItem = make_unique<FuncCall>("menu_item", move(itemArgs));
                
                vector<unique_ptr<Expr>> setArgs;
                setArgs.push_back(move(menuItem));
                unionArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
            }
            postArgs.push_back(make_unique<FuncCall>("union", move(unionArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Get Menu API block ---
    {
        /* pre: restaurant_id ∈ dom(R) */
        vector<unique_ptr<Expr>> inDomR;
        inDomR.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("R"));
            inDomR.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(inDomR));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        auto callFn = make_unique<FuncCall>("get_menu", move(callArgs));

        /* post: menu_items = if restaurant_id ∈ dom(M) then M[restaurant_id] else [] */
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("menu_items"));
        
        // Build conditional expression: if restaurant_id ∈ dom(M) then M[restaurant_id] else []
        {
            // Condition: restaurant_id ∈ dom(M)
            vector<unique_ptr<Expr>> condArgs;
            condArgs.push_back(make_unique<Var>("restaurant_id"));
            {
                vector<unique_ptr<Expr>> domM;
                domM.push_back(make_unique<Var>("M"));
                condArgs.push_back(make_unique<FuncCall>("dom", move(domM)));
            }
            auto condition = make_unique<FuncCall>("in", move(condArgs));
            
            // Then branch: M[restaurant_id]
            vector<unique_ptr<Expr>> thenArgs;
            thenArgs.push_back(make_unique<Var>("M"));
            thenArgs.push_back(make_unique<Var>("restaurant_id"));
            auto thenBranch = make_unique<FuncCall>("mapped_value", move(thenArgs));
            
            // Else branch: empty list []
            auto elseBranch = make_unique<FuncCall>("empty_list", vector<unique_ptr<Expr>>());
            
            // Build conditional
            vector<unique_ptr<Expr>> ifArgs;
            ifArgs.push_back(move(condition));
            ifArgs.push_back(move(thenBranch));
            ifArgs.push_back(move(elseBranch));
            postArgs.push_back(make_unique<FuncCall>("if_then_else", move(ifArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Delete Menu Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && restaurant_id ∈ dom(M) && item_id_to_delete ∈ M[restaurant_id] */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("M"));
            inDomM.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> itemInMenu;
        itemInMenu.push_back(make_unique<Var>("item_id_to_delete"));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            itemInMenu.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomM)));
        land.push_back(make_unique<FuncCall>("in", move(itemInMenu)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        callArgs.push_back(make_unique<Var>("item_id_to_delete"));
        auto callFn = make_unique<FuncCall>("delete_menu_item", move(callArgs));

        /* post: M[restaurant_id] = M[restaurant_id] \ {item_id_to_delete} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> diffArgs;
            {
                vector<unique_ptr<Expr>> idx;
                idx.push_back(make_unique<Var>("M"));
                idx.push_back(make_unique<Var>("restaurant_id"));
                diffArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
            }
            {
                vector<unique_ptr<Expr>> setArgs;
                setArgs.push_back(make_unique<Var>("item_id_to_delete"));
                diffArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
            }
            postArgs.push_back(make_unique<FuncCall>("difference", move(diffArgs)));
        }
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apiBlocks.push_back(
            make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

    // --- Update Menu Item API block ---
    {
        /* pre: admin_token ∈ dom(AT) && restaurant_id ∈ dom(M) && item_id_to_update ∈ M[restaurant_id] */
        vector<unique_ptr<Expr>> inDomAT;
        inDomAT.push_back(make_unique<Var>("admin_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("AT"));
            inDomAT.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> inDomM;
        inDomM.push_back(make_unique<Var>("restaurant_id"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("M"));
            inDomM.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        
        vector<unique_ptr<Expr>> itemInMenu;
        itemInMenu.push_back(make_unique<Var>("item_id_to_update"));
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            itemInMenu.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        
        vector<unique_ptr<Expr>> land;
        land.push_back(make_unique<FuncCall>("in", move(inDomAT)));
        land.push_back(make_unique<FuncCall>("in", move(inDomM)));
        land.push_back(make_unique<FuncCall>("in", move(itemInMenu)));
        auto pre = make_unique<FuncCall>("and_operator", move(land));

        /* call */
        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("restaurant_id"));
        callArgs.push_back(make_unique<Var>("item_id_to_update"));
        callArgs.push_back(make_unique<Var>("updated_item_name"));
        callArgs.push_back(make_unique<Var>("updated_item_price"));
        callArgs.push_back(make_unique<Var>("updated_item_description"));
        auto callFn = make_unique<FuncCall>("update_menu_item", move(callArgs));

        /* post: M[restaurant_id] = (M[restaurant_id] \ {item_id_to_update}) ∪ {MenuItem(updated_item_name, updated_item_price, updated_item_description)} */
        vector<unique_ptr<Expr>> postArgs;
        {
            vector<unique_ptr<Expr>> idx;
            idx.push_back(make_unique<Var>("M"));
            idx.push_back(make_unique<Var>("restaurant_id"));
            postArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
        }
        {
            vector<unique_ptr<Expr>> unionArgs;
            {
                // (M[restaurant_id] \ {item_id_to_update})
                vector<unique_ptr<Expr>> diffArgs;
                {
                    vector<unique_ptr<Expr>> idx;
                    idx.push_back(make_unique<Var>("M"));
                    idx.push_back(make_unique<Var>("restaurant_id"));
                    diffArgs.push_back(make_unique<FuncCall>("mapped_value", move(idx)));
                }
                {
                    vector<unique_ptr<Expr>> setArgs;
                    setArgs.push_back(make_unique<Var>("item_id_to_update"));
                    diffArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
                }
                unionArgs.push_back(make_unique<FuncCall>("difference", move(diffArgs)));
            }
            {
                // {MenuItem(updated_item_name, updated_item_price, updated_item_description)}
                vector<unique_ptr<Expr>> itemArgs;
                itemArgs.push_back(make_unique<Var>("updated_item_name"));
                itemArgs.push_back(make_unique<Var>("updated_item_price"));
                itemArgs.push_back(make_unique<Var>("updated_item_description"));
                auto updatedItem = make_unique<FuncCall>("menu_item", move(itemArgs));
                
                vector<unique_ptr<Expr>> setArgs;
                setArgs.push_back(move(updatedItem));
                unionArgs.push_back(make_unique<FuncCall>("singleton_set", move(setArgs)));
            }
            postArgs.push_back(make_unique<FuncCall>("union", move(unionArgs)));
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
                 make_unique<TypeConst>("AdminRecord"))));
    // Admin token to username map
    globals.push_back(make_unique<Decl>(
        "AT", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));
    // Restaurant data map (restaurant_name -> restaurant_record)
    globals.push_back(make_unique<Decl>(
        "R", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("RestaurantRecord"))));
    // Menu data map (restaurant_id -> menu_items_set)
    globals.push_back(make_unique<Decl>(
        "M", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("MenuItemSet"))));

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