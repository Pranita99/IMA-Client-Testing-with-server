// Path 3:
// login_success → logout → getmenu → add_to_cart → order
// Invalid flow: token is removed after logout → order fails ⇒ UNSAT expected.

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the client Program
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // username = input();
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    // logout(username);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
    }

    // getmenu(canteen_2);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("canteen_2"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getmenu", move(a))));
    }

    // add_to_cart(item_3);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_3"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // order(cart);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("cart"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("order", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API Specification
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> apis;

    // --- login_success ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> notIn;
            notIn.push_back(make_unique<Var>("T"));
            notIn.push_back(make_unique<Var>("token"));
            conj.push_back(make_unique<FuncCall>("not_in", move(notIn)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T", "token"));
        eq2.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- logout ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            preArgs.push_back(make_unique<FuncCall>("mapped_value", move(h)));
        }
        auto pre = make_unique<FuncCall>("equals", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("logout", move(args));

        vector<unique_ptr<Expr>> ni;
        ni.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            ni.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto post = make_unique<FuncCall>("not_in", move(ni));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- getmenu ---
    {
        auto pre = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>());

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("canteen_2"));
        auto callFn = make_unique<FuncCall>("getmenu", move(args));

        auto post = make_unique<FuncCall>("menu_visible", vector<unique_ptr<Expr>>());

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_3"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("item_3"));
        auto post = make_unique<FuncCall>("in_cart", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("cart"));
        auto pre = make_unique<FuncCall>("not_empty", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("cart"));
        auto post = make_unique<FuncCall>("ordered", move(postArgs));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Globals ---
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("cart", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apis));
}

// ────────────────────────────────────────────────
// 3. Export to Driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
