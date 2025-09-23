// Flow: Login → Add to Cart → Order → Logout
// Path: Login → Add items to cart → Place order → Logout
// Expected: SAT (should successfully add to cart, place order and logout)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // input(username)
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs), make_unique<FuncCall>("input", move(a))));
    }

    // input(password)
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs), make_unique<FuncCall>("input", move(a))));
    }

    // signup_success(username, password)
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("signup_success", move(args))));
    }

    // login_success(username, password)
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("login_success", move(args))));
    }

    // add_to_cart(item, quantity) - First item
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("\"pizza\""));
        args.push_back(make_unique<Var>("2"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("add_to_cart", move(args))));
    }

    // add_to_cart(item, quantity) - Second item
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("\"burger\""));
        args.push_back(make_unique<Var>("1"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("add_to_cart", move(args))));
    }

    // order(cart) [cart now has items from add_to_cart operations]
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("order", move(args))));
    }

    // logout(token)
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        stmts.push_back(make_unique<FuncCallStmt>(make_unique<FuncCall>("logout", move(args))));
    }

    return Program(std::move(stmts));
}

static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key) {
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    auto mapSize = [](const string& map) {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(map));
        return make_unique<FuncCall>("size", move(args));
    };

    vector<unique_ptr<API>> apis;

    // signup_success
    {
        vector<unique_ptr<Expr>> pre;
        pre.push_back(make_unique<Var>("u"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("U"));
          pre.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto precond = make_unique<FuncCall>("not_in", move(pre));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_success", move(args));

        vector<unique_ptr<Expr>> post;
        post.push_back(mapVal("U", "u"));
        post.push_back(make_unique<Var>("p"));
        auto postcond = make_unique<FuncCall>("equals", move(post));

        Response resp(HTTPResponseCode::CREATED_201, postcond->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(precond), move(apicall), move(resp)));
    }

    // login_success
    {
        vector<unique_ptr<Expr>> conj;

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U", "u"));
        eq.push_back(make_unique<Var>("p"));
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));

        vector<unique_ptr<Expr>> ni;
        ni.push_back(make_unique<Var>("T"));
        ni.push_back(make_unique<Var>("token"));
        conj.push_back(make_unique<FuncCall>("not_in", move(ni)));

        auto precond = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T", "token"));
        eq2.push_back(make_unique<Var>("u"));
        auto postcond = make_unique<FuncCall>("equals", move(eq2));

        Response resp(HTTPResponseCode::OK_200, postcond->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(precond), move(apicall), move(resp)));
    }

    // add_to_cart
    {
        vector<unique_ptr<Expr>> gtArgs;
        gtArgs.push_back(make_unique<Var>("quantity"));
        gtArgs.push_back(make_unique<Var>("0"));
        auto precond = make_unique<FuncCall>("greater_than", move(gtArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item"));
        args.push_back(make_unique<Var>("quantity"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        vector<unique_ptr<Expr>> post;
        post.push_back(mapVal("cart", "item"));
        post.push_back(make_unique<Var>("quantity"));
        auto postcond = make_unique<FuncCall>("equals", move(post));

        Response resp(HTTPResponseCode::OK_200, postcond->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(precond), move(apicall), move(resp)));
    }

    // order (successful case with non-empty cart)
    {
        vector<unique_ptr<Expr>> gtArgs;
        gtArgs.push_back(mapSize("cart"));
        gtArgs.push_back(make_unique<Var>("0"));
        auto precond = make_unique<FuncCall>("greater_than", move(gtArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("cart"));
        auto callFn = make_unique<FuncCall>("order", move(args));

        auto postcond = make_unique<Var>("\"Order placed successfully\"");

        Response resp(HTTPResponseCode::OK_200, postcond->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(precond), move(apicall), move(resp)));
    }

    // logout
    {
        vector<unique_ptr<Expr>> inArgs;
        inArgs.push_back(make_unique<Var>("token"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          inArgs.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto precond = make_unique<FuncCall>("in", move(inArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        auto callFn = make_unique<FuncCall>("logout", move(args));

        auto postcond = make_unique<Var>("\"Logged out successfully\"");

        Response resp(HTTPResponseCode::OK_200, postcond->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(precond), move(apicall), move(resp)));
    }

    // Globals
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("cart", make_unique<MapType>(make_unique<TypeConst>("string"), make_unique<TypeConst>("int"))));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(vector<pair<unique_ptr<Var>, unique_ptr<Expr>>>{})));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(vector<pair<unique_ptr<Var>, unique_ptr<Expr>>>{})));
    
    // Initialize cart as empty - items will be added via add_to_cart operations
    inits.push_back(make_unique<Init>("cart", make_unique<Map>(vector<pair<unique_ptr<Var>, unique_ptr<Expr>>>{})));

    return Spec(std::move(globals), std::move(inits), std::vector<unique_ptr<FuncDecl>>{}, std::move(apis));
}

Program clientProgram = buildClientProgram();
Spec spec = buildSpec();