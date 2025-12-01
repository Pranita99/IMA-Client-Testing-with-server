

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

static unique_ptr<Expr> mkDom(const string& mapName) {
    vector<unique_ptr<Expr>> args;
    args.push_back(make_unique<Var>(mapName));
    return make_unique<FuncCall>("dom", std::move(args));
}

// in_dom(T, token)
static unique_ptr<Expr> mkInDom(const string& mapName, const string& keyVar) {
    vector<unique_ptr<Expr>> args;
    args.push_back(make_unique<Var>(mapName)); // map
    args.push_back(make_unique<Var>(keyVar));  // key
    return make_unique<FuncCall>("in_dom", std::move(args));
}

static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // account(token);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        stmts.push_back(
            make_unique<FuncCallStmt>(
                make_unique<FuncCall>("account", std::move(args))));
    }

    return Program(std::move(stmts));
}

static Spec buildSpec()
{
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>(
        "U",
        make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>(
        "T",
        make_unique<MapType>(
            make_unique<TypeConst>("string"),
            make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>(
        "token",
        make_unique<TypeConst>("string")));

    // Initial: U = {}, T = {}
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));

    vector<unique_ptr<FuncDecl>> funs;
    vector<unique_ptr<API>>      apis;

    // Only API: account(token)
    {
        // pre: token ∈ dom(T)
        auto pre = mkInDom("T", "token");

        // call
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        auto callExpr = make_unique<FuncCall>("account", std::move(args));

        // post: true
        auto post = make_unique<Var>("true");
        Response resp(HTTPResponseCode::OK_200, std::move(post));

        auto apiCall = make_unique<APIcall>(
            std::move(callExpr),
            Response(HTTPResponseCode::OK_200, make_unique<Var>("true")));

        apis.push_back(make_unique<API>(
            std::move(pre),
            std::move(apiCall),
            std::move(resp)));
    }

    return Spec(std::move(globals), std::move(inits),
                std::move(funs), std::move(apis));
}

Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
