

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;



static unique_ptr<Expr> mkEquals(unique_ptr<Expr> a, unique_ptr<Expr> b) {
    vector<unique_ptr<Expr>> args;
    args.push_back(std::move(a));
    args.push_back(std::move(b));
    return make_unique<FuncCall>("equals", std::move(args));
}

static unique_ptr<Expr> mkAnd(vector<unique_ptr<Expr>> items) {
    return make_unique<FuncCall>("and_operator", std::move(items));
}

static unique_ptr<Expr> mkDom(const string& mapName) {
    vector<unique_ptr<Expr>> args;
    args.push_back(make_unique<Var>(mapName));
    return make_unique<FuncCall>("dom", std::move(args));
}


static unique_ptr<Expr> mkInDom(const string& mapName, const string& keyVar) {
    vector<unique_ptr<Expr>> args;
    args.push_back(make_unique<Var>(mapName)); // map
    args.push_back(make_unique<Var>(keyVar));  // key
    return make_unique<FuncCall>("in_dom", std::move(args));
}


static unique_ptr<Expr> mkNotInDom(const string& mapName, const string& keyVar) {
    vector<unique_ptr<Expr>> args;
    // pattern: not_in(key, dom(U))
    args.push_back(make_unique<Var>(keyVar));   // key
    args.push_back(mkDom(mapName));             // dom(U)
    return make_unique<FuncCall>("not_in", std::move(args));
}

// mapVal(U, u)
static unique_ptr<Expr> mkMapVal(const string& mapName, const string& keyVar) {
    vector<unique_ptr<Expr>> args;
    args.push_back(make_unique<Var>(mapName));
    args.push_back(make_unique<Var>(keyVar));
    return make_unique<FuncCall>("mapVal", std::move(args));
}


static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(
            make_unique<FuncCallStmt>(
                make_unique<FuncCall>("signup_success", std::move(args))));
    }

    // login_success(username, password);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(
            make_unique<FuncCallStmt>(
                make_unique<FuncCall>("login_success", std::move(args))));
    }

   
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

    
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));
    inits.push_back(make_unique<Init>("T", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));

    vector<unique_ptr<FuncDecl>> funs;
    vector<unique_ptr<API>>      apis;

   
    {
       
        auto pre = mkNotInDom("U", "username");

      
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        auto callExpr = make_unique<FuncCall>("signup_success", std::move(args));

        
        auto post = mkInDom("U", "username");

        
        Response resp(HTTPResponseCode::CREATED_201, std::move(post));
        auto apiCall = make_unique<APIcall>(
            std::move(callExpr),
            Response(HTTPResponseCode::CREATED_201, make_unique<Var>("true")));

        apis.push_back(make_unique<API>(
            std::move(pre),
            std::move(apiCall),
            std::move(resp)));
    }

   
    {
       
        vector<unique_ptr<Expr>> conj;
        conj.push_back(mkInDom("U", "username"));
        conj.push_back(
            mkEquals(
                mkMapVal("U", "username"),
                make_unique<Var>("password")));

        auto pre = mkAnd(std::move(conj));

      
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        auto callExpr = make_unique<FuncCall>("login_success", std::move(args));

      
        auto post = mkInDom("T", "token");

        Response resp(HTTPResponseCode::OK_200, std::move(post));
        auto apiCall = make_unique<APIcall>(
            std::move(callExpr),
            Response(HTTPResponseCode::OK_200, make_unique<Var>("true")));

        apis.push_back(make_unique<API>(
            std::move(pre),
            std::move(apiCall),
            std::move(resp)));
    }

   
    {
       
        auto pre = mkInDom("T", "token");

       
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("token"));
        auto callExpr = make_unique<FuncCall>("account", std::move(args));

       
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
