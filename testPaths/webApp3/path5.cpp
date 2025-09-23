// Flow 5:
// Attempt to login without prior signup
// input(username), input(password)
// login_success(username, password)
// Expected UNSAT: because user is not in U (user DB)

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
        stmts.push_back(make_unique<Assign>(
            move(lhs), make_unique<FuncCall>("input", move(a))));
    }

    // input(password)
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(
            move(lhs), make_unique<FuncCall>("input", move(a))));
    }

    // login_success(username, password)
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("username"));
        args.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(args))));
    }

    return Program(std::move(stmts));
}

static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> apis;

    // login_success spec
    {
        vector<unique_ptr<Expr>> conj;

        // U[username] == password
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // token ∉ dom(T)
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

        vector<unique_ptr<Expr>> postEq;
        postEq.push_back(mapVal("T", "token"));
        postEq.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(postEq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        apis.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // Globals and Init
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); // U = {}
    inits.push_back(make_unique<Init>("T", make_unique<Map>(
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); // T = {}

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(apis));
}

Program clientProgram = buildClientProgram();
Spec spec = buildSpec();
