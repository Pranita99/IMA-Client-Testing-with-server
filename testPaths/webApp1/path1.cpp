#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;

static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // Signup
    {
        auto lhs = make_unique<Var>("u");
        vector<unique_ptr<Expr>> args;
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    {
        auto lhs = make_unique<Var>("p");
        vector<unique_ptr<Expr>> args;
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(args))));
    }

    // Login
    {
        auto lhs = make_unique<Var>("u");
        vector<unique_ptr<Expr>> args;
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    {
        auto lhs = make_unique<Var>("p");
        vector<unique_ptr<Expr>> args;
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(args))));
    }
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(args))));
    }

    return Program(move(stmts));
}

static Spec buildSpec()
{
    vector<unique_ptr<API>> blocks;

    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    // Signup API
    {
        vector<unique_ptr<Expr>> notInArgs;
        notInArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("U"));
            notInArgs.push_back(make_unique<FuncCall>("dom", move(domArgs)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(notInArgs));

        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto call = make_unique<FuncCall>("signup_success", move(callArgs));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U", "u"));
        eq.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        auto apiCall = make_unique<APIcall>(move(call),
                         Response(HTTPResponseCode::CREATED_201, post->clone()));

        blocks.push_back(make_unique<API>(move(pre), move(apiCall),
                         Response(HTTPResponseCode::CREATED_201, post->clone())));
    }

    // Login API
    {
        vector<unique_ptr<Expr>> conj;

        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U", "u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        {
            vector<unique_ptr<Expr>> domArgs;
            domArgs.push_back(make_unique<Var>("T"));
            domArgs.push_back(make_unique<Var>("token"));
            conj.push_back(make_unique<FuncCall>("in_dom", move(domArgs)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> callArgs;
        callArgs.push_back(make_unique<Var>("u"));
        callArgs.push_back(make_unique<Var>("p"));
        auto call = make_unique<FuncCall>("login_success", move(callArgs));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T", "u"));
        eq2.push_back(make_unique<Var>("token"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        auto apiCall = make_unique<APIcall>(move(call),
                         Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(move(pre), move(apiCall),
                         Response(HTTPResponseCode::OK_200, post->clone())));
    }

    vector<unique_ptr<Decl>> globals;

    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>(
        "token", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    for (const string& m : {"U", "T"})
        inits.push_back(make_unique<Init>(
            m, make_unique<Map>(vector<pair<unique_ptr<Var>, unique_ptr<Expr>>>{})));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{}, std::move(blocks));
}

Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
