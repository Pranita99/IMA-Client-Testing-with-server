#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;

/* ────────────────────────────────────────────────
 * 1. Build the client Program (imperative path)
 * ──────────────────────────────────────────────── */
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    /* --- SIGN-UP success ----------------------------------- */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>( move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>( move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(a))));
    }

    /* --- LOGIN success ------------------------------------- */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>( move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>( move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    /* --- LOGOUT -------------------------------------------- */
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
    }

    return Program(std::move(stmts));
}

/* ────────────────────────────────────────────────
 * 2. Build the API specification
 * ──────────────────────────────────────────────── */
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

    /* ----- signup_success ----- */
    {
        vector<unique_ptr<Expr>> preA;
        preA.push_back(make_unique<Var>("u"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("U"));
          preA.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto pre = make_unique<FuncCall>("not_in", move(preA));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_success", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    /* ----- login_success ----- */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));
        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          h.push_back(make_unique<Var>("token"));
          conj.push_back(make_unique<FuncCall>("in_dom", move(h))); }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T","u"));
        eq2.push_back(make_unique<Var>("token"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    /* ----- logout ----- */
    {
        vector<unique_ptr<Expr>> preA;
        preA.push_back(make_unique<Var>("u"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          h.push_back(make_unique<Var>("token"));
          preA.push_back(make_unique<FuncCall>("mapped_value", move(h))); }
        auto pre = make_unique<FuncCall>("equals", move(preA));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("logout", move(args));

        vector<unique_ptr<Expr>> ni;
        ni.push_back(make_unique<Var>("token"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          ni.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto post = make_unique<FuncCall>("not_in", move(ni));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    /* --- globals & init --- */
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
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

/* ────────────────────────────────────────────────
 * 3. Export globals for the driver
 * ──────────────────────────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
