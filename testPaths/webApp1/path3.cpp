#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;
/*This is giving unsat and needs changes , as the symbols are clashing */

/* 1 ─ Client program  */
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> s;

    /* login_notok  */
    auto in = [&](const string& v){
        auto lhs = make_unique<Var>(v);
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>(""));
        s.push_back(make_unique<Assign>(move(lhs),
                 make_unique<FuncCall>("input", move(a))));
    };
    in("username");
    in("password");
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        s.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_notok", move(a))));
    }

    /* login_ok  */
    in("username"); in("password");
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        s.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_ok", move(a))));
    }

    /* onboard → map → logout  */
    s.push_back(make_unique<FuncCallStmt>(
        make_unique<FuncCall>("do_onboard", vector<unique_ptr<Expr>>{})));
    s.push_back(make_unique<FuncCallStmt>(
        make_unique<FuncCall>("go_map", vector<unique_ptr<Expr>>{})));
    {
        vector<unique_ptr<Expr>> a; a.push_back(make_unique<Var>("username"));
        s.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("logout", move(a))));
    }
    return Program(std::move(s));
}

/* 2 ─ API specification  */
static Spec buildSpec()
{
    auto mapVal = [](const string& m,const string& k){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(m));
        mv.push_back(make_unique<Var>(k));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };
    auto boolEq = [](unique_ptr<Expr> lhs, const string& lit){
        vector<unique_ptr<Expr>> e;
        e.push_back(std::move(lhs));
        e.push_back(make_unique<String>(lit));
        return make_unique<FuncCall>("equals", move(e));
    };

    vector<unique_ptr<API>> B;

/*  ▸ 1. login_notok  */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));

        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          h.push_back(make_unique<Var>("token"));
          conj.push_back(make_unique<FuncCall>("in_dom", move(h))); }

        vector<unique_ptr<Expr>> ψ;
        ψ.push_back(make_unique<FuncCall>("and_operator", move(conj)));
        auto pre = make_unique<FuncCall>("is_false", move(ψ));

        vector<unique_ptr<Expr>> ca;
        ca.push_back(make_unique<Var>("u"));
        ca.push_back(make_unique<Var>("p"));
        auto call = make_unique<FuncCall>("login_notok", move(ca));

        vector<unique_ptr<Expr>> postEq;
        postEq.push_back(mapVal("T","u"));
        postEq.push_back(make_unique<Var>("token"));
        vector<unique_ptr<Expr>> wrap;
        wrap.push_back(make_unique<FuncCall>("equals", move(postEq)));
        auto post = make_unique<FuncCall>("is_false", move(wrap));

        Response r(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        B.push_back(make_unique<API>(move(pre),
                  make_unique<APIcall>(move(call), move(r)), move(r)));
    }

/*  ▸ 2. login_ok  */
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

        vector<unique_ptr<Expr>> ca;
        ca.push_back(make_unique<Var>("u"));
        ca.push_back(make_unique<Var>("p"));
        auto call = make_unique<FuncCall>("login_ok", move(ca));

        vector<unique_ptr<Expr>> postEq;
        postEq.push_back(mapVal("T","u"));
        postEq.push_back(make_unique<Var>("token"));
        auto post = make_unique<FuncCall>("equals", move(postEq));

        Response r(HTTPResponseCode::OK_200, post->clone());
        B.push_back(make_unique<API>(move(pre),
                  make_unique<APIcall>(move(call), move(r)), move(r)));
    }

/*  ▸ 3. do_onboard  */
    {
        auto pre  = boolEq(make_unique<Var>("onboard"), "false");

        auto call = make_unique<FuncCall>("do_onboard",
                                          vector<unique_ptr<Expr>>{});

        auto post = boolEq(make_unique<Var>("onboard"), "true");

        Response r(HTTPResponseCode::OK_200, post->clone());
        B.push_back(make_unique<API>(move(pre),
                  make_unique<APIcall>(move(call), move(r)), move(r)));
    }

/*  ▸ 4. go_map  */
    {
        auto pre = boolEq(make_unique<Var>("onboard"), "true");
        auto call = make_unique<FuncCall>("go_map",
                                          vector<unique_ptr<Expr>>{});

        vector<unique_ptr<Expr>> p;
        p.push_back(make_unique<Var>("location"));
        p.push_back(make_unique<String>("map"));
        auto post = make_unique<FuncCall>("in", move(p));

        Response r(HTTPResponseCode::OK_200, post->clone());
        B.push_back(make_unique<API>(move(pre),
                  make_unique<APIcall>(move(call), move(r)), move(r)));
    }

/*  ▸ 5. logout  */
    {
        vector<unique_ptr<Expr>> preEq;
        preEq.push_back(mapVal("T","u"));
        preEq.push_back(make_unique<Var>("token"));
        auto pre = make_unique<FuncCall>("equals", move(preEq));

        vector<unique_ptr<Expr>> ca; ca.push_back(make_unique<Var>("u"));
        auto call = make_unique<FuncCall>("logout", move(ca));

        vector<unique_ptr<Expr>> postA;
        postA.push_back(make_unique<Var>("token"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          postA.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto post = make_unique<FuncCall>("not_in", move(postA));

        Response r(HTTPResponseCode::OK_200, post->clone());
        B.push_back(make_unique<API>(move(pre),
                  make_unique<APIcall>(move(call), move(r)), move(r)));
    }

/*  ▸ Globals & init  */
    vector<unique_ptr<Decl>> G;
    G.push_back(make_unique<Decl>("U",
        make_unique<MapType>(make_unique<TypeConst>("string"),
                             make_unique<TypeConst>("string"))));
    G.push_back(make_unique<Decl>("T",
        make_unique<MapType>(make_unique<TypeConst>("string"),
                             make_unique<TypeConst>("string"))));
    G.push_back(make_unique<Decl>("onboard",
        make_unique<TypeConst>("string")));
    G.push_back(make_unique<Decl>("location",
        make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> I;
    I.push_back(make_unique<Init>("U",
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));
    I.push_back(make_unique<Init>("T",
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));
    I.push_back(make_unique<Init>("onboard",  make_unique<String>("false")));
    I.push_back(make_unique<Init>("location", make_unique<String>("")));

    return Spec(std::move(G), std::move(I),
                vector<unique_ptr<FuncDecl>>{}, std::move(B));
}

/* 3 ─ Export for the driver  */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
