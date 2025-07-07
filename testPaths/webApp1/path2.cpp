#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;

/* ─────────────────────────────────────────────
 * 1.  Client-side test path (imperative program)
 * ───────────────────────────────────────────── */
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    /* ------------------------------------------------ signup_notok */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_notok", move(a))));
    }

    /* ------------------------------------------------ signup_success */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(a))));
    }

    /* ------------------------------------------------ login_notok */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_notok", move(a))));
    }

    /* ------------------------------------------------ login_success */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    return Program(std::move(stmts));
}

/* ─────────────────────────────────────────────
 * 2.  API specification for the four endpoints
 * ───────────────────────────────────────────── */
static Spec buildSpec()
{
    auto mapVal = [](const string& m,const string& k)
    {
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(m));
        mv.push_back(make_unique<Var>(k));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

/* ---------- 1. signup_notok ---------- */
    {
        /* pre: not_in(u , dom(U)) */
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("U"));
          a.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto pre = make_unique<FuncCall>("not_in", move(a));

        /* call */
        vector<unique_ptr<Expr>> ca;
        ca.push_back(make_unique<Var>("u"));
        ca.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_notok", move(ca));

        /* post: is_false( equals(U[u],p) ) */
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));
        vector<unique_ptr<Expr>> wrap;
        wrap.push_back(make_unique<FuncCall>("equals", move(eq)));
        auto post = make_unique<FuncCall>("is_false", move(wrap));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(move(callFn), move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

/* ---------- 2. signup_success ---------- */
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("U"));
          a.push_back(make_unique<FuncCall>("dom", move(h))); }
        auto pre = make_unique<FuncCall>("not_in", move(a));

        vector<unique_ptr<Expr>> ca;
        ca.push_back(make_unique<Var>("u"));
        ca.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("signup_success", move(ca));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apiCall = make_unique<APIcall>(move(callFn), move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

/* ---------- 3. login_notok ---------- */
    {
        /* pre: is_false( equals(U[u],p) ∧ in_dom(T,token) ) */
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));

        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        { vector<unique_ptr<Expr>> h; h.push_back(make_unique<Var>("T"));
          h.push_back(make_unique<Var>("token"));
          conj.push_back(make_unique<FuncCall>("in_dom", move(h))); }

        vector<unique_ptr<Expr>> wrapPre;          /*  FIX ▲  */
        wrapPre.push_back(make_unique<FuncCall>("and_operator", move(conj)));
        auto pre = make_unique<FuncCall>("is_false", move(wrapPre));

        /* call */
        vector<unique_ptr<Expr>> ca;
        ca.push_back(make_unique<Var>("u"));
        ca.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_notok", move(ca));

        /* post: is_false( equals(T[token],u) ) */
        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T","u"));
        eq2.push_back(make_unique<Var>("token"));
        vector<unique_ptr<Expr>> wrapPost;         /*  FIX ▲  */
        wrapPost.push_back(make_unique<FuncCall>("equals", move(eq2)));
        auto post = make_unique<FuncCall>("is_false", move(wrapPost));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apiCall = make_unique<APIcall>(move(callFn), move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

/* ---------- 4. login_success ---------- */
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
        auto callFn = make_unique<FuncCall>("login_success", move(ca));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T","u"));
        eq2.push_back(make_unique<Var>("token"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apiCall = make_unique<APIcall>(move(callFn), move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apiCall), move(resp)));
    }

/* ---------- globals & init ---------- */
    vector<unique_ptr<Decl>> globals;
    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(make_unique<TypeConst>("string"),
                                  make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(make_unique<TypeConst>("string"),
                                  make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>(
        "U", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));
    inits.push_back(make_unique<Init>(
        "T", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));

    return Spec(std::move(globals), std::move(inits),
                vector<unique_ptr<FuncDecl>>{}, std::move(blocks));
}

/* ─────────────────────────────────────────────
 * 3.  Exports picked up by the driver
 * ───────────────────────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
