#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;

/* ────────────────────────────────────────────────
 * 1. Build the client Program
 * ──────────────────────────────────────────────── */
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    /* username = input(); */
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    /* password = input(); */
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }
    /* login_success(username, password) */
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }
    /* getProducts(username) */
    {
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>("username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getProducts", move(a))));
    }
    /* viewProduct(productID) */
    {
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>("productID"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("viewProduct", move(a))));
    }
    /* addToWishlist(productID, username) */
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("productID"));
        a.push_back(make_unique<Var>("username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("addToWishlist", move(a))));
    }
    /* viewWishlist(username) */
    {
        vector<unique_ptr<Expr>> a;  a.push_back(make_unique<Var>("username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("viewWishlist", move(a))));
    }

    return Program(std::move(stmts));
}

/* ────────────────────────────────────────────────
 * 2. Build the API specification (five blocks)
 * ──────────────────────────────────────────────── */
static Spec buildSpec()
{
    /* helper  mapVal(M,k) → mapped_value(M,k) */
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

/* ---------- login_success ---------- */
    {
        /* pre: equals(U[u],p) ∧ in_dom(T,token) */
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("U","u"));
        eq.push_back(make_unique<Var>("p"));

        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            conj.push_back(make_unique<FuncCall>("in_dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T","u"));
        eq2.push_back(make_unique<Var>("token"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        auto apicall = make_unique<APIcall>(
                std::move(callFn),
                Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(
                std::move(pre),
                std::move(apicall),
                Response(HTTPResponseCode::OK_200, post->clone())));
    }

/* ---------- getProducts ---------- */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(h)));
        }
        auto pre = make_unique<FuncCall>("equals", move(eq));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        a.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("getProducts", move(a));

        auto post = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>{});

        auto apicall = make_unique<APIcall>(
                std::move(callFn),
                Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(
                std::move(pre),
                std::move(apicall),
                Response(HTTPResponseCode::OK_200, post->clone())));
    }

/* ---------- viewProduct ---------- */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(h)));
        }
        vector<unique_ptr<Expr>> inArgs;
        inArgs.push_back(make_unique<Var>("prodId"));
        {
            vector<unique_ptr<Expr>> domA;
            domA.push_back(make_unique<Var>("ProductIdMap"));
            inArgs.push_back(make_unique<FuncCall>("dom", move(domA)));
        }
        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        conj.push_back(make_unique<FuncCall>("in", move(inArgs)));
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("prodId"));
        auto callFn = make_unique<FuncCall>("viewProduct", move(a));

        auto post = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>{});

        auto apicall = make_unique<APIcall>(
                std::move(callFn),
                Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(
                std::move(pre),
                std::move(apicall),
                Response(HTTPResponseCode::OK_200, post->clone())));
    }

/* ---------- addToWishlist ---------- */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(h)));
        }
        vector<unique_ptr<Expr>> inArgs;
        inArgs.push_back(make_unique<Var>("prodId"));
        {
            vector<unique_ptr<Expr>> domA;
            domA.push_back(make_unique<Var>("ProductIdMap"));
            inArgs.push_back(make_unique<FuncCall>("dom", move(domA)));
        }
        vector<unique_ptr<Expr>> conj;
        conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        conj.push_back(make_unique<FuncCall>("in", move(inArgs)));
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("prodId"));
        a.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("addToWishlist", move(a));

        vector<unique_ptr<Expr>> idx;
        idx.push_back(make_unique<Var>("Wishlist"));
        idx.push_back(make_unique<Var>("u"));
        auto wlAccess = make_unique<FuncCall>("getMapAtMatch", move(idx));

        vector<unique_ptr<Expr>> postIn;
        postIn.push_back(make_unique<Var>("prodId"));
        {
            vector<unique_ptr<Expr>> domA;
            domA.push_back(std::move(wlAccess));
            postIn.push_back(make_unique<FuncCall>("dom", move(domA)));
        }
        auto post = make_unique<FuncCall>("in", move(postIn));

        auto apicall = make_unique<APIcall>(
                std::move(callFn),
                Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(
                std::move(pre),
                std::move(apicall),
                Response(HTTPResponseCode::OK_200, post->clone())));
    }

/* ---------- viewWishlist ---------- */
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("T"));
            h.push_back(make_unique<Var>("token"));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(h)));
        }
        auto pre = make_unique<FuncCall>("equals", move(eq));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("viewWishlist", move(a));

        auto post = make_unique<FuncCall>("true", vector<unique_ptr<Expr>>{});

        auto apicall = make_unique<APIcall>(
                std::move(callFn),
                Response(HTTPResponseCode::OK_200, post->clone()));

        blocks.push_back(make_unique<API>(
                std::move(pre),
                std::move(apicall),
                Response(HTTPResponseCode::OK_200, post->clone())));
    }

/* ----------- Globals & Init ----------- */
    vector<unique_ptr<Decl>> globals;

    globals.push_back(make_unique<Decl>(
        "U", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>(
        "T", make_unique<MapType>(
                 make_unique<TypeConst>("string"),
                 make_unique<TypeConst>("string"))));

    auto buildProductTupleType = []{
        vector<unique_ptr<TypeExpr>> f;
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("int"));
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("string"));
        return make_unique<TupleType>(move(f));
    };
    globals.push_back(make_unique<Decl>(
        "ProductIdMap",
        make_unique<MapType>(make_unique<TypeConst>("string"),
                             buildProductTupleType())));

    {
        vector<unique_ptr<TypeExpr>> elem;
        elem.push_back(make_unique<TypeConst>("string"));
        globals.push_back(make_unique<Decl>(
            "Wishlist",
            make_unique<MapType>(
                make_unique<TypeConst>("string"),
                make_unique<TupleType>(move(elem)))));
    }

    globals.push_back(make_unique<Decl>(
        "token", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    for (const string& m : {"U","T","ProductIdMap","Wishlist"})
        inits.push_back(make_unique<Init>(
            m, make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));

    return Spec(std::move(globals), std::move(inits),
                vector<unique_ptr<FuncDecl>>{}, std::move(blocks));
}

/* ────────────────────────────────────────────────
 * 3. Export globals for the driver
 * ──────────────────────────────────────────────── */
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
