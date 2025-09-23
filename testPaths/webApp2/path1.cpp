#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"

using namespace std;

static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    auto in = [&](const string& var) {
        auto lhs = make_unique<Var>(var);
        vector<unique_ptr<Expr>> a;
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    };

    in("u");
    in("p");
    in("prodId");

    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        a.push_back(make_unique<Var>("p"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_success", move(a))));
    }

    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getProducts", move(a))));
    }

    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("prodId"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("viewProduct", move(a))));
    }

    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("prodId"));
        a.push_back(make_unique<Var>("u"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("addToWishlist", move(a))));
    }

    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("viewWishlist", move(a))));
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

    vector<unique_ptr<API>> blocks;

    // login_success
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
            domArgs.push_back(mapVal("T", "u"));
            conj.push_back(make_unique<FuncCall>("in_dom", move(domArgs)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq2;
        eq2.push_back(mapVal("T", "u"));
        eq2.push_back(mapVal("T", "u"));
        auto post = make_unique<FuncCall>("equals", move(eq2));

        Response r(HTTPResponseCode::OK_200, post->clone());
        blocks.push_back(make_unique<API>(
            move(pre),
            make_unique<APIcall>(move(callFn), std::move(r)),
            std::move(r)));
    }

    // getProducts
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        eq.push_back(mapVal("T", "u"));
        auto pre = make_unique<FuncCall>("equals", move(eq));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("getProducts", move(a));

        auto post = make_unique<String>("true");

        Response r(HTTPResponseCode::OK_200, post->clone());
        blocks.push_back(make_unique<API>(
            move(pre),
            make_unique<APIcall>(move(callFn), std::move(r)),
            std::move(r)));
    }

    // viewProduct
    {
        vector<unique_ptr<Expr>> conj;

        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("u"));
            eq.push_back(mapVal("T", "u"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("prodId"));
            {
                vector<unique_ptr<Expr>> domA;
                domA.push_back(make_unique<Var>("ProductIdMap"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domA)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("prodId"));
        auto callFn = make_unique<FuncCall>("viewProduct", move(a));

        auto post = make_unique<String>("true");

        Response r(HTTPResponseCode::OK_200, post->clone());
        blocks.push_back(make_unique<API>(
            move(pre),
            make_unique<APIcall>(move(callFn), std::move(r)),
            std::move(r)));
    }

    // addToWishlist
    {
        vector<unique_ptr<Expr>> conj;

        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("u"));
            eq.push_back(mapVal("T", "u"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        {
            vector<unique_ptr<Expr>> inArgs;
            inArgs.push_back(make_unique<Var>("prodId"));
            {
                vector<unique_ptr<Expr>> domA;
                domA.push_back(make_unique<Var>("ProductIdMap"));
                inArgs.push_back(make_unique<FuncCall>("dom", move(domA)));
            }
            conj.push_back(make_unique<FuncCall>("in", move(inArgs)));
        }

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
            domA.push_back(move(wlAccess));
            postIn.push_back(make_unique<FuncCall>("dom", move(domA)));
        }
        auto post = make_unique<FuncCall>("in", move(postIn));

        Response r(HTTPResponseCode::OK_200, post->clone());
        blocks.push_back(make_unique<API>(
            move(pre),
            make_unique<APIcall>(move(callFn), std::move(r)),
            std::move(r)));
    }

    // viewWishlist
    {
        vector<unique_ptr<Expr>> eq;
        eq.push_back(make_unique<Var>("u"));
        eq.push_back(mapVal("T", "u"));
        auto pre = make_unique<FuncCall>("equals", move(eq));

        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("u"));
        auto callFn = make_unique<FuncCall>("viewWishlist", move(a));

        auto post = make_unique<String>("true");

        Response r(HTTPResponseCode::OK_200, post->clone());
        blocks.push_back(make_unique<API>(
            move(pre),
            make_unique<APIcall>(move(callFn), std::move(r)),
            std::move(r)));
    }

    // Globals & Inits
    vector<unique_ptr<Decl>> globals;

    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    auto buildProductTupleType = []{
        vector<unique_ptr<TypeExpr>> f;
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("int"));
        f.push_back(make_unique<TypeConst>("string"));
        f.push_back(make_unique<TypeConst>("string"));
        return make_unique<TupleType>(move(f));
    };
    globals.push_back(make_unique<Decl>("ProductIdMap", make_unique<MapType>(
        make_unique<TypeConst>("string"), buildProductTupleType())));

    {
        vector<unique_ptr<TypeExpr>> elem;
        elem.push_back(make_unique<TypeConst>("string"));
        globals.push_back(make_unique<Decl>("Wishlist", make_unique<MapType>(
            make_unique<TypeConst>("string"), make_unique<TupleType>(move(elem)))));
    }

    globals.push_back(make_unique<Decl>("token", make_unique<TypeConst>("string")));

    vector<unique_ptr<Init>> inits;
    for (const string& m : {"U","T","ProductIdMap","Wishlist"})
        inits.push_back(make_unique<Init>(
            m, make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>{})));

    return Spec(std::move(globals), std::move(inits),
                vector<unique_ptr<FuncDecl>>{}, std::move(blocks));
}

Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
