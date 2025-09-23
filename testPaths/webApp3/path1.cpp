// Path 1:
// Signup → Login → Get Menu → Add to Cart → Order  (Valid path, should be SAT)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1) Client program (imperative path under test)
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // username = input();
    {
        auto lhs = make_unique<Var>("username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // password = input();
    {
        auto lhs = make_unique<Var>("password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // signup_success(username, password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("username"));
        a.push_back(make_unique<Var>("password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_success", move(a))));
    }

    // login_success(username, password);
    {
      vector<unique_ptr<Expr>> a;
      a.push_back(make_unique<Var>("username"));
      a.push_back(make_unique<Var>("password"));
      stmts.push_back(make_unique<FuncCallStmt>(
          make_unique<FuncCall>("login_success", move(a))));
    }

    // getmenu(canteen_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("canteen_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("getmenu", move(a))));
    }

    // add_to_cart(item_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("add_to_cart", move(a))));
    }

    // order(item_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("item_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("order", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2) API specification (semantic pres / posts)
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    // mapped_value(M, k) → printer introduces Dom_M / Val_M and (select Val_M k)
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    // getMapAtMatch("BaseMap", key) → derived map “BaseMap@key”
    auto atBucket = [](const string& baseMap, unique_ptr<Expr> keyExpr){
        vector<unique_ptr<Expr>> v;
        v.push_back(make_unique<Var>(baseMap));
        v.push_back(std::move(keyExpr));
        return make_unique<FuncCall>("getMapAtMatch", move(v));
    };

    vector<unique_ptr<API>> blocks;

    // --- signup_success ---
    // pre : u ∉ dom(U)
    // post: U[u] == p
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("u"));
        {
            vector<unique_ptr<Expr>> d; d.push_back(make_unique<Var>("U"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(d)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(preArgs));

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

    // --- login_success ---
    // pre : U[u] == p  ∧  token ∉ dom(T)
    // post: T[token] == u
    {
        vector<unique_ptr<Expr>> conj;

        {   // U[u] == p
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("U","u"));
            eq.push_back(make_unique<Var>("p"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {   // token ∉ dom(T)
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("token"));
            {
                vector<unique_ptr<Expr>> d; d.push_back(make_unique<Var>("T"));
                h.push_back(make_unique<FuncCall>("dom", move(d)));
            }
            conj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("u"));
        args.push_back(make_unique<Var>("p"));
        auto callFn = make_unique<FuncCall>("login_success", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("T","token"));
        eq.push_back(make_unique<Var>("u"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- getmenu ---
    // pre : canteen_id ∈ dom(C)
    // post: menuList = M[canteen_id]
    {
        // pre: in(canteen_id, dom(C))
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("canteen_id"));
        {
            vector<unique_ptr<Expr>> d; d.push_back(make_unique<Var>("C"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(d)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        // call: getmenu(canteen_id)
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("canteen_id"));
        auto callFn = make_unique<FuncCall>("getmenu", move(args));

        // post: equals(menuList, M[canteen_id])
        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("menuList"));
        postArgs.push_back(mapVal("M","canteen_id"));
        auto post = make_unique<FuncCall>("equals", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- add_to_cart ---
    // pre : in(token, dom(T))  ∧  in(item_id, mapVal(M, canteen_id))
    // post: in(item_id, dom(Cart@T[token]))
    {
        // pre: in(token, dom(T)) ∧ in(item_id, mapVal(M,canteen_id))
        vector<unique_ptr<Expr>> preAnd;

        {   // in(token, dom(T))
            vector<unique_ptr<Expr>> a;
            a.push_back(make_unique<Var>("token"));
            { vector<unique_ptr<Expr>> d; d.push_back(make_unique<Var>("T"));
              a.push_back(make_unique<FuncCall>("dom", move(d))); }
            preAnd.push_back(make_unique<FuncCall>("in", move(a)));
        }
        {   // in(item_id, mapVal(M, canteen_id))
            vector<unique_ptr<Expr>> b;
            b.push_back(make_unique<Var>("item_id"));
            { vector<unique_ptr<Expr>> mv;
              mv.push_back(make_unique<Var>("M"));
              mv.push_back(make_unique<Var>("canteen_id"));
              b.push_back(make_unique<FuncCall>("mapped_value", move(mv))); }
            preAnd.push_back(make_unique<FuncCall>("in", move(b)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(preAnd));

        // call
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));
        auto callFn = make_unique<FuncCall>("add_to_cart", move(args));

        // post: in(item_id, dom(Cart@T[token]))
        // user := mapVal(T, token)
        vector<unique_ptr<Expr>> uargs;
        uargs.push_back(make_unique<Var>("T"));
        uargs.push_back(make_unique<Var>("token"));
        auto user = make_unique<FuncCall>("mapped_value", move(uargs)); // T[token]

        // Cart@user
        auto cart_bucket = atBucket("Cart", user->clone());

        // dom(Cart@user)
        vector<unique_ptr<Expr>> dcb; dcb.push_back(cart_bucket->clone());
        auto dom_cart_bucket = make_unique<FuncCall>("dom", move(dcb));

        vector<unique_ptr<Expr>> postArgs;
        postArgs.push_back(make_unique<Var>("item_id"));
        postArgs.push_back(dom_cart_bucket->clone());
        auto post = make_unique<FuncCall>("in", move(postArgs));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- order ---
    // pre:
    //   in(token, dom(T)) ∧ not_empty(dom(Cart@T[token]))
    //   ∧ subset(dom(Cart@T[token]), dom(getMapAtMatch(M, canteen_id)))
    // post:
    //   clear user cart: subset(dom(Cart@T[token]), false)
    //   (optionally assert QR mapping; we keep it as an equality with an uninterpreted generator)
    {
        // ---------- PRE ----------
        vector<unique_ptr<Expr>> conj;

        // in(token, dom(T))
        {
            vector<unique_ptr<Expr>> a;
            a.push_back(make_unique<Var>("token"));
            { vector<unique_ptr<Expr>> d; d.push_back(make_unique<Var>("T"));
              a.push_back(make_unique<FuncCall>("dom", move(d))); }
            conj.push_back(make_unique<FuncCall>("in", move(a)));
        }

        // user := mapVal(T, token)
        vector<unique_ptr<Expr>> uargs;
        uargs.push_back(make_unique<Var>("T"));
        uargs.push_back(make_unique<Var>("token"));
        auto user = make_unique<FuncCall>("mapped_value", move(uargs)); // T[token]

        // dom(Cart@user)
        auto cart_bucket = atBucket("Cart", user->clone());
        vector<unique_ptr<Expr>> dcb; dcb.push_back(cart_bucket->clone());
        auto dom_cart_bucket = make_unique<FuncCall>("dom", move(dcb));

        // not_empty(dom(Cart@user))
        {
            vector<unique_ptr<Expr>> ne; ne.push_back(dom_cart_bucket->clone());
            conj.push_back(make_unique<FuncCall>("not_empty", move(ne)));
        }

        // subset(dom(Cart@user), dom(getMapAtMatch(M, canteen_id)))
        {
            // dom(getMapAtMatch(M, canteen_id))
            vector<unique_ptr<Expr>> mm;
            mm.push_back(make_unique<Var>("M"));
            mm.push_back(make_unique<Var>("canteen_id"));
            auto matched = make_unique<FuncCall>("getMapAtMatch", move(mm));
            vector<unique_ptr<Expr>> dMatched; dMatched.push_back(move(matched));
            auto domMatched = make_unique<FuncCall>("dom", move(dMatched));

            vector<unique_ptr<Expr>> ss;
            ss.push_back(dom_cart_bucket->clone());
            ss.push_back(move(domMatched));
            conj.push_back(make_unique<FuncCall>("subset", move(ss)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        // ---------- CALL ----------
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("item_id"));   // preserved signature
        auto callFn = make_unique<FuncCall>("order", move(args));

        // ---------- POST ----------
        vector<unique_ptr<Expr>> posts;

        // clear user cart: subset(dom(Cart@user), false)
        {
            vector<unique_ptr<Expr>> ss;
            ss.push_back(dom_cart_bucket->clone());
            ss.push_back(make_unique<Var>("false"));
            posts.push_back(make_unique<FuncCall>("subset", move(ss)));
        }

        // optional: Q'[savedOrder.id] = generateQRCode(savedOrder)
        {
            // generateQRCode(savedOrder)
            vector<unique_ptr<Expr>> genArgs;
            genArgs.push_back(make_unique<Var>("savedOrder"));
            auto gen = make_unique<FuncCall>("generateQRCode", move(genArgs));

            // equals( mapVal(Q, savedOrder_id), gen )
            vector<unique_ptr<Expr>> eq;
            {
                vector<unique_ptr<Expr>> mv;
                mv.push_back(make_unique<Var>("Q"));
                mv.push_back(make_unique<Var>("savedOrder_id"));
                eq.push_back(make_unique<FuncCall>("mapped_value", move(mv)));
            }
            eq.push_back(move(gen));
            posts.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(posts));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ───────────────────────────────────────────
    // 3) Globals (only what the spec really needs)
    // ───────────────────────────────────────────
    vector<unique_ptr<Decl>> globals;

    // U : Map(username → password)
    globals.push_back(make_unique<Decl>("U", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    // T : Map(token → username)
    globals.push_back(make_unique<Decl>("T", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    // M : Map(canteen_id → menuList)
    globals.push_back(make_unique<Decl>("M", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    // C : Map(canteen_id → Canteen)  (we only use dom(C) in getmenu pre)
    globals.push_back(make_unique<Decl>("C", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    // Cart : Map(username → Bool)  (cart bucket per user; membership via dom(Cart@user))
    globals.push_back(make_unique<Decl>("Cart", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("Bool"))));
    // Q : Map(orderId → QRCode)   (optional parity)
    globals.push_back(make_unique<Decl>("Q", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Scalars touched by specs
    globals.push_back(make_unique<Decl>("token",      make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("canteen_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("item_id",    make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("menuList",   make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("savedOrder", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("savedOrder_id", make_unique<TypeConst>("string")));

    // Initial maps are empty
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("U",    make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("T",    make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("M",    make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("C",    make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); // canteens
    inits.push_back(make_unique<Init>("Cart", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); // carts
    inits.push_back(make_unique<Init>("Q",    make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3) Exported for the driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
