#ifndef IMA_HPP
#define IMA_HPP
/* ────────── standard headers ────────── */
#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <string>
#include <memory>
#include <unordered_map>
#include <algorithm>          // sort / unique

/* ────────── project headers ────────── */
#include "ast.hpp"
#include "PrintVisitor.hpp"
#include "symbol_table.hpp"

using namespace std;

/* ══════════════════════════════════════
   1) Per-map snapshot table
   ══════════════════════════════════════*/
struct MapVerTable {
    unordered_map<string,int> ver;           // M -> version

    string verName(const string& base) const {
        auto it = ver.find(base);
        return (it==ver.end() || it->second==0)
               ? base
               : base + '@' + to_string(it->second);
    }
    string bump(const string& base) {
        ++ver[base];
        return verName(base);
    }
};
static MapVerTable gMapVer;

/* convenience alias */
using Env = map<string,string>;              // τ : formal → actual

/* ───────────────────────────── clone helpers ─────────────────────────── */
static unique_ptr<Expr> convert1(unique_ptr<Expr>& expr, SymbolTable* sym, const string& add)
{
    if (!expr) return nullptr;

    if (auto *v = dynamic_cast<Var*>(expr.get()))
        return make_unique<Var>( sym->exists(*v) ? v->name+add : v->name );

    if (auto *n = dynamic_cast<Num*>(expr.get()))
        return make_unique<Num>(n->value);

    if (auto *s = dynamic_cast<String*>(expr.get()))
        return make_unique<String>(s->value);

    if (auto *fc = dynamic_cast<FuncCall*>(expr.get()))
    {
        vector<unique_ptr<Expr>> args;
        for (auto &a : fc->args) args.push_back(convert1(a,sym,add));
        return make_unique<FuncCall>(fc->name, move(args));
    }

    if (auto *set = dynamic_cast<Set*>(expr.get()))
    {
        vector<unique_ptr<Expr>> xs;
        for (auto &e : set->elements) xs.push_back(convert1(e,sym,add));
        return make_unique<Set>(move(xs));
    }

    if (auto *mapE = dynamic_cast<Map*>(expr.get()))
    {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> pairs;
        for (auto &kv : mapE->value) {
            auto k = convert1(reinterpret_cast<unique_ptr<Expr>&>(kv.first),sym,add);
            auto v = convert1(kv.second,sym,add);
            pairs.emplace_back(
                unique_ptr<Var>(dynamic_cast<Var*>(k.release())), move(v));
        }
        return make_unique<Map>(move(pairs));
    }

    if (auto *tup = dynamic_cast<Tuple*>(expr.get()))
    {
        vector<unique_ptr<Expr>> xs;
        for (auto &e : tup->expr) xs.push_back(convert1(e,sym,add));
        return make_unique<Tuple>(move(xs));
    }

    throw runtime_error("convert1: unknown Expr kind");
}

/* Inject current map snapshot names into helper calls */
static unique_ptr<Expr> renameExprWithMap(const Expr* e, const Env& τ)
{
    if (!e) return nullptr;

    if (auto *v = dynamic_cast<const Var*>(e)) {
        auto it = τ.find(v->name);
        return make_unique<Var>( it!=τ.end() ? it->second : v->name );
    }

    if (auto *n = dynamic_cast<const Num*>(e))    return make_unique<Num>(n->value);
    if (auto *s = dynamic_cast<const String*>(e)) return make_unique<String>(s->value);

    if (auto *fc = dynamic_cast<const FuncCall*>(e))
    {
        vector<unique_ptr<Expr>> args;
        for (auto &a : fc->args) args.push_back(renameExprWithMap(a.get(),τ));

        auto bumpFirstArgVarToCurrent = [&](){
            if (!args.empty())
            if (auto *v = dynamic_cast<Var*>(args[0].get()))
                v->name = gMapVer.verName(v->name);
        };

        // dom(M) / mapped_value(M,…) / mapVal(M,…) use current snapshot
        if (fc->name=="dom" || fc->name=="mapped_value" || fc->name=="mapVal")
            bumpFirstArgVarToCurrent();

        // in_dom(M,k) → current snapshot
        if (fc->name=="in_dom")
            bumpFirstArgVarToCurrent();

        // not_in(M,k) pattern (“M” is first arg)
        if (fc->name=="not_in" && args.size()==2) {
            if (dynamic_cast<Var*>(args[0].get()))
                bumpFirstArgVarToCurrent();
            // not_in(k, dom(M)) is covered by dom(M) rule above
        }

        return make_unique<FuncCall>(fc->name, move(args));
    }

    if (auto *set = dynamic_cast<const Set*>(e)) {
        vector<unique_ptr<Expr>> xs;
        for (auto &el : set->elements) xs.push_back(renameExprWithMap(el.get(),τ));
        return make_unique<Set>(move(xs));
    }
    if (auto *mapE = dynamic_cast<const Map*>(e)) {
        vector<pair<unique_ptr<Var>,unique_ptr<Expr>>> pairs;
        for (auto &kv : mapE->value) {
            auto k = renameExprWithMap(kv.first.get(),τ);
            auto v = renameExprWithMap(kv.second.get(),τ);
            pairs.emplace_back(
                unique_ptr<Var>(dynamic_cast<Var*>(k.release())), move(v));
        }
        return make_unique<Map>(move(pairs));
    }
    if (auto *tup = dynamic_cast<const Tuple*>(e)) {
        vector<unique_ptr<Expr>> xs;
        for (auto &ex : tup->expr) xs.push_back(renameExprWithMap(ex.get(),τ));
        return make_unique<Tuple>(move(xs));
    }

    throw runtime_error("renameExprWithMap: unhandled Expr");
}

static unique_ptr<Stmt> cloneStmt(const Stmt* s)
{
    if (auto *a = dynamic_cast<const Assign*>(s)) {
        return make_unique<Assign>( make_unique<Var>(a->left->name),
                                    renameExprWithMap(a->right.get(),{}) );
    }
    if (auto *fc = dynamic_cast<const FuncCallStmt*>(s)) {
        vector<unique_ptr<Expr>> args;
        for (auto &ar : fc->call->args) args.push_back(renameExprWithMap(ar.get(),{}));
        return make_unique<FuncCallStmt>(
                 make_unique<FuncCall>(fc->call->name, move(args)));
    }
    throw runtime_error("cloneStmt: unexpected Stmt kind");
}

/* Find maps referenced in an expression (for deciding which maps to bump) */
static void collectMaps(const Expr* e, vector<string>& out)
{
    if (!e) return;

    if (auto *fc = dynamic_cast<const FuncCall*>(e))
    {
        auto pushVarName = [&](const Expr* ex){
            if (auto *v = dynamic_cast<const Var*>(ex)) out.push_back(v->name);
        };

        if (fc->name=="dom" && !fc->args.empty())                         pushVarName(fc->args[0].get());
        if ((fc->name=="mapped_value" || fc->name=="mapVal") && !fc->args.empty())
                                                                          pushVarName(fc->args[0].get());
        if (fc->name=="in_dom" && !fc->args.empty())                      pushVarName(fc->args[0].get());
        if (fc->name=="not_in" && fc->args.size()==2) {
            pushVarName(fc->args[0].get());                               // not_in(M,k)
            if (auto *d = dynamic_cast<const FuncCall*>(fc->args[1].get()))
                if (d->name=="dom" && !d->args.empty())                   pushVarName(d->args[0].get()); // not_in(k, dom(M))
        }

        for (auto &a : fc->args) collectMaps(a.get(),out);
        return;
    }

    if (auto *set = dynamic_cast<const Set*>(e))
        for (auto &el : set->elements) collectMaps(el.get(),out);

    if (auto *mapE = dynamic_cast<const Map*>(e))
        for (auto &kv : mapE->value) {
            collectMaps(kv.first.get(),out);
            collectMaps(kv.second.get(),out);
        }

    if (auto *tup = dynamic_cast<const Tuple*>(e))
        for (auto &ex : tup->expr) collectMaps(ex.get(),out);
}

static vector<string> getMutatedVars(const API& blk,
                                     const vector<string>& /*formal*/,
                                     const Env& /*τ*/)
{
    vector<string> maps;
    collectMaps(blk.call->response.expr.get(), maps);
    sort(maps.begin(), maps.end());
    maps.erase(unique(maps.begin(), maps.end()), maps.end());
    return maps;
}

/* NEW: collect **scalars** mentioned in Post (to hoist before Post) */
static void collectScalars(const Expr* e,
                           std::vector<std::string>& out,
                           const TypeMap& tmap)
{
    if (!e) return;

    if (auto* v = dynamic_cast<const Var*>(e)) {
        auto it = tmap.mapping.find(v->name);
        bool isMap = (it != tmap.mapping.end() &&
                      dynamic_cast<MapType*>(it->second) != nullptr);
        if (!isMap) out.push_back(v->name);
        return;
    }

    if (auto* fc = dynamic_cast<const FuncCall*>(e)) {
        for (auto& a : fc->args) collectScalars(a.get(), out, tmap);
        return;
    }
    if (auto* s = dynamic_cast<const Set*>(e)) {
        for (auto& el : s->elements) collectScalars(el.get(), out, tmap);
        return;
    }
    if (auto* m = dynamic_cast<const Map*>(e)) {
        for (auto& kv : m->value) {
            collectScalars(kv.first.get(),  out, tmap);
            collectScalars(kv.second.get(), out, tmap);
        }
        return;
    }
    if (auto* t = dynamic_cast<const Tuple*>(e)) {
        for (auto& ex : t->expr) collectScalars(ex.get(), out, tmap);
        return;
    }
}

/* τ (formal → actual) */
static Env createTau(const vector<string>& f, const vector<string>& a)
{
    Env τ;
    for (size_t i=0;i<f.size() && i<a.size();++i) τ[f[i]] = a[i];
    return τ;
}

/* ══════════════════════════════════════
   3) IMA transformation
   ══════════════════════════════════════*/
Program IMA(const Program& P,
            const Spec&    spec,
            SymbolTable&   sym,
            TypeMap&       tmap)
{
    vector<unique_ptr<Stmt>> out;

    /* ---- globals & init block ---------------------------------------- */
    for (auto &g : spec.globals)
        if (!sym.exists(Var(g->name))) {
            sym.symtable.insert(Var(g->name));
            tmap.mapping[g->name] = g->type->clone().release();
        }

    for (auto &ini : spec.init)
        out.push_back( make_unique<Assign>( make_unique<Var>(ini->varName),
                                            ini->expr->clone() ) );

    /* ---- walk client program ----------------------------------------- */
    for (auto &sp : P.statements)
    {
        auto *fcStmt = dynamic_cast<FuncCallStmt*>(sp.get());
        if (!fcStmt) { out.push_back(cloneStmt(sp.get())); continue; }

        /* match against a Spec block */
        API *blk = nullptr; vector<string> formal;
        for (auto &b : spec.blocks)
            if (b->call->call->name == fcStmt->call->name) {
                blk = b.get();
                for (auto &a : blk->call->call->args)
                    if (auto *v = dynamic_cast<Var*>(a.get()))
                        formal.push_back(v->name);
                break;
            }
        if (!blk) { out.push_back(cloneStmt(sp.get())); continue; }

        /* τ  (formal → actual) */
        vector<string> actual;
        for (auto &a : fcStmt->call->args)
            if (auto *v = dynamic_cast<Var*>(a.get()))
                actual.push_back(v->name);
        Env τ = createTau(formal, actual);

        /* -----  PRE  -------------------------------------------------- */
        if (auto pre = renameExprWithMap(blk->pre.get(),τ)) {
            vector<unique_ptr<Expr>> a; a.push_back(move(pre));
            out.push_back( make_unique<FuncCallStmt>(
                 make_unique<FuncCall>("assume", move(a))) );
        }

        /* -----  ORIGINAL CALL  --------------------------------------- */
        out.push_back(cloneStmt(sp.get()));

        /* -----  MAP VERSION BUMPS  ----------------------------------- */
        auto mutated = getMutatedVars(*blk, formal, τ);
        for (auto &m : mutated)
            if (sym.exists(Var(m))) gMapVer.bump(m);   // snapshot ++

        /* -----  SCALAR HOIST before POST  ---------------------------- */
        {
            std::vector<std::string> scalars;
            collectScalars(blk->call->response.expr.get(), scalars, tmap);
            std::sort(scalars.begin(), scalars.end());
            scalars.erase(std::unique(scalars.begin(), scalars.end()), scalars.end());

            for (auto& v : scalars) {
                if (!sym.exists(Var(v))) continue;    // only known program vars
                // v = input();
                std::vector<std::unique_ptr<Expr>> noArgs;
                auto fresh = std::make_unique<FuncCall>("input", std::move(noArgs));
                out.push_back( std::make_unique<Assign>( std::make_unique<Var>(v),
                                                         std::move(fresh) ) );
            }
        }

        /* -----  POST  (translated **after** bump & hoist) ------------- */
        if (auto post = renameExprWithMap(blk->call->response.expr.get(), τ)) {
            vector<unique_ptr<Expr>> a; a.push_back(move(post));
            out.push_back( make_unique<FuncCallStmt>(
                 make_unique<FuncCall>("assert", move(a))) );
        }
    }

    return Program(move(out));
}

#endif /* IMA_HPP */
