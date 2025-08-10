#pragma once
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>
#include <map>

class SymbolicEnv
{
public:
    struct MapSyms { std::string dom, val; };

    /* ── Map registration ─────────────────────────────────────────────── */
    const MapSyms& declareMap(const std::string& base)
    {
        auto& slot = maps[base];
        if (slot.dom.empty()) {
            slot.dom = "Dom_" + base;
            slot.val = "Val_" + base;
        }
        return slot;
    }
    bool           isMap (const std::string& b) const { return maps.count(b); }
    const MapSyms& getMap(const std::string& b) const { return maps.at(b);    }

    /* ── Scalar symbol management (SSA + fresh) ───────────────────────── */
    const std::string& symFor(const std::string& var)
    {
        auto [it, inserted] = scalars.emplace(var, "");
        if (inserted) {
            it->second          = "x" + std::to_string(++fresh);
            order.push_back(it->second);
            id2var_[it->second] = var;
        }
        return it->second;
    }

    const std::string& bumpScalar(const std::string& var)
    {
        auto& id = scalars[var];
        id = "x" + std::to_string(++fresh);
        order.push_back(id);
        id2var_[id] = var;
        return scalars[var];
    }

    std::string freshSym(const std::string& tag)
    {
        std::string id = "x" + std::to_string(++fresh);
        order.push_back(id);
        id2var_[id] = tag;  // still useful when back-mapping
        return id;
    }

    /* ── Constraints & warnings ───────────────────────────────────────── */
    void addPredicate(const std::string& p) {
        if (!p.empty()) { preds.push_back(p); names.push_back("c" + std::to_string(++pc)); }
    }
    void addWarning  (const std::string& w) { if (!w.empty()) warnings.push_back(w); }
    const std::vector<std::string>& getWarnings() const { return warnings; }

    /* ── SMT-LIB serialisation ────────────────────────────────────────── */
    // Default: ask only for the model (no unsat-core request → no warning on SAT)
    std::string toSMTLib(bool footer = true) const
    {
        return emitSmt(/*askCore=*/false, /*askModel=*/true, footer);
    }

    // When debugging UNSAT: use this version to request the unsat core.
    // Note: Z3 will complain if the problem is SAT (that's expected).
    std::string toSMTLibWithUnsatCore(bool footer = true) const
    {
        return emitSmt(/*askCore=*/true, /*askModel=*/false, footer);
    }

    const std::unordered_map<std::string,std::string>& var2id() const { return scalars; }
    const std::unordered_map<std::string,std::string>& id2var() const { return id2var_; }

private:
    std::string emitSmt(bool askCore, bool askModel, bool footer) const
    {
        std::ostringstream out;
        out << "(set-logic ALL)\n";
        if (askModel) out << "(set-option :produce-models true)\n";
        if (askCore)  out << "(set-option :produce-unsat-cores true)\n";
        out << '\n';

        for (const auto& w : warnings) out << "; WARN: " << w << "\n";
        if (!warnings.empty()) out << '\n';

        for (const auto& id : order)
            out << "(declare-fun " << id << " () String)\n";
        if (!order.empty()) out << '\n';

        for (const auto& [base, ms] : maps) {
            out << "(declare-const " << ms.dom << " (Array String Bool))\n";
            out << "(declare-const " << ms.val << " (Array String String))\n\n";
        }

        for (size_t i=0;i<preds.size();++i)
            out << "(assert (! " << preds[i] << " :named " << names[i] << "))\n";

        if (footer) {
            out << "\n(check-sat)\n";
            if (askCore)  out << "(get-unsat-core)\n";
            if (askModel) out << "(get-model)\n";
        }
        return out.str();
    }

    // scalars
    std::unordered_map<std::string,std::string> scalars; // var -> xN
    std::unordered_map<std::string,std::string> id2var_;  // xN  -> var/tag
    std::vector<std::string>                    order;    // decl order
    std::vector<std::string>                    preds;
    std::vector<std::string>                    names;
    std::vector<std::string>                    warnings;
    int                                         fresh = 0;
    mutable int                                 pc = 0;

    // maps
    std::map<std::string,MapSyms>               maps;
};
