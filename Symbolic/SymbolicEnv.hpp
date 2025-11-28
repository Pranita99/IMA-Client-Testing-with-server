#pragma once
#include <string>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <map>

/**
 * SymbolicEnv — extended with staged pinning + model binding support.
 * ✅ Drop-in replacement for your old version.
 * Adds:
 *   - bindModelValues()
 *   - hasValue(), getValue()
 */
class SymbolicEnv
{
public:
    struct MapSyms {
        std::string dom;   // (Array String Bool)
        std::string val;   // (Array String String)
        std::string bval;  // (Array String (Array String Bool)) -- declared iff has_bucket
        bool        has_bucket = false;
    };

    /* ── Map registration ─────────────────────────────────────────────── */
    const MapSyms& declareMap(const std::string& base)
    {
        auto& slot = maps[base];
        if (slot.dom.empty()) {
            slot.dom  = "Dom_"  + base;
            slot.val  = "Val_"  + base;
            slot.bval = "BVal_" + base;
        }
        return slot;
    }
    bool           isMap (const std::string& b) const { return maps.count(b); }
    const MapSyms& getMap(const std::string& b) const { return maps.at(b);    }

    // When nested map access appears, ensure bucket view exists for this map state
    void ensureBucketVal(const std::string& base) {
        auto& slot = maps[base];
        if (slot.dom.empty()) {
            slot.dom  = "Dom_"  + base;
            slot.val  = "Val_"  + base;
            slot.bval = "BVal_" + base;
        }
        slot.has_bucket = true;
    }

    // Declare uninterpreted functions (dedup by full declare-fun line)
    void declareUF(const std::string& decl_line) {
        if (!decl_line.empty()) uf_decls.insert(decl_line);
    }

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
        id2var_[id] = tag;
        return id;
    }

    /* ── Pinning & staged solving ─────────────────────────────────────── */
    // Record a concrete value for an existing SSA (used in staged/concolic runs).
    void pinValue(const std::string& ssa, const std::string& concrete) {
        if (!ssa.empty()) pinnedValues[ssa] = concrete;
    }

    // NEW: bind Z3 model values into environment mid-run
    void bindModelValues(const std::unordered_map<std::string,std::string>& model) {
        for (const auto& [ssa, val] : model) {
            if (!ssa.empty()) pinnedValues[ssa] = val;
        }
    }

    // Check if variable currently has a concrete value (via pinned SSA)
    bool hasValue(const std::string& var) const {
        auto it = scalars.find(var);
        if (it == scalars.end()) return false;
        return pinnedValues.find(it->second) != pinnedValues.end();
    }

    // Get the concrete value of a variable if available
    std::string getValue(const std::string& var) const {
        auto it = scalars.find(var);
        if (it == scalars.end()) return "";
        auto jt = pinnedValues.find(it->second);
        return (jt != pinnedValues.end()) ? jt->second : "";
    }

    // Helper to lookup last SSA name for a base variable without bumping
    std::string peekScalar(const std::string& var) const {
        auto it = scalars.find(var);
        return (it == scalars.end()) ? "" : it->second;
    }

    /* ── Constraints & warnings ───────────────────────────────────────── */
    void addPredicate(const std::string& p) {
        if (!p.empty()) { preds.push_back(p); names.push_back("c" + std::to_string(++pc)); }
    }
    void addWarning  (const std::string& w) { if (!w.empty()) warnings.push_back(w); }
    const std::vector<std::string>& getWarnings() const { return warnings; }
    const std::vector<std::string>& getPredNames() const { return names; }

    /* ── SMT-LIB serialisation ────────────────────────────────────────── */
    std::string toSMTLib() const { return emitSmtBody({}, false); }

    // Overload that includes pinned SSA equalities
    std::string toSMTLib(const std::map<std::string,std::string>& extraPins) const {
        return emitSmtBody(extraPins, true);
    }

    const std::unordered_map<std::string,std::string>& var2id() const { return scalars; }
    const std::unordered_map<std::string,std::string>& id2var() const { return id2var_; }

private:
    static std::string quoteString(const std::string& s) {
        std::string r; r.reserve(s.size()+2); r.push_back('"');
        for (char c : s) {
            if (c=='"') r += "\\\"";
            else r.push_back(c);
        }
        r.push_back('"');
        return r;
    }

    std::string emitSmtBody(const std::map<std::string,std::string>& extraPins, bool includePins) const
    {
        std::ostringstream out;
        out << "(set-logic ALL)\n";
        out << "(set-option :produce-models true)\n";
        out << '\n';

        for (const auto& w : warnings) out << "; WARN: " << w << "\n";
        if (!warnings.empty()) out << '\n';

        // SSA scalars (stable order)
        for (const auto& id : order)
            out << "(declare-fun " << id << " () String)\n";
        if (!order.empty()) out << '\n';

        // Maps: Dom + Val always; BVal only if needed
        for (const auto& [base, ms] : maps) {
            out << "(declare-const " << ms.dom  << " (Array String Bool))\n";
            out << "(declare-const " << ms.val  << " (Array String String))\n";
            if (ms.has_bucket) {
                out << "(declare-const " << ms.bval << " (Array String (Array String Bool)))\n";
            }
            out << '\n';
        }

        // Uninterpreted functions
        for (const auto& d : uf_decls) out << d << "\n";
        if (!uf_decls.empty()) out << '\n';

        // Predicates as Bool consts
        for (size_t i = 0; i < preds.size(); ++i) {
            out << "(declare-const " << names[i] << " Bool)\n";
            out << "(assert (= " << names[i] << " " << preds[i] << "))\n";
        }

        // Append pinned equalities if any
        if (includePins) {
            for (const auto& kv : pinnedValues) {
                out << "(assert (= " << kv.first << " " << quoteString(kv.second) << "))\n";
            }
            for (const auto& kv : extraPins) {
                out << "(assert (= " << kv.first << " " << quoteString(kv.second) << "))\n";
            }
        }

        return out.str();
    }

    // scalars
    std::unordered_map<std::string,std::string> scalars; // var -> xN
    std::unordered_map<std::string,std::string> id2var_; // xN  -> var/tag
    std::vector<std::string>                    order;   // decl order
    std::vector<std::string>                    preds;
    std::vector<std::string>                    names;
    std::vector<std::string>                    warnings;
    int                                         fresh = 0;
    mutable int                                 pc = 0;

    // maps / UFs
    std::map<std::string,MapSyms>               maps;
    std::unordered_set<std::string>             uf_decls;

    // pinned SSA → concrete value map
    std::map<std::string,std::string>           pinnedValues;
};
