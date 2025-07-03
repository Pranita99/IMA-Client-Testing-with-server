// ──────────────────────────────────────────────────────────────────────────
// Symbolic/SymbolicEnv.hpp
// ──────────────────────────────────────────────────────────────────────────
#pragma once
#include <string>
#include <unordered_map>
#include <vector>
#include <sstream>

/*  A *very* small “symbol table” that maps each program-level
 *  variable name to one fresh SMT-id (x1, x2, …) **once per path**.
 *  The class also collects raw predicates and can emit a full
 *  self-contained SMT-LIB script.
 */
class SymbolicEnv
{
public:
    /* ---------------------------------------------------------------
     * 1.  Bind or look-up the SMT identifier for a variable.
     *     On first sighting we allocate a fresh xN.
     * --------------------------------------------------------------*/
    const std::string& symFor(const std::string& var)
    {
        auto [it, inserted] = env.emplace(var, "");
        if (inserted) {
            it->second = "x" + std::to_string(++freshCounter);
            insertionOrder.push_back(it->second);              // keep order
        }
        return it->second;
    }

    /* ---------------------------------------------------------------
     * 2.  Add a predicate already in valid SMT-LIB syntax.
     * --------------------------------------------------------------*/
    void addPredicate(const std::string& p)
    {
        if (!p.empty()) predicates.push_back(p);
    }

    /* ---------------------------------------------------------------
     * 3.  Serialise a complete SMT-LIB file (optionally omit footer).
     * --------------------------------------------------------------*/
    std::string toSMTLib(bool withFooter = true) const
    {
        std::ostringstream out;

        /* a) declare every xN that occurred in source order */
        for (const auto& id : insertionOrder)
            out << "(declare-fun " << id << " () String)\n";

        /* b) one-shot declarations for the helper functions that
               may occur inside predicates                                   */
        static const char* extra[] = {
            "(declare-fun input         (String)           String)",
            "(declare-fun mapped_value  (String String)    String)",
            "(declare-fun dom           (String)           String)",
            "(declare-fun not_in        (String String)    Bool)",
            "(declare-fun in_dom        (String String)    Bool)",
            "(declare-fun in            (String String)    Bool)",
            "(declare-fun and_operator  (Bool Bool)        Bool)",
            "(declare-fun getMapAtMatch (String String)    String)",
            "(declare-fun is_false      (Bool)             Bool)",
            "(declare-fun is_true       (Bool)             Bool)"
        };
        for (auto l : extra) out << l << '\n';

        /* c) path constraints */
        for (const auto& p : predicates)
            out << "(assert " << p << ")\n";

        /* d) optional footer to make file immediately solvable */
        if (withFooter)
            out << "(check-sat)\n(get-model)\n";

        return out.str();
    }

    /* ---------------------------------------------------------------
     * 4.  Public read-only access – used by run_se_driver for
     *     pretty-printing human-friendly literals.
     * --------------------------------------------------------------*/
    const std::unordered_map<std::string,std::string>& var2id() const
    { return env; }

    /* ---------------------------------------------------------------
     * 5.  Helpers & reset (mostly for unit tests).
     * --------------------------------------------------------------*/
    std::size_t numSymbols()    const { return env.size(); }
    std::size_t numPredicates() const { return predicates.size(); }

    void clear()
    {
        env.clear();
        insertionOrder.clear();
        predicates.clear();
        freshCounter = 0;
    }

private:
    /* implementation state -----------------------------------------*/
    std::unordered_map<std::string,std::string> env;   // var  →  xN
    std::vector<std::string>          insertionOrder;  // stable order
    std::vector<std::string>          predicates;      // collected (assert …)
    int                               freshCounter = 0;
};
