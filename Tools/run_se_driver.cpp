// ───────────────────────────────────────────────────────────
//  Tools/run_se_driver.cpp
//  (batch driver – ONE executable per test‑path)
// ───────────────────────────────────────────────────────────
#include "../ast.hpp"
#include "../IMA.hpp"
#include "../Symbolic/SEVisitor.hpp"
#include "../Symbolic/SymbolicEnv.hpp"
#include "../PrintVisitor.hpp"

#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <unordered_set>
#include <iomanip>              // ➊ new – pretty CSV

#ifndef PATH_FILE
#   error "compile with  -DPATH_FILE=\"<test-path>.cpp\""
#endif
#include PATH_FILE              // brings in  Program clientProgram,  Spec spec

/* ---------- helpers ------------------------------------------------------- */
static void writeFile(const std::string& f, const std::string& txt)
{
    std::ofstream(f).write(txt.data(), static_cast<std::streamsize>(txt.size()));
}

/* deterministic, human‑friendly literal for a symbolic id */
static std::string prettyLit(const std::string& id,
                             const std::string& pathId)
{
    if (id.rfind('x', 0) != 0)                  // keep helper‑ids untouched
        return id;

    static const char* stem[] = {"user", "pass", "tok", "lit"};
    unsigned n = std::stoi(id.substr(1));       //  x17 → 17
    return "\"" + std::string(stem[n % 4]) + '_' + pathId + '"';
}

/* drop duplicate (declare‑fun …) lines – keep the first one only */
static std::string dedupDecls(const std::string& src)
{
    std::istringstream in(src);
    std::ostringstream out;
    std::unordered_set<std::string> seen;

    std::string line;
    static const std::regex declRE(R"(\(declare-fun\s+([^\s]+))");

    while (std::getline(in, line))
    {
        std::smatch m;
        if (std::regex_search(line, m, declRE))
        {
            const std::string id = m[1];
            if (!seen.insert(id).second)        // seen before → skip
                continue;
        }
        out << line << '\n';
    }
    return out.str();
}

/* ---------- main ---------------------------------------------------------- */
int main(int argc, char** argv)
{
    /* Basename & stable path‑id  (e.g. webApp2_path3) */
    const std::string base   = (argc >= 2) ? argv[1] : "constraints";
    const std::string pathId = base.substr(base.find_last_of("/\\") + 1);

    /* 1 ─ run IMA to obtain the mutated program */
    SymbolTable sym;    TypeMap tmap;
    Program mutant = IMA(clientProgram, spec, sym, tmap);

    /* 2 ─ symbolic execution → constraints */
    SymbolicEnv sigma;

    /* register every MapType that IMA discovered */
    for (const auto& kv : tmap.mapping)
        if (dynamic_cast<MapType*>(kv.second) != nullptr)
            sigma.declareMap(kv.first);

    SEVisitor se(sigma);
    mutant.accept(se);

    /* 2 ½ ─ remember var↔id table once and for all */
    const auto& var2id = sigma.var2id();        // ➋ new

    /* 3 ─ raw SMT‑LIB   */
    std::string smt = sigma.toSMTLib(/*footer*/true);
    writeFile(base + ".smt2", smt);

    /* 3 ½ ─ emit CSV so we can walk  model → id → program‑var */
    {
        std::ofstream csv(base + ".map.csv");
        csv << "program,id\n";
        for (const auto& [v,id] : var2id)
            csv << std::quoted(v) << ',' << id << '\n';
    }

    /* 4 ─ pretty SMT (substitute literals, dedup decls, inline comments) */
    std::string pretty = smt;
    for (const auto& [var,id] : var2id)
    {
        const std::regex rx("\\b" + id + "\\b");
        pretty = std::regex_replace(pretty, rx, prettyLit(id, pathId));
    }

    /* ➌ add “← username” comments so the mapping is visible in‑file */
    for (const auto& [var,id] : var2id)
    {
        const std::regex rx_comment(";.*\\b" + id + "\\b");
        pretty = std::regex_replace(pretty, rx_comment,
                                    "$& ← " + var);
    }

    pretty = dedupDecls(pretty);
    writeFile(base + ".pretty.smt2", pretty);

    std::cout << "✓ wrote  " << base << ".smt2, "          //
              << base << ".pretty.smt2 and "                //
              << base << ".map.csv\n";
    return 0;
}
