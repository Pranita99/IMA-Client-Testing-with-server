// Tools/run_se_driver.cpp
// -----------------------------------------------------------
// Build one test-path, emit plain SMT and a pretty literal
// annotated copy *without duplicate declarations*.
// -----------------------------------------------------------
#include "../ast.hpp"
#include "../IMA.hpp"
#include "../Symbolic/SEVisitor.hpp"
#include "../Symbolic/SymbolicEnv.hpp"

#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <unordered_set>

#ifndef PATH_FILE
#  error "compile with -DPATH_FILE"
#endif
#include PATH_FILE    // brings in  Program clientProgram  &  Spec spec

/* ---------- helpers --------------------------------------------------------- */
static void writeFile(const std::string& f, const std::string& txt)
{
    std::ofstream(f) << txt;
}

/* deterministic, human-friendly literal for a symbolic id */
static std::string prettyLit(const std::string& id,
                             const std::string& pathId)
{
    if (id.rfind('x', 0) != 0)         // keep helper ids etc. untouched
        return id;

    static const char* stem[] = {"user", "pass", "tok", "lit"};
    unsigned n = std::stoi(id.substr(1));      // x17 → 17
    return "\"" + std::string(stem[n % 3]) + '_' + pathId + '"';
}

/* remove duplicate (declare-fun …) lines — keeps only the first one */
static std::string dedupDecls(const std::string& src)
{
    std::istringstream in(src);
    std::ostringstream out;
    std::unordered_set<std::string> seen;

    std::string line;
    const std::regex declRE(R"(\(declare-fun\s+([^\s]+))");

    while (std::getline(in, line))
    {
        std::smatch m;
        if (std::regex_search(line, m, declRE))
        {
            const std::string id = m[1];
            if (!seen.insert(id).second)          // already had it → skip
                continue;
        }
        out << line << '\n';
    }
    return out.str();
}

/* ---------- main ------------------------------------------------------------ */
int main(int argc, char** argv)
{
    /* Basename & stable path-id (e.g. webApp2_path3) */
    const std::string base   = (argc >= 2) ? argv[1] : "constraints";
    const std::string pathId = base.substr(base.find_last_of("/\\") + 1);

    /* 1 — mutate with IMA ---------------------------------------------------- */
    SymbolTable sym;  TypeMap tmap;
    Program mutant = IMA(clientProgram, spec, sym, tmap);

    /* 2 — symbolic execution ------------------------------------------------- */
    SymbolicEnv sigma;
    SEVisitor   se(sigma);
    mutant.accept(se);

    /* 3 — plain SMT-LIB (unchanged) ----------------------------------------- */
    std::string smt = "(set-logic ALL)\n" + sigma.toSMTLib(/*withFooter*/true);
    writeFile(base + ".smt2", smt);

    /* 4 — pretty copy (literal substitution + dedup) ------------------------ */
    std::string pretty = smt;
    for (const auto& [var, id] : sigma.var2id())
    {
        const std::regex rx("\\b" + id + "\\b");
        pretty = std::regex_replace(pretty, rx, prettyLit(id, pathId));
    }
    pretty = dedupDecls(pretty);
    writeFile(base + ".pretty.smt2", pretty);

    std::cout << "✓ wrote  "      << base << ".smt2  and  "
              << base << ".pretty.smt2\n";
    return 0;
}
