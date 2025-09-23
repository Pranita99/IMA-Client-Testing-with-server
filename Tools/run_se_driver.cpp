#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <iterator>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <string>
#include <vector>
#include <iomanip>

#include "../ast.hpp"
#include "../IMA.hpp"

#ifndef PATH_FILE
#   error "compile with  -DPATH_FILE=\"<test-path>.cpp\""
#endif

#include PATH_FILE

// Forward declarations
struct SymbolTable;
struct TypeMap;
Program IMA(const Program& clientProgram,
            const Spec&    spec,
            SymbolTable&   sym,
            TypeMap&       tmap);

#include "../Symbolic/SEVisitor.hpp"
#include "../Symbolic/SymbolicEnv.hpp"
#include "../PrintVisitor.hpp"

// ---------- utils ----------------------------------------------------------
static void writeFile(const std::string& f, const std::string& txt) {
    std::ofstream out(f.c_str(), std::ios::binary);
    out.write(txt.data(), static_cast<std::streamsize>(txt.size()));
}

static std::string jsonEscape(const std::string& s) {
    std::string out; out.reserve(s.size() + 8);
    out.push_back('"');
    for (size_t i=0;i<s.size();++i) {
        const unsigned char c = static_cast<unsigned char>(s[i]);
        switch (c) {
            case '\\': out += "\\\\"; break;
            case '"':  out += "\\\""; break;
            case '\b': out += "\\b";  break;
            case '\f': out += "\\f";  break;
            case '\n': out += "\\n";  break;
            case '\r': out += "\\r";  break;
            case '\t': out += "\\t";  break;
            default:
                if (c < 0x20) {
                    char buf[7]; std::snprintf(buf, sizeof(buf), "\\u%04x", (unsigned)c);
                    out += buf;
                } else out.push_back((char)c);
        }
    }
    out.push_back('"');
    return out;
}

static inline bool isQuoted(const std::string& s) {
    return s.size() >= 2 && s.front()=='"' && s.back()=='"';
}

// Convert a raw Z3 token into a JSON string literal
static std::string asJsonString(const std::string& raw) {
    if (raw.empty())               return "\"\"";
    if (isQuoted(raw))             return raw;         // already a quoted string
    if (raw=="true"||raw=="false") return raw;        // booleans stay bare
    // For SSA Strings (x*) treat any bare atom as a string:
    return jsonEscape(raw);
}

// If Z3 returns "", fill a stable placeholder so the runner always has a value
static std::string nonEmptyOrAuto(const std::string& ssaId, const std::string& jsonLit) {
    return (jsonLit == "\"\"") ? jsonEscape("auto_" + ssaId) : jsonLit;
}

static std::string dedupDecls(const std::string& src) {
    std::istringstream in(src);
    std::ostringstream out;
    std::unordered_set<std::string> seen_fun, seen_const;
    std::string line;

    const std::regex declFunRE(R"Z3(\(declare-fun\s+([^\s\)]+))Z3");
    const std::regex declConstRE(R"Z3(\(declare-const\s+([^\s\)]+))Z3");

    while (std::getline(in, line)) {
        std::smatch m;
        if (std::regex_search(line, m, declFunRE)) {
            const std::string id = m[1];
            if (!seen_fun.insert(id).second) continue;
        } else if (std::regex_search(line, m, declConstRE)) {
            const std::string id = m[1];
            if (!seen_const.insert(id).second) continue;
        }
        out << line << '\n';
    }
    return out.str();
}

static std::string runCmdCapture(const std::string& cmd) {
    const std::string tmp = "build/.z3_stdout.txt";
#if defined(_WIN32) || defined(_WIN64)
    const std::string wrapped = cmd + " > \"" + tmp + "\"";
#else
    const std::string wrapped = cmd + " > \"" + tmp + "\" 2>&1";
#endif
    (void)std::system(wrapped.c_str());

    std::ifstream in(tmp.c_str(), std::ios::binary);
    if (!in) return std::string();
    return std::string((std::istreambuf_iterator<char>(in)),
                       std::istreambuf_iterator<char>());
}

static void printWithLineNumbers(const std::string& text) {
    std::istringstream in(text);
    std::string line; size_t ln = 1;
    std::cout << "===== SMT-LIB sent to Z3 =====\n";
    while (std::getline(in, line)) {
        std::cout << std::setw(5) << ln++ << "  " << line << "\n";
    }
    std::cout << "===== END SMT-LIB =====\n\n";
}

static std::string slurpFile(const std::string& p) {
    std::ifstream f(p.c_str(), std::ios::binary);
    return f ? std::string((std::istreambuf_iterator<char>(f)),
                           std::istreambuf_iterator<char>()) : std::string();
}

// Parse ((id value) ...) from Z3's (get-value ...) output
static std::unordered_map<std::string, std::string>
parseGetValuePairs(const std::string& z3out) {
    std::unordered_map<std::string, std::string> id2val;
    // (x "str") or (x !0!) or (c1 true)
    std::regex pair_re(R"(\(\s*([^\s\(\)]+)\s+("([^"\\]|\\.)*"|[^\s\(\)]+)\s*\))");

    auto begin = std::sregex_iterator(z3out.begin(), z3out.end(), pair_re);
    auto end   = std::sregex_iterator();

    for (auto it = begin; it != end; ++it) {
        const std::smatch& m = *it;
        std::string id = m[1].str();
        std::string val = m[2].str();
        id2val[id] = val;
    }
    return id2val;
}

// Data structures for CTC generation
struct StepRec {
    int         step;
    std::string role;
    std::string var;
    std::string value;  // JSON-literal string (already quoted)
    std::string at;
};
struct CallCheck {
    std::string at;
    bool        pre;
    bool        post;
};

// ---------- main -----------------------------------------------------------
int main(int argc, char** argv)
{
    // CLI: run_se_driver [base] [--show-smt] [--show-z3] [--show-json] [--fullmodel]
    bool show_smt = false, show_z3 = false, show_json = false, want_fullmodel = false;

    std::string base = (argc >= 2 && argv[1][0] != '-') ? argv[1] : "constraints";
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--show-smt")   show_smt   = true;
        else if (a == "--show-z3")    show_z3    = true;
        else if (a == "--show-json")  show_json  = true;
        else if (a == "--fullmodel")  want_fullmodel = true;
    }
    const std::string pathId = base.substr(base.find_last_of("/\\") + 1);

    // 1) IMA → mutated program
    SymbolTable sym;    TypeMap tmap;
    Program mutant = IMA(clientProgram, spec, sym, tmap);

    // 2) Symbolic execution → sigma
    SymbolicEnv sigma;
    for (const auto& kv : tmap.mapping) {
        if (dynamic_cast<MapType*>(kv.second) != 0)
            sigma.declareMap(kv.first);
    }
    SEVisitor se(sigma);
    mutant.accept(se);

    const auto& var2id    = sigma.var2id();
    const auto& id2var    = sigma.id2var();
    const auto& predNames = sigma.getPredNames(); // include cN in get-value

    // 3) SMT body
    std::string smt_body = sigma.toSMTLib();

    // 4) SMT footer — ask for SSA ids + cN
    std::ostringstream smt_footer;
    smt_footer << "\n(set-option :model.partial true)\n";
    smt_footer << "(set-option :model.compact false)\n";
    smt_footer << "(check-sat)\n";
    smt_footer << "(get-value (";
    for (const auto& [var, id] : var2id)  smt_footer << id   << " ";
    for (const auto& name    : predNames) smt_footer << name << " ";
    smt_footer << "))\n";

    const std::string smt_final = smt_body + smt_footer.str();
    writeFile(base + ".smt2", smt_final);

    // 3½) map CSV (debug)
    {
        std::ostringstream csv;
        csv << "program,id\n";
        for (const auto& [program_var, ssa_id] : var2id)
            csv << program_var << ',' << ssa_id << '\n';
        writeFile(base + ".map.csv", csv.str());
    }

    // 4) Pretty SMT (dedup comments) — file only
    std::string pretty = smt_body;
    for (const auto& [var, id] : var2id) {
        const std::regex rx_comment(";.*\\b" + id + "\\b");
        pretty = std::regex_replace(pretty, rx_comment, std::string("$& \xE2\x86\x90 ") + var);
    }
    pretty = dedupDecls(pretty);
    writeFile(base + ".pretty.smt2", pretty);

    if (show_smt) printWithLineNumbers(smt_final);

    // 5) Run Z3 for (check-sat) + (get-value …)
    const std::string z3cmd = std::string("z3 -smt2 \"") + base + ".smt2\"";
    std::string z3out = runCmdCapture(z3cmd);
    if (show_z3) {
        std::cout << "===== Z3 (get-value) =====\n" << z3out << "\n";
    }

    if (z3out.find("(error") != std::string::npos) {
        std::cerr << "Z3 reported an error. Full output:\n" << z3out << "\n";
    }
    if (z3out.find("unsat") != std::string::npos) {
        std::cerr << "WARN: Z3 reported UNSAT for path " << pathId << std::endl;
        writeFile(base + ".model.json", "{ \"status\": \"unsat\" }");
        writeFile(base + ".ctc.json",   "{ \"status\": \"unsat\" }");
        return 1;
    }

    // 5b) Optionally capture FULL model (arrays/maps/UFs) into a file
    if (want_fullmodel) {
        writeFile(base + ".getmodel.smt2", smt_body + "\n(check-sat)\n(get-model)\n");
        std::string fullModel = runCmdCapture(std::string("z3 -smt2 \"") + base + ".getmodel.smt2\"");
        writeFile(base + ".fullmodel.txt", fullModel);
    }

    // 6) Parse model values
    std::unordered_map<std::string,std::string> id2val = parseGetValuePairs(z3out);
    const bool sat = (z3out.find("sat") != std::string::npos);
    if (sat && id2val.empty()) {
        std::cerr << "WARN: Z3 reported SAT but model parsing found no pairs. Raw output follows:\n---\n"
                  << z3out << "\n---\n";
    }

    // Helpers for JSON emission
    auto getJsonForSSA = [&](const std::string& ssa)->std::string {
        auto it = id2val.find(ssa);
        std::string raw = (it != id2val.end()) ? it->second : "\"\"";
        std::string j   = asJsonString(raw);        // ensure quoted if needed
        return nonEmptyOrAuto(ssa, j);              // force non-empty string for artifacts
    };

    // 7) Build step records from the mutated program
    std::vector<StepRec> steps;
    int stepCounter = 0;
    std::string currentCall;

    for (const auto& S : mutant.statements) {
        if (const auto* call = dynamic_cast<const FuncCallStmt*>(S.get())) {
            const std::string& name = call->call->name;
            if (name != "assume" && name != "assert") currentCall = name;
        } else if (const auto* a = dynamic_cast<const Assign*>(S.get())) {
            const std::string var = a->left->name;
            if (auto* fc = dynamic_cast<FuncCall*>(a->right.get())) {
                if (fc->name == "input") {
                    auto itId = var2id.find(var);
                    const std::string jval = (itId == var2id.end()) ? jsonEscape("") : getJsonForSSA(itId->second);
                    steps.push_back({++stepCounter, "input", var, jval, currentCall});
                } else if (fc->name == "fresh") {
                    auto itId = var2id.find(var);
                    const std::string jval = (itId == var2id.end()) ? jsonEscape("") : getJsonForSSA(itId->second);
                    steps.push_back({++stepCounter, "effect", var, jval, currentCall});
                }
            }
        }
    }

    // 8) Build checks array using c1..cN values (now queried)
    std::vector<CallCheck> checks;
    std::unordered_map<std::string, int> callCounts;
    int constraint_idx = 0;

    auto getBoolC = [&](int idx)->bool {
        auto it = id2val.find("c" + std::to_string(idx));
        return (it != id2val.end() && it->second == "true");
    };

    for (const auto& S : mutant.statements) {
        if (const auto* call = dynamic_cast<const FuncCallStmt*>(S.get())) {
            const std::string& name = call->call->name;
            if (name == "assume") {
                if (!checks.empty()) checks.back().pre  = getBoolC(++constraint_idx);
            } else if (name == "assert") {
                if (!checks.empty()) checks.back().post = getBoolC(++constraint_idx);
            } else {
                std::string at_tag = name + "#" + std::to_string(++callCounts[name]);
                checks.push_back({at_tag, false, false});
            }
        }
    }

    // 9) Emit model.json — always has non-empty JSON string values
    {
        std::ostringstream json;
        json << "{\n";
        json << "  \"path\": " << jsonEscape(pathId) << ",\n";
        json << "  \"vars\": {\n";

        bool first = true;
        for (const auto& [var, id] : var2id) {
            if (!first) json << ",\n";
            first = false;
            const std::string jval = getJsonForSSA(id);
            json << "    " << jsonEscape(var) << ": " << jval;
        }
        json << "\n  }\n}\n";
        writeFile(base + ".model.json", json.str());
    }

    // 10) Emit ctc.json (steps + checks)
    {
        std::ostringstream json;
        json << "{\n";
        json << "  \"path\": " << jsonEscape(pathId) << ",\n";
        json << "  \"steps\": [\n";
        for (size_t i = 0; i < steps.size(); ++i) {
            const StepRec& st = steps[i];
            json << "    { \"step\": " << st.step
                 << ", \"role\": " << jsonEscape(st.role)
                 << ", \"name\": " << jsonEscape(st.var)
                 << ", \"value\": " << st.value
                 << ", \"at\": " << jsonEscape(st.at) << " }";
            json << (i + 1 == steps.size() ? "\n" : ",\n");
        }
        json << "  ],\n";
        json << "  \"checks\": [\n";
        for (size_t i = 0; i < checks.size(); ++i) {
            const CallCheck& c = checks[i];
            json << "    { \"at\": " << jsonEscape(c.at)
                 << ", \"pre\": "  << (c.pre ? "true" : "false")
                 << ", \"post\": " << (c.post ? "true" : "false") << " }";
            json << (i + 1 == checks.size() ? "\n" : ",\n");
        }
        json << "  ]\n}\n";
        writeFile(base + ".ctc.json", json.str());
    }

    // 11) Emit simple text CTC
    {
        std::ostringstream txt;
        txt << "CTC for " << pathId << "\n---------------------------------\n";
        for (const auto& st : steps) {
            std::string v = st.value;
            if (isQuoted(v)) v = v.substr(1, v.size() - 2);
            txt << "Step " << st.step << "  [" << st.role << "]  "
                << st.var << " = " << (v.empty() ? "<empty>" : v)
                << "   @ " << st.at << "\n";
        }
        writeFile(base + ".ctc.txt", txt.str());
    }

    if (show_json) {
        std::cout << "===== model.json =====\n" << slurpFile(base + ".model.json") << "\n";
        std::cout << "===== ctc.json =====\n"   << slurpFile(base + ".ctc.json")   << "\n";
    }

    std::cout << "✓ wrote  " << base << ".smt2, "
              << base << ".pretty.smt2, "
              << base << ".map.csv, "
              << base << ".model.json, "
              << base << ".ctc.json, "
              << base << ".ctc.txt"
              << (want_fullmodel ? ", " + base + ".fullmodel.txt" : "")
              << "\n";
    return 0;
}
