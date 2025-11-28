// Tools/run_se_driver.cpp
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
    out.push_back('"'); return out;
}
static inline bool isQuoted(const std::string& s) {
    return s.size() >= 2 && s.front()=='"' && s.back()=='"';
}
static std::string unquote(std::string s) {
    return isQuoted(s) ? s.substr(1, s.size()-2) : s;
}
static std::string asJsonString(const std::string& raw) {
    if (raw.empty())               return "\"\"";
    if (isQuoted(raw))             return raw;
    if (raw=="true"||raw=="false") return raw;
    return jsonEscape(raw);
}
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
    int rc = std::system(wrapped.c_str());
    (void)rc;
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

/*───────────────────────────────────────────────────────────────────────────*
 * Test-State "lens" CSV + probes (tiny & generic)
 *───────────────────────────────────────────────────────────────────────────*/

struct LensRow {
    std::string map;
    std::string keyType;
    std::string valType;
    std::string getOneTemplate;
    std::string getKeysTemplate;
    std::string setOneTemplate;
    std::string notes;
};

// tiny CSV splitter supporting quoted fields
static std::vector<std::vector<std::string>> parseCsv(const std::string& text) {
    std::vector<std::vector<std::string>> rows;
    std::vector<std::string> row;
    std::string cur; bool inq=false;
    for (size_t i=0;i<text.size();++i) {
        char c=text[i];
        if (inq) {
            if (c=='"' && i+1<text.size() && text[i+1]=='"'){cur.push_back('"');++i;}
            else if (c=='"'){inq=false;}
            else cur.push_back(c);
        } else {
            if (c==','){row.push_back(cur);cur.clear();}
            else if (c=='\n'){row.push_back(cur);rows.push_back(row);row.clear();cur.clear();}
            else if (c=='"'){inq=true;}
            else cur.push_back(c);
        }
    }
    if (!cur.empty() || !row.empty()){row.push_back(cur);rows.push_back(row);}
    return rows;
}
static std::string replaceAll(std::string s, const std::string& a, const std::string& b){
    size_t pos=0;
    while((pos=s.find(a,pos))!=std::string::npos){ s.replace(pos,a.size(),b); pos+=b.size(); }
    return s;
}
static std::string curlGET(const std::string& url) {
    return runCmdCapture(std::string("curl -s \"") + url + "\"");
}
static std::string curlPOST_json(const std::string& url, const std::string& body) {
    std::string cmd = std::string("curl -s -X POST -H \"Content-Type: application/json\" --data '")
                      + body + "' \"" + url + "\"";
    return runCmdCapture(cmd);
}

// emit skeleton once (never overwrite a filled CSV)
static void emitStateLensSkeleton(const TypeMap& tmap, const std::string& base) {
    const std::string skel = base + ".state_lens.skel.csv";
    std::ifstream check1((base + ".state_lens.csv").c_str());
    std::ifstream check2(skel.c_str());
    if (check1.good() || check2.good()) return; // already present

    std::ostringstream out;
    out << "# map,key_type,value_type,GET_one_template,GET_keys_template,SET_one_template,notes\n";
    out << "# Use {key} and {value} placeholders in templates.\n";
    for (const auto& kv : tmap.mapping) {
        if (dynamic_cast<MapType*>(kv.second) == nullptr) continue;
        const std::string& M = kv.first;
        out << M << ",String,String,"
            << "http://localhost:8089/state/" << M << "?key={key},"
            << "http://localhost:8089/state/" << M << "/keys,"
            << "http://localhost:8089/state/" << M << "/set?key={key}&value={value},"
            << "\"\"\n";
    }
    writeFile(skel, out.str());
}

// load user-filled lens if available
static std::vector<LensRow> loadStateLens(const std::string& base) {
    const std::string file = base + ".state_lens.csv";
    std::ifstream in(file.c_str(), std::ios::binary);
    if (!in) return {};
    std::string txt((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
    auto rows = parseCsv(txt);
    std::vector<LensRow> out;
    for (const auto& r : rows) {
        if (r.empty() || (!r[0].empty() && r[0][0]=='#')) continue;
        if (r[0] == "MAIN") continue; // reserved for business rows
        LensRow L{};
        if (r.size()>0) L.map             = r[0];
        if (r.size()>1) L.keyType         = r[1];
        if (r.size()>2) L.valType         = r[2];
        if (r.size()>3) L.getOneTemplate  = r[3];
        if (r.size()>4) L.getKeysTemplate = r[4];
        if (r.size()>5) L.setOneTemplate  = r[5];
        if (r.size()>6) L.notes           = r[6];
        if (!L.map.empty()) out.push_back(L);
    }
    return out;
}
static const LensRow* findLens(const std::vector<LensRow>& L, const std::string& map) {
    for (size_t i=0;i<L.size();++i) if (L[i].map == map) return &L[i];
    return nullptr;
}

/*───────────────────────────────────────────────────────────────────────────*
 * Optional MAIN API rows (same CSV)
 * Format:  MAIN,Name,Method,URL_Template,BodyTemplate(optional),Notes
 *───────────────────────────────────────────────────────────────────────────*/
struct MainRow { std::string name, method, url, body; };
static std::vector<MainRow> loadMainRows(const std::string& csvPath) {
    std::vector<MainRow> v;
    std::ifstream in(csvPath.c_str(), std::ios::binary);
    if (!in) return v;
    std::string txt((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
    auto rows = parseCsv(txt);
    for (const auto& r : rows) {
        if (r.empty()) continue;
        if (r[0] != "MAIN") continue;
        MainRow m{};
        if (r.size()>1) m.name   = r[1];
        if (r.size()>2) m.method = r[2];
        if (r.size()>3) m.url    = r[3];
        if (r.size()>4) m.body   = r[4];
        if (!m.name.empty()) v.push_back(m);
    }
    return v;
}
static std::string expandNV(std::string templ, const std::string& name, const std::string& value) {
    size_t p = 0;
    while ((p = templ.find("{name}", p))  != std::string::npos) { templ.replace(p, 6, name);  p += name.size();  }
    p = 0;
    while ((p = templ.find("{value}", p)) != std::string::npos) { templ.replace(p, 7, value); p += value.size(); }
    return templ;
}
static const MainRow* findMain(const std::vector<MainRow>& M, const std::string& name) {
    for (size_t i=0;i<M.size();++i) if (M[i].name == name) return &M[i];
    return nullptr;
}

/*───────────────────────────────────────────────────────────────────────────*
 * Existing SE → SMT driver (+ probes) + staged mid-execution + run-ctc
 *───────────────────────────────────────────────────────────────────────────*/

// For CTC generation
struct StepRec { int step; std::string role, var, value, at; };
struct CallCheck { std::string at; bool pre, post; };

// For run report (CTC execution)
struct RunStep { int step; std::string at, kind; bool ok; std::string note; };

static bool run_ctc_once(const std::string& base,
                         const std::vector<LensRow>& lens,
                         const std::vector<MainRow>& mains,
                         std::vector<RunStep>& report)
{
    const std::string ctc = slurpFile(base + ".ctc.json");
    if (ctc.empty()) return false;

    const std::regex stepRE(
        R"STEP("step"\s*:\s*(\d+)[^}]*"role"\s*:\s*"([^"]+)"[^}]*"name"\s*:\s*"([^"]+)"[^}]*"value"\s*:\s*([^,}\n\r]+)[^}]*"at"\s*:\s*"([^"]*)")STEP",
        std::regex::ECMAScript
    );

    std::sregex_iterator it(ctc.begin(), ctc.end(), stepRE);
    std::sregex_iterator end;

    for (; it != end; ++it) {
        const int         step    = std::stoi((*it)[1].str());
        const std::string role    = (*it)[2].str();
        const std::string name    = (*it)[3].str();
        const std::string jval    = (*it)[4].str();
        const std::string at      = (*it)[5].str();
        const std::string value   = unquote(jval);

        std::string callName = at;
        const size_t hash = callName.find('#');
        if (hash != std::string::npos) callName.resize(hash);

        const MainRow* MR = (!callName.empty() ? findMain(mains, callName) : nullptr);
        if (MR && !MR->url.empty()) {
            const std::string url  = expandNV(MR->url,  name, value);
            const std::string body = expandNV(MR->body, name, value);
            bool ok = false; std::string note;

            if (MR->method.empty() || MR->method == "GET" || MR->method == "get") {
                ok   = !curlGET(url).empty();
                note = ok ? "MAIN GET ok" : "MAIN GET failed";
            } else {
                ok   = !curlPOST_json(url, body).empty();
                note = ok ? "MAIN POST ok" : "MAIN POST failed";
            }
            report.push_back({step, at, "MAIN", ok, note});
            continue;
        }

        const LensRow* LR = findLens(lens, name);
        if (LR && !LR->setOneTemplate.empty()) {
            std::string urlSet = replaceAll(replaceAll(LR->setOneTemplate, "{key}", name), "{value}", value);
            bool okSet = !curlGET(urlSet).empty();
            bool okGet = false;
            if (okSet && !LR->getOneTemplate.empty()) {
                std::string urlGet = replaceAll(LR->getOneTemplate, "{key}", name);
                okGet = !curlGET(urlGet).empty();
            }
            report.push_back({step, at, "TEST", okSet && (LR->getOneTemplate.empty() ? true : okGet),
                              okSet ? (LR->getOneTemplate.empty() ? "set ok" : (okGet ? "set+get ok" : "get failed"))
                                    : "set failed"});
        } else {
            report.push_back({step, at, "NONE", true, "no MAIN row; no TEST lens row"});
        }
    }

    return true;
}

static void write_run_report(const std::string& base, const std::vector<RunStep>& report) {
    // JSON
    {
        std::ostringstream j;
        j << "{\n  \"steps\": [\n";
        for (size_t i=0;i<report.size();++i) {
            const auto& r = report[i];
            j << "    { \"step\": " << r.step
              << ", \"at\": "   << jsonEscape(r.at)
              << ", \"kind\": " << jsonEscape(r.kind)
              << ", \"ok\": "   << (r.ok?"true":"false")
              << ", \"note\": " << jsonEscape(r.note)
              << " }";
            j << (i+1==report.size() ? "\n" : ",\n");
        }
        j << "  ]\n}\n";
        writeFile(base + ".run_report.json", j.str());
    }
    // Text
    {
        std::ostringstream t;
        t << "Run report for " << base << "\n---------------------------------\n";
        for (const auto& r : report) {
            t << "Step " << r.step << "  @" << r.at << "  [" << r.kind << "]  "
              << (r.ok ? "PASS" : "FAIL") << "  -- " << r.note << "\n";
        }
        writeFile(base + ".run_report.txt", t.str());
    }
}

/*───────────────────────────────────────────────────────────────────────────*/

int main(int argc, char** argv)
{
    bool show_smt=false, show_z3=false, show_json=false, want_fullmodel=false;
    bool want_state_get=false, want_state_keys=false, want_state_set=false;
    bool run_ctc = false;

    // NEW staged flags
    bool stagedMode = false;
    bool executeMid = false;

    std::string sp_map, sp_key, sp_value;

    std::string base = (argc >= 2 && argv[1][0] != '-') ? argv[1] : "constraints";
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if      (a == "--show-smt")           show_smt   = true;
        else if (a == "--show-z3")            show_z3    = true;
        else if (a == "--show-json")          show_json  = true;
        else if (a == "--fullmodel")          want_fullmodel = true;
        else if (a == "--run-ctc")            run_ctc = true;
        else if (a == "--solve-mode=staged")  stagedMode = true;
        else if (a == "--execute-mid")        executeMid = true;
        else if (a == "--state-get"  && i+2 < argc) { want_state_get=true;  sp_map=argv[++i]; sp_key=argv[++i]; }
        else if (a == "--state-keys" && i+1 < argc) { want_state_keys=true; sp_map=argv[++i]; }
        else if (a == "--state-set"  && i+3 < argc) { want_state_set=true;  sp_map=argv[++i]; sp_key=argv[++i]; sp_value=argv[++i]; }
    }
    const std::string pathId = base.substr(base.find_last_of("/\\") + 1);

    // 1) IMA → mutated program
    SymbolTable sym;    TypeMap tmap;
    Program mutant = IMA(clientProgram, spec, sym, tmap);

    // Emit CSV skeleton once
    emitStateLensSkeleton(tmap, base);

    // Pure Test-API probe mode
    if (want_state_get || want_state_keys || want_state_set) {
        const auto lens = loadStateLens(base);
        if (lens.empty()) {
            std::cerr << "No " << base << ".state_lens.csv found. "
                      << "We wrote a skeleton at " << base << ".state_lens.skel.csv\n";
            return 2;
        }
        const LensRow* L = findLens(lens, sp_map);
        if (!L) { std::cerr << "Map not found in lens: " << sp_map << "\n"; return 2; }

        if (want_state_get) {
            std::string url = replaceAll(L->getOneTemplate, "{key}", sp_key);
            std::cout << curlGET(url) << std::endl;
            return 0;
        }
        if (want_state_keys) {
            if (L->getKeysTemplate.empty()) { std::cerr << "No GET_keys_template for " << sp_map << "\n"; return 2; }
            std::cout << curlGET(L->getKeysTemplate) << std::endl;
            return 0;
        }
        if (want_state_set) {
            if (L->setOneTemplate.empty()) { std::cerr << "No SET_one_template for " << sp_map << "\n"; return 2; }
            std::string url = replaceAll(L->setOneTemplate, "{key}", sp_key);
            url = replaceAll(url, "{value}", sp_value);
            std::cout << curlGET(url) << std::endl;
            return 0;
        }
    }

    /*─────────────────── Symbolic collection ──────────────────*/
    SymbolicEnv sigma;
    for (const auto& kv : tmap.mapping)
        if (dynamic_cast<MapType*>(kv.second) != 0) sigma.declareMap(kv.first);

    SEVisitor se(sigma);
    mutant.accept(se);

    /*─────────────────── STAGED mid-execution (optional) ──────────────────*/
    if (stagedMode) {
        auto lens  = loadStateLens(base);
        auto mains = loadMainRows(base + ".state_lens.csv"); // optional MAIN rows
        const auto cps = se.checkpoints();

        // Accumulate pinned values across stages
        std::map<std::string,std::string> pinned;

        int stageIdx = 0;
        for (const auto& cp : cps) {
            // Build a small footer asking only for the SSAs we need now
            std::vector<std::string> ask;
            for (const auto& v : cp.neededVars) {
                std::string ssa = sigma.peekScalar(v);
                if (!ssa.empty()) ask.push_back(ssa);
            }
            if (ask.empty()) { ++stageIdx; continue; }

            std::ostringstream footer;
            footer << "\n(check-sat)\n(get-value (";
            for (const auto& ssa : ask) footer << ssa << " ";
            footer << "))\n";

            // Write a stage file
            std::string smt = sigma.toSMTLib(pinned) + footer.str();
            const std::string stageFile = base + ".stage_" + std::to_string(stageIdx) + ".smt2";
            writeFile(stageFile, smt);

            // Solve
            std::string z3out = runCmdCapture(std::string("z3 -smt2 \"") + stageFile + "\"");
            if (show_z3) {
                std::cout << "===== STAGED Z3 after " << cp.callName
                          << " (stage " << stageIdx << ") =====\n"
                          << z3out << "\n";
            }

            // Parse and pin ONLY xN SSA vars (skip cN, 'error', etc.)
            std::regex pair_re(R"(\(\s*([^\s\(\)]+)\s+("([^"\\]|\\.)*"|[^\s\(\)]+)\s*\))");
            std::sregex_iterator it(z3out.begin(), z3out.end(), pair_re), end;
            for (; it != end; ++it) {
                const std::string ssa = (*it)[1].str();
                if (ssa.empty() || ssa[0] != 'x') continue; // keep only scalar SSAs

                std::string val = (*it)[2].str();
                if (isQuoted(val)) val = val.substr(1, val.size()-2);
                if (val.empty())   val = "auto_" + ssa;

                pinned[ssa] = val;
                sigma.pinValue(ssa, val); // keep env consistent
            }

            // Optional: execute mid-step (MAIN preferred, else TEST lens)
            if (executeMid) {
                bool did = false;
                const MainRow* MR = findMain(mains, cp.callName);
                if (MR && !MR->url.empty() && !cp.neededVars.empty()) {
                    std::string name  = cp.neededVars.front();
                    std::string ssa   = sigma.peekScalar(name);
                    std::string value;
                    if (!ssa.empty()) {
                        auto itP = pinned.find(ssa);
                        if (itP != pinned.end()) value = itP->second;
                    }

                    const std::string url  = expandNV(MR->url,  name, value);
                    const std::string body = expandNV(MR->body, name, value);
                    if (MR->method.empty() || MR->method == "GET" || MR->method == "get") {
                        (void)curlGET(url);
                    } else {
                        (void)curlPOST_json(url, body);
                    }
                    did = true;
                }
                if (!did) {
                    // fallback: TEST lens for each (var,value) we just solved
                    for (const auto& v : cp.neededVars) {
                        const LensRow* LR = findLens(lens, v);
                        if (!LR || LR->setOneTemplate.empty()) continue;
                        std::string ssa = sigma.peekScalar(v);
                        if (ssa.empty()) continue;
                        auto itP = pinned.find(ssa);
                        if (itP == pinned.end()) continue;
                        std::string value = itP->second;
                        std::string urlSet = replaceAll(replaceAll(LR->setOneTemplate, "{key}", v), "{value}", value);
                        (void)curlGET(urlSet);
                    }
                }
            }

            ++stageIdx;
        }
    }

    /*─────────────────── Final (end-of-path) solve and artifacts ──────────────────*/
    const auto& var2id    = sigma.var2id();
    const auto& predNames = sigma.getPredNames();

    std::string smt_body = sigma.toSMTLib();

    std::ostringstream smt_footer;
    smt_footer << "\n(set-option :model.partial true)\n";
    smt_footer << "(set-option :model.compact false)\n";
    smt_footer << "(check-sat)\n";
    smt_footer << "(get-value (";
    for (auto it = var2id.begin(); it != var2id.end(); ++it)  smt_footer << it->second << " ";
    for (size_t i=0;i<predNames.size();++i) smt_footer << predNames[i] << " ";
    smt_footer << "))\n";
    const std::string smt_final = smt_body + smt_footer.str();
    writeFile(base + ".smt2", smt_final);

    // map CSV (debug)
    {
        std::ostringstream csv;
        csv << "program,id\n";
        for (auto it = var2id.begin(); it != var2id.end(); ++it)
            csv << it->first << ',' << it->second << '\n';
        writeFile(base + ".map.csv", csv.str());
    }

    // Pretty SMT (dedup comments) — file only
    std::string pretty = smt_body;
    for (auto it = var2id.begin(); it != var2id.end(); ++it) {
        const std::regex rx_comment(std::string(";.*\\b") + it->second + "\\b");
        pretty = std::regex_replace(pretty, rx_comment, std::string("$& \xE2\x86\x90 ") + it->first);
    }
    writeFile(base + ".pretty.smt2", dedupDecls(pretty));
    if (show_smt) printWithLineNumbers(smt_final);

    // Run Z3
    const std::string z3cmd = std::string("z3 -smt2 \"") + base + ".smt2\"";
    std::string z3out = runCmdCapture(z3cmd);
    if (show_z3) std::cout << "===== Z3 (get-value) =====\n" << z3out << "\n";

    if (z3out.find("(error") != std::string::npos) {
        std::cerr << "Z3 reported an error. Full output:\n" << z3out << "\n";
    }
    if (z3out.find("unsat") != std::string::npos) {
        std::cerr << "WARN: Z3 reported UNSAT for path " << pathId << std::endl;
        writeFile(base + ".model.json", "{ \"status\": \"unsat\" }");
        writeFile(base + ".ctc.json",   "{ \"status\": \"unsat\" }");
        if (!run_ctc) return 1; // still allow --run-ctc to continue if user insists
    }

    // Parse model values
    std::unordered_map<std::string,std::string> id2val;
    {
        std::regex pair_re(R"(\(\s*([^\s\(\)]+)\s+("([^"\\]|\\.)*"|[^\s\(\)]+)\s*\))");
        std::sregex_iterator begin(z3out.begin(), z3out.end(), pair_re), end;
        for (auto it = begin; it != end; ++it) {
            const std::smatch& m = *it;
            id2val[m[1].str()] = m[2].str();
        }
    }
    auto getJsonForSSA = [&](const std::string& ssa)->std::string {
        auto it = id2val.find(ssa);
        std::string raw = (it != id2val.end()) ? it->second : "\"\"";
        return nonEmptyOrAuto(ssa, asJsonString(raw));
    };

    // Build CTC steps
    std::vector<StepRec> steps; int stepCounter = 0; std::string currentCall;
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

    // Checks from assume/assert
    std::vector<CallCheck> checks; std::unordered_map<std::string,int> callCounts; int cidx=0;
    auto getBoolC = [&](int idx)->bool {
        auto it = id2val.find("c" + std::to_string(idx));
        return (it != id2val.end() && it->second == "true");
    };
    for (const auto& S : mutant.statements) {
        if (const auto* call = dynamic_cast<const FuncCallStmt*>(S.get())) {
            const std::string& name = call->call->name;
            if (name == "assume") {
                if (!checks.empty()) checks.back().pre  = getBoolC(++cidx);
            } else if (name == "assert") {
                if (!checks.empty()) checks.back().post = getBoolC(++cidx);
            } else {
                std::string at_tag = name + "#" + std::to_string(++callCounts[name]);
                checks.push_back({at_tag, false, false});
            }
        }
    }

    // model.json
    {
        std::ostringstream json;
        json << "{\n";
        json << "  \"path\": " << jsonEscape(pathId) << ",\n";
        json << "  \"vars\": {\n";
        bool first = true;
        for (auto it = var2id.begin(); it != var2id.end(); ++it) {
            if (!first) json << ",\n"; first = false;
            json << "    " << jsonEscape(it->first) << ": " << getJsonForSSA(it->second);
        }
        json << "\n  }\n}\n";
        writeFile(base + ".model.json", json.str());
    }

    // ctc.json
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

    // ctc.txt
    {
        std::ostringstream txt;
        txt << "CTC for " << pathId << "\n---------------------------------\n";
        for (const auto& st : steps) {
            std::string v = unquote(st.value);
            txt << "Step " << st.step << "  [" << st.role << "]  "
                << st.var << " = " << (v.empty() ? "<empty>" : v)
                << "   @ " << st.at << "\n";
        }
        writeFile(base + ".ctc.txt", txt.str());
    }

    // Optional: run the CTC end-to-end and write a run report
    if (run_ctc) {
        auto lens  = loadStateLens(base);
        auto mains = loadMainRows(base + ".state_lens.csv"); // same CSV (optional MAIN rows)
        if (lens.empty() && mains.empty()) {
            std::cerr << "No lens rows or MAIN rows found in " << base << ".state_lens.csv\n";
            return 2;
        }
        std::vector<RunStep> report;
        if (!run_ctc_once(base, lens, mains, report)) {
            std::cerr << "Could not load " << base << ".ctc.json\n";
            return 2;
        }
        write_run_report(base, report);
        std::cout << "✓ wrote  " << base << ".run_report.json, " << base << ".run_report.txt\n";
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
              << "\n";
    return 0;
}
