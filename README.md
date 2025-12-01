# IMA-Client-Testing-with-server
The Implicit Mocking Algorithm (IMA) generates test cases by transforming client programs using formal API specifications and statecharts

1.  Project at a glance
2.  repo-root/
│
├─ Tools/ ← helper scripts & drivers
│ └─ build_all_paths.sh … batch-builds every test path
│
├─ Symbolic/ ← symbolic execution engine
│ ├─ SEVisitor.cpp/hpp
│ ├─ SymbolicEnv.hpp
│ └─ smtlib_printer.hpp
│
├─ testPaths/ ← concrete test paths, grouped per web-app
│ ├─ webApp1/
│ │ ├─ path1.cpp
│ │ ├─ path2.cpp
│ │ ├─ path3.cpp
│ │ └─ path4.cpp
│ └─ webApp2/
│ └─ path1.cpp
│
├─ Scratch/ ← out-of-band helpers (never part of production)
│ └─ print_ast.cpp … prints abstract & symbolic test cases on demand
│
├─ IMA.hpp ← in-memory mutation algorithm (abstract test cases)
├─ ast.hpp ← full AST for programs & specs
└─ README.md ← you are here


* **`ast.hpp`** – node definitions for the client program and the API specification.  
* **`IMA.hpp`** – *Inference-Mutation Algorithm* that transforms an abstract spec into a
  concrete test-case program with `assume` / `assert`.  
* **`SEVisitor.*`** – walks the mutated program, collects path constraints, and
  emits pure SMT-LIB.  
* **`SymbolicEnv.hpp`** – small helper that stores fresh symbolic IDs (`x1`,`x2`,…)
  and prints them as declarations + assertions.  
* **`build_all_paths.sh`** – compiles every `testPaths/**/path*.cpp`, runs the symbolic
  executor, and drops  
  `build/paths/<pathN>.smt2`  +  `build/paths/<pathN>.pretty.smt2`.  
* **`Scratch/print_ast.cpp`** – optional one-off tool to *print* the abstract test case
  (and, if you uncomment the lines, the symbolic constraints) for any single path file.

---

## 3.  One-shot build & run (all paths)

```bash
# 0) open WSL and cd to the repo root
cd /mnt/c/Users/<you>/Downloads/Specification-Based-Testing-of-RESTful-APIs-master

# 1) first time only: make the helper script executable
chmod +x Tools/build_all_paths.sh

# 2) compile *and* execute every path
Tools/build_all_paths.sh

Build & run a single path

Example uses testPaths/webApp3/path1.cpp. Change as needed.

# 1) build
g++ -std=c++17 -O2 \
  Tools/run_se_driver.cpp \
  Symbolic/SEVisitor.cpp \
  Scratch/ExpoSEVisitor_stubs.cpp \
  -I . \
  -DPATH_FILE=\"testPaths/webApp3/path1.cpp\" \
  -o build/paths/webApp3_path1

# 2) run 
./build/paths/webApp3_path1 build/paths/webApp3_path1


# 3) Artifacts (in build/paths/)

webApp3_path1.smt2 – solver input

webApp3_path1.pretty.smt2 – cleaned/ordered SMT

webApp3_path1.map.csv – program var ↔ SSA id

webApp3_path1.model.json – concrete values (never empty)

webApp3_path1.ctc.json – concrete test case (steps + checks)

webApp3_path1.ctc.txt – human summary



## 4. Useful run flags 
# show SMT with line numbers
./build/paths/webApp3_path1 build/paths/webApp3_path1 --show-smt

# show Z3 output
./build/paths/webApp3_path1 build/paths/webApp3_path1 --show-z3

# echo JSONs
./build/paths/webApp3_path1 build/paths/webApp3_path1 --show-json

# dump full (get-model) to webApp3_path1.fullmodel.txt
./build/paths/webApp3_path1 build/paths/webApp3_path1 --fullmodel

# Combine Files as you like
  ./build/paths/webApp3_path1 build/paths/webApp3_path1 --show-smt --show-z3 --show-json --fullmodel

# Quick inspect
sed -n '1,120p' build/paths/webApp3_path1.pretty.smt2
column -s, -t build/paths/webApp3_path1.map.csv | less
jq . build/paths/webApp3_path1.model.json
jq . build/paths/webApp3_path1.ctc.json
z3 -smt2 build/paths/webApp3_path1.smt2

# or just:
cat build/paths/webApp3_path1.smt2
cat build/paths/webApp3_path1.pretty.smt2

# var ↔ SSA map
cat build/paths/webApp3_path1.map.csv

# JSON (raw)
cat build/paths/webApp3_path1.model.json
cat build/paths/webApp3_path1.ctc.json


Print abstract & symbolic (no solver)
g++ -std=c++17 -O2 -Wall \
  -Wno-unused-variable -Wno-strict-aliasing \
  -I. -ISymbolic \
  Scratch/ExpoSEVisitor_stubs.cpp \
  Scratch/print_ast.cpp \
  -o build/print_ast

./build/print_ast
