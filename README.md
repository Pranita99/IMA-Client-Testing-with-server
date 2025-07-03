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

3.
| Name                | What it contains                                                                 |
| ------------------- | -------------------------------------------------------------------------------- |
| `pathN.exe`         | the compiled test driver (mutant + symbolic executor)                            |
| `pathN.smt2`        | raw SMT-LIB straight from the executor                                           |
| `pathN.pretty.smt2` | same SMT−LIB **plus** deterministic<br>literals (`user_webApp1_path1`, `pass_…`) |

Check satisfiability with Z3
z3 -model build/paths/webApp1_path1.smt2
# => sat + full model

z3 -model build/paths/webApp1_path3.smt2
# => unsat

4. Printing abstract test cases
The normal pipeline skips printing for performance.
When you need a human-friendly listing:

Open Scratch/print_ast.cpp
Edit one line to point at the path you want:

#include "../testPaths/webApp1/path1.cpp"   // ← adjust

5. Typical workflow cheat-sheet

| Task                                | Command                                            |
| ----------------------------------- | -------------------------------------------------- |
| Rebuild everything & regenerate SMT | `Tools/build_all_paths.sh`                         |
| Inspect solver result               | `z3 -model build/paths/<name>.smt2`                |
| Read human-friendly SMT             | `wslview build/paths/<name>.pretty.smt2`           |
| Print an abstract test case         | *edit* `Scratch/print_ast.cpp` → `g++ …` → run exe |






