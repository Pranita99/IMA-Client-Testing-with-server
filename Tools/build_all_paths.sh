#!/usr/bin/env bash
# ────────────────────────────────────────────────────────────────
# Build & run every   testPaths/**/path*.cpp
#  → build/paths/<app>_<path>.{smt2,pretty.smt2}
# ────────────────────────────────────────────────────────────────
set -euo pipefail
shopt -s nullglob

root="$(dirname "$(readlink -f "$0")")/.."   # repo root
out="$root/build/paths"
mkdir -p "$out"

# ── compile these into *every* per‑path executable ──────────────
core_sources=(
  "$root/Symbolic/"*.cpp                      
   #"$root/jsCodeGenerator/visitor.cpp"          
  "$root/jsCodeGenerator/jsCodeGen.cpp"      
)

# ── collect all concrete path files ─────────────────────────────
mapfile -t paths < <(find "$root/testPaths" -name 'path*.cpp' | sort)
echo "Found ${#paths[@]} path files."

# ── build + execute each path ───────────────────────────────────
for p in "${paths[@]}"; do
  folder="$(basename "$(dirname "$p")")"        # e.g. webApp1
  file="$(basename "${p%.cpp}")"                # path1 / path2 …
  base="${folder}_${file}"                      # webApp1_path1
  exe="$out/${base}.exe"

  echo "• g++ → $exe   (with PATH_FILE=\"$p\")"
  g++ -std=c++17 -I"$root" \
      -DPATH_FILE="\"$p\"" \
      "$root/Tools/run_se_driver.cpp" \
      "${core_sources[@]}" \
      -o "$exe"

  "$exe" "$out/${base}"                         # writes .smt2 + .pretty.smt2
done

echo -e "\n✓ All artefacts are in  $out/"
