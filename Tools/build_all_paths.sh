#!/usr/bin/env bash
# ------------------------------------------------------------------
# Build & run every  testPaths/**/path*.cpp
# -> build/paths/<app>_<path>.{smt2,pretty.smt2,model.json,ctc.json,...}
# ------------------------------------------------------------------
set -euo pipefail
shopt -s nullglob

root="$(dirname "$(readlink -f "$0")")/.."   # repo root
out="$root/build/paths"
mkdir -p "$out"

# Silence the driver’s verbose printing unless user overrides.
export QUIET="${QUIET:-1}"

# Collect all concrete path files (sorted for determinism)
mapfile -t paths < <(find "$root/testPaths" -name 'path*.cpp' | sort)
echo "Found ${#paths[@]} path files."

# Build + execute each path
for p in "${paths[@]}"; do
  folder="$(basename "$(dirname "$p")")"   # e.g., webApp1
  file="$(basename "${p%.cpp}")"           # e.g., path1
  base="${folder}_${file}"                 # e.g., webApp1_path1
  exe="$out/${base}"

  echo ":: g++ -> $exe   (PATH_FILE=$p)"
  g++ -std=c++17 -O2 -Wall \
    Tools/run_se_driver.cpp \
    Symbolic/SEVisitor.cpp \
    Scratch/ExpoSEVisitor_stubs.cpp \
    -I . \
    -DPATH_FILE="\"$p\"" \
    -o "$exe"

  # Run: this writes .smt2, .pretty.smt2, .map.csv, .model.json, .ctc.json, .ctc.txt
  "$exe" "$out/${base}"
done

echo -e "\n✓ All artefacts are in  $out/"
