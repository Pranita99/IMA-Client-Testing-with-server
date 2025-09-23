#!/usr/bin/env bash
# --------------------------------------------------------------------
# Build & run every  testPaths/**/path*.cpp
# -> build/paths/<app>_<path>.{smt2,pretty.smt2,model.json,ctc.json,ctc.txt,...}
# --------------------------------------------------------------------

set -euo pipefail
shopt -s nullglob

# repo root and output dir
root="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
out="$root/build/paths"
mkdir -p "$out"

# Silence the driver's extra printing unless the user overrides it
#   usage to see verbose:  QUIET=0 Tools/build_all_paths.sh
export QUIET="${QUIET:-1}"

# Collect all path files (sorted for determinism)
mapfile -t paths < <(find "$root/testPaths" -name 'path*.cpp' | sort)
echo "Found ${#paths[@]} path files."

# Build + execute each path
for p in "${paths[@]}"; do
  folder="$(basename "$(dirname "$p")")"   # e.g. webApp1
  file="$(basename "${p%.cpp}")"           # path1 / path2 …
  base="${folder}_${file}"                 # webApp1_path1
  exe="$out/${base}.exe"

  echo ": g++  ->  $exe    (with PATH_FILE=\"$p\")"
  g++ -std=c++17 -O2 -Wall \
     "$root/Tools/run_se_driver.cpp" \
     "$root/Symbolic/SEVisitor.cpp" \
     "$root/Scratch/ExpoSEVisitor_stubs.cpp" \
     -I "$root" \
     -DPATH_FILE="\"$p\"" \
     -o "$exe"

  # Run: this writes .smt2, .pretty.smt2, .map.csv, .model.json, .ctc.json, .ctc.txt, .fullmodel.txt
  "$exe" "$out/$base"
done

echo -e "\n✓ All artefacts are in  $out/"