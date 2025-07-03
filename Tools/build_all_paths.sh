
set -euo pipefail
shopt -s nullglob                               

root="$(dirname "$(readlink -f "$0")")/.."      
out="$root/build/paths"
mkdir -p "$out"


core_sources=(
  "$root/Symbolic/"*.cpp
  "$root/jsCodeGenerator/jsCodeGen.cpp"
)


mapfile -t paths < <(find "$root/testPaths" -name 'path*.cpp' | sort)
echo "Found ${#paths[@]} path files."


for p in "${paths[@]}"; do
  folder="$(basename "$(dirname "$p")")"         # webApp1 / webApp2 / …
  file="$(basename "${p%.cpp}")"                 # path1 / path2 …
  base="${folder}_${file}"                       # → webApp2_path1 …

  exe="$out/${base}.exe"

  echo "⮡  building $exe"
  g++ -std=c++17 -I"$root" \
      -DPATH_FILE="\"$p\"" \
      "$root/Tools/run_se_driver.cpp" \
      "${core_sources[@]}" \
      -o "$exe"

  echo "   running $exe"
  "$exe" "$out/${base}"                          # writes ${base}.smt2
done

echo " Finished.  SMT-LIB files are in  $out/"
