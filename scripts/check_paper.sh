#!/bin/bash
# Compile all four papers with tectonic. Paper I and Paper II have a main text and a supplement
# that cross-reference each other via xr-hyper, so each is compiled twice in alternation.
# Fails on LaTeX errors, undefined or multiply defined references and citations, unstable
# references and overfull boxes.
set -u
cd "$(dirname "$0")/../paper" || exit 2
status=0
build() {  # build <paper dir> <documents...>
  local dir=$1; shift
  mkdir -p "$dir/build"
  local passes=("$@" "$@")
  for doc in "${passes[@]}"; do
    (cd "$dir" && tectonic -X compile "$doc.tex" --outdir build --keep-intermediates --keep-logs \
      > "build/$doc.tectonic.out" 2>&1) || { echo "tectonic failed on $dir/$doc"; tail -20 "$dir/build/$doc.tectonic.out"; exit 2; }
  done
  for doc in "$@"; do
    local log="$dir/build/$doc.log"
    pages=$(grep -o "([0-9]* pages" "$log" | tail -1 | tr -dc '0-9')
    undef=$(grep -c "undefined" "$log" || true)
    overfull=$(grep -c '^Overfull' "$log" || true)
    multiple=$(grep -c 'multiply defined' "$log" || true)
    rerun=$(grep -c 'Rerun to get' "$log" || true)
    echo "$dir/$doc: $pages pages, $undef undefined references, $multiple multiply defined labels, $overfull overfull boxes"
    [ -n "$pages" ] && [ -s "$dir/build/$doc.pdf" ] || { echo "$dir/$doc: no PDF produced"; status=1; }
    [ "$undef" = "0" ] || { grep "undefined" "$log" | head -20; status=1; }
    [ "$multiple" = "0" ] || { grep "multiply defined" "$log" | head -20; status=1; }
    [ "$rerun" = "0" ] || { echo "$dir/$doc: references not stable after two passes"; status=1; }
    [ "$overfull" = "0" ] || { grep '^Overfull' "$log" | head -20; status=1; }
  done
}
build overview main
build p1 supplement main
build p2 supplement main
build p3 main
build p4 main
exit $status
