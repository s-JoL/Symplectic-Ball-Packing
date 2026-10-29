#!/bin/bash
# Compile the main text and the supplement with tectonic (cross-references between the two
# documents via xr-hyper need two passes). Fails on LaTeX errors, undefined or multiply
# defined references and citations, unstable references and overfull boxes.
set -u
cd "$(dirname "$0")/../paper" || exit 2
mkdir -p build
status=0
for doc in supplement main supplement main; do
  tectonic -X compile "$doc.tex" --outdir build --keep-intermediates --keep-logs \
    > "build/$doc.tectonic.out" 2>&1 || { echo "tectonic failed on $doc"; tail -20 "build/$doc.tectonic.out"; exit 2; }
done
for doc in main supplement; do
  pages=$(grep -o "([0-9]* pages" "build/$doc.log" | tail -1 | tr -dc '0-9')
  undef=$(grep -c "undefined" "build/$doc.log" || true)
  overfull=$(grep -c '^Overfull' "build/$doc.log" || true)
  multiple=$(grep -c 'multiply defined' "build/$doc.log" || true)
  rerun=$(grep -c 'Rerun to get' "build/$doc.log" || true)
  echo "$doc: $pages pages, $undef undefined references, $multiple multiply defined labels, $overfull overfull boxes"
  [ -n "$pages" ] && [ -s "build/$doc.pdf" ] || { echo "$doc: no PDF produced"; status=1; }
  [ "$undef" = "0" ] || { grep "undefined" "build/$doc.log" | head -20; status=1; }
  [ "$multiple" = "0" ] || { grep "multiply defined" "build/$doc.log" | head -20; status=1; }
  [ "$rerun" = "0" ] || { echo "$doc: references not stable after two passes"; status=1; }
  [ "$overfull" = "0" ] || { grep '^Overfull' "build/$doc.log" | head -20; status=1; }
done
exit $status
