#!/usr/bin/env bash
# Full check of the repository: source hygiene, paper-to-Lean tags, Lean build with axiom and
# explicitness gates, regression tests and both papers. Every stage is fatal. Node.js is
# needed in every mode (source checks); Elan for the Lean stages, Tectonic for the papers.
#   bash scripts/verify.sh            # everything
#   bash scripts/verify.sh --lean     # Lean only
#   bash scripts/verify.sh --paper    # papers only
set -euo pipefail
cd "$(dirname "$0")/.."
mode=${1:---all}
case "$mode" in
  --all|--lean|--paper) ;;
  *) echo 'usage: bash scripts/verify.sh [--all|--lean|--paper]' >&2; exit 2 ;;
esac
log=.lake/verify; mkdir -p "$log"

echo '== source checks'
node scripts/paper_tags.mjs --self-test > "$log/paper-tags-selftest.log"
node scripts/check_publication_sources.mjs --self-test > "$log/sources-selftest.log"
node scripts/check_publication_sources.mjs | tee "$log/sources.log"

if [[ $mode != --paper ]]; then
  echo '== paper-to-Lean tags'
  node scripts/paper_tags.mjs --check
  echo '== Lean build (library, verification entry, audits, tag check, regression tests)'
  lake --version
  build_status=0
  lake build SymplecticPacking verification test > "$log/build.log" 2>&1 || build_status=$?
  grep -E '^(error|✖)' "$log/build.log" || true
  [[ $build_status -eq 0 ]] || { echo "Lean build FAILED (exit $build_status); see $log/build.log" >&2; exit 1; }
  echo '== re-elaborate review entries and checker regressions'
  # Re-run the source-level gates even when Lake restored compiled audit artifacts.
  # Resolve the environment once; one process at a time bounds peak memory on CI.
  lake env bash -s -- "$log" <<'REVIEW'
set -euo pipefail
log=$1
for entry in verification/Statement.lean verification/Computability.lean \
  verification/EpochComputability.lean verification/Executable.lean verification/Audit/Independence.lean \
  verification/Audit/PaperTags.lean test/ExplicitTest.lean \
  test/DependencyAuditTest.lean test/AxiomCheckTest.lean; do
  name=${entry//\//-}
  lean -j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
    "$entry" > "$log/recheck-$name.log" 2>&1 || {
      tail -40 "$log/recheck-$name.log"
      echo "Review entry FAILED: $entry" >&2
      exit 1
    }
done
REVIEW
  echo 'Lean: PASS'
fi

if [[ $mode != --lean ]]; then
  echo '== papers'
  bash scripts/check_paper.sh
  echo 'Papers: PASS'
fi

echo 'VERIFY PASS'
