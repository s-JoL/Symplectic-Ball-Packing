#!/usr/bin/env bash
# Replay the full proof closure into an empty environment using the pinned Lean kernel.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/verify
lake build +verification.Kernel > .lake/verify/kernel-build.log 2>&1
kernel_inputs=$(python3 -c 'import json; from scripts.project_cache import source_digest, artifact_digest; print(json.dumps([source_digest(), artifact_digest()]))')
lake env leanchecker --fresh verification.Kernel > .lake/verify/kernel.log 2>&1 || {
  tail -40 .lake/verify/kernel.log
  echo 'KERNEL REPLAY FAILED' >&2
  exit 1
}
python3 - "$kernel_inputs" <<'PY'
import datetime, json, sys
from pathlib import Path
from scripts.project_cache import source_digest, artifact_digest
inputs = json.loads(sys.argv[1])
if inputs != [source_digest(), artifact_digest()]:
    raise SystemExit('proof sources or objects changed during kernel replay')
receipt = {'result': 'PASS', 'command': 'lake env leanchecker --fresh verification.Kernel',
           'verified_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'source_sha256': inputs[0], 'artifact_sha256': inputs[1],
           'lean_toolchain': Path('lean-toolchain').read_text().strip()}
Path('.lake/verify/kernel-replay.json').write_text(json.dumps(receipt, indent=2) + '\n')
PY
echo 'KERNEL REPLAY PASS'
