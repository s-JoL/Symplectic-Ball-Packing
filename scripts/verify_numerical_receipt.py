#!/usr/bin/env python3
"""Generate or check a source-bound numerical verification receipt for program/.

- `--generate`: runs deterministic bundle checks, audits the full `program/release-check/`
  suite logs, runs live `float64` and 100-digit `mpmath` checks on the current frozen
  sources, and writes `program/release-check/NUMERICAL-VERIFICATION.json`.
- `--check`: verifies (using Python stdlib only) that `NUMERICAL-VERIFICATION.json`
  exists, passed all live and suite checks, and matches the SHA-256 digests of every
  current file in `program/` and `experiments/hamiltonian_lift/`.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
RECEIPT_PATH = ROOT / "program" / "release-check" / "NUMERICAL-VERIFICATION.json"

TRACKED_PROGRAM_FILES = (
    "program/solution_epoch.py",
    "program/check_epoch.py",
    "program/build_embedding.py",
    "program/solution_embedding.py",
    "program/check_embedding.py",
    "program/check_embedding_mp.py",
    "program/embedding_src/chain.py",
    "program/embedding_src/comparator.py",
    "program/embedding_src/keyhole.py",
    "program/embedding_src/primitives.py",
    "program/embedding_src/transfer.py",
    "program/embedding_src/twists.py",
)

TRACKED_EXPERIMENTAL_FILES = (
    "experiments/hamiltonian_lift/README.md",
    "experiments/hamiltonian_lift/build_hamiltonian.py",
    "experiments/hamiltonian_lift/solution_hamiltonian.py",
    "experiments/hamiltonian_lift/check_hamiltonian.py",
    "experiments/hamiltonian_lift/repro_branch_jump.py",
    "experiments/hamiltonian_lift/hamiltonian_src/chain_primitive.py",
    "experiments/hamiltonian_lift/hamiltonian_src/h_primitives.py",
    "experiments/hamiltonian_lift/hamiltonian_src/hamiltonian_general.py",
    "experiments/hamiltonian_lift/logs/repro_branch_jump.log",
    "experiments/hamiltonian_lift/logs/current_honest_check.log",
    "experiments/hamiltonian_lift/logs/current_honest_check.json",
)


def sha256_file(rel_path: str) -> str:
    path = ROOT / rel_path
    if not path.is_file():
        raise RuntimeError(f"missing tracked file: {rel_path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_digests(paths: tuple[str, ...]) -> dict[str, str]:
    return {rel: sha256_file(rel) for rel in paths}


def parse_last_result_json(output: str) -> dict:
    for line in reversed(output.splitlines()):
        if line.startswith("RESULT "):
            return json.loads(line[len("RESULT "):])
    raise RuntimeError(f"no RESULT JSON line found in output:\n{output[-800:]}")


def audit_suite_logs() -> dict:
    rc_dir = ROOT / "program" / "release-check"
    epoch_logs = sorted(rc_dir.glob("k*.log"))
    if len(epoch_logs) != 12:
        raise RuntimeError(f"expected 12 epoch logs, found {len(epoch_logs)}")
    for log_file in epoch_logs:
        rec = parse_last_result_json(log_file.read_text())
        if not rec.get("passed"):
            raise RuntimeError(f"epoch suite log failed: {log_file.name}")

    emb_jsons = sorted((rc_dir / "embedding").glob("*.json"))
    if len(emb_jsons) != 9:
        raise RuntimeError(f"expected 9 float64 embedding JSONs, found {len(emb_jsons)}")
    for jf in emb_jsons:
        rec = json.loads(jf.read_text())
        if not (
            rec.get("finite") is True
            and rec.get("margin", 0.0) > 0.0
            and rec.get("overlap_points") == 0
            and rec.get("multi_member") == 0
        ):
            raise RuntimeError(f"embedding float64 geometry check failed: {jf.name}")

    mp_jsons = sorted((rc_dir / "embedding_mp").glob("*.json"))
    if len(mp_jsons) != 5:
        raise RuntimeError(f"expected 5 mpmath embedding JSONs, found {len(mp_jsons)}")
    for jf in mp_jsons:
        rec = json.loads(jf.read_text())
        lf = jf.with_suffix(".log")
        log_txt = lf.read_text() if lf.is_file() else ""
        if not (
            rec.get("pass_all") is True
            and rec.get("dps") == 100
            and rec.get("finite_mp") is True
            and rec.get("mp_overlaps") == 0
            and rec.get("g_all_continuous") is True
            and "target_iters=300" in log_txt
            and "h=1e-33" in log_txt
            and "MP CHECK PASS" in log_txt
        ):
            raise RuntimeError(f"embedding mpmath suite JSON/log failed or stale: {jf.name}")

    exp_json = json.loads(
        (ROOT / "experiments/hamiltonian_lift/logs/current_honest_check.json").read_text()
    )
    exp_pass = sum(1 for r in exp_json if r.get("passed") is True)
    exp_fail = sum(1 for r in exp_json if r.get("passed") is False)
    if exp_fail == 0:
        raise RuntimeError("experimental log unexpectedly claims 0 failures")

    return {
        "epoch_f64_suite_cases": len(epoch_logs),
        "embedding_f64_suite_cases": len(emb_jsons),
        "embedding_mp100_suite_cases": len(mp_jsons),
        "experimental_honest_cases": {"pass": exp_pass, "fail": exp_fail},
    }


def python_runner(with_mpmath: bool = False) -> list[str]:
    uv = shutil.which("uv") or str(Path.home() / ".local" / "bin" / "uv")
    if Path(uv).is_file():
        pkgs = ["--with", "torch"] + (["--with", "mpmath"] if with_mpmath else [])
        return [uv, "run", *pkgs, "python3"]
    return [sys.executable]


def generate_receipt() -> None:
    subprocess.run(
        [sys.executable, "program/build_embedding.py", "--check"],
        cwd=ROOT,
        check=True,
    )
    subprocess.run(
        [sys.executable, "experiments/hamiltonian_lift/build_hamiltonian.py", "--check"],
        cwd=ROOT,
        check=True,
    )
    suite_summary = audit_suite_logs()

    specs = [
        {
            "name": "epoch_k10_e0.1_rk4",
            "program": "program/solution_epoch.py",
            "checker": "program/check_epoch.py",
            "args": ["program/solution_epoch.py", "--k", "10", "--eps", "0.1", "--recommended", "--N", "300"],
            "with_mpmath": False,
            "scope": "Paper III sheared-window k=10 family, fixed-step float64 RK4 at N=2592 and 2N=5184",
        },
        {
            "name": "epoch_k11_e0.11_rk4",
            "program": "program/solution_epoch.py",
            "checker": "program/check_epoch.py",
            "args": ["program/solution_epoch.py", "--k", "11", "--eps", "0.11", "--recommended", "--N", "300"],
            "with_mpmath": False,
            "scope": "Paper III non-square lattice k=11 family, fixed-step float64 RK4 at N=400 and 2N=800",
        },
        {
            "name": "embedding_f64_k10_e0.1",
            "program": "program/solution_embedding.py",
            "checker": "program/check_embedding.py",
            "args": ["program/solution_embedding.py", "--k", "10", "--eps", "0.1", "--h", "1e-7"],
            "with_mpmath": False,
            "scope": "Paper IV closed-form C^4 embeddings & Preimage in float64 (full checks A-G, 17 special + 1000 random/ball, 200k volume)",
        },
        {
            "name": "embedding_f64_k11_e0.01_geom",
            "program": "program/solution_embedding.py",
            "checker": "program/check_embedding.py",
            "args": ["program/solution_embedding.py", "--k", "11", "--eps", "0.01", "--h", "1e-7", "--chords", "0", "--M", "50000"],
            "with_mpmath": False,
            "scope": "Paper IV non-square k=11 eps=0.01 float64 checks A-F (containment, Richardson symplecticity, round-trip, disjointness, volume)",
        },
        {
            "name": "embedding_mp100_k10_e0.002",
            "program": "program/solution_embedding.py",
            "checker": "program/check_embedding_mp.py",
            "args": ["program/solution_embedding.py", "--k", "10", "--eps", "0.002", "--dps", "100", "--chords", "10", "--mp-random", "2"],
            "with_mpmath": True,
            "scope": "AST-transformed 100-digit mpmath execution (target_iters=300, h=1e-33) on k=10, eps=0.002 across all 10 balls",
        },
        {
            "name": "embedding_mp100_k11_e0.01",
            "program": "program/solution_embedding.py",
            "checker": "program/check_embedding_mp.py",
            "args": ["program/solution_embedding.py", "--k", "11", "--eps", "0.01", "--dps", "100", "--chords", "10", "--mp-random", "2"],
            "with_mpmath": True,
            "scope": "AST-transformed 100-digit mpmath execution (target_iters=300, h=1e-33, plus 1e-30 chord continuity) on non-square k=11, eps=0.01 across all 11 balls",
        },
    ]

    env = dict(os.environ)
    live_runs = []
    for spec in specs:
        cmd = [*python_runner(spec["with_mpmath"]), spec["checker"], *spec["args"]]
        display_cmd = f"python3 {spec['checker']} " + " ".join(spec["args"])
        print(f"[numerical-gate] running {display_cmd} ...", flush=True)
        t0 = time.monotonic()
        proc = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
        elapsed = round(time.monotonic() - t0, 3)
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
            raise RuntimeError(f"live numerical check failed ({proc.returncode}): {display_cmd}")
        res = parse_last_result_json(proc.stdout)
        passed = bool(res.get("passed", res.get("pass", res.get("pass_all", False))))
        if not passed:
            raise RuntimeError(f"live numerical check reported failure: {spec['name']}: {res}")
        live_runs.append({
            "name": spec["name"],
            "command": display_cmd,
            "scope": spec["scope"],
            "exit_code": proc.returncode,
            "passed": True,
            "wall_seconds": elapsed,
            "metrics": {
                k: res[k]
                for k in (
                    "k", "eps", "R_needed", "margin", "min_radius_margin", "max_point_difference",
                    "roundtrip_max", "sym_defect", "overlap_points", "multi_member",
                    "max_roundtrip_mp", "max_sym_mp", "max_agree_scaled", "mp_overlaps",
                )
                if k in res
            },
        })

    receipt = {
        "schema": "symplectic-numerical-verification-v1",
        "version": "1.2.0",
        "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "result": "PASS",
        "note": (
            "Numerical corroboration receipt for the frozen program/ sources. "
            "Formal mathematical verification of Papers I-II and RK4Convergence.lean is recorded separately "
            "in RELEASE-VERIFICATION.json and KERNEL-REPLAY.json. "
            "experiments/hamiltonian_lift/ is archived solely as unfinished experimental material and is NOT certified."
        ),
        "program_source_sha256": current_digests(TRACKED_PROGRAM_FILES),
        "suite_logs_audited": suite_summary,
        "live_runs": live_runs,
        "experimental_archive": {
            "status": "EXPERIMENTAL_UNFINISHED_NOT_CERTIFIED",
            "directory": "experiments/hamiltonian_lift",
            "known_issue": (
                "Straight-ray branch sheet unwrapping in Stages 9-11 exhibits integer-turn scalar jumps "
                "across cutoff collars near small |Z_0| (e.g. k=12, eps=0.001, ball 11; see repro_branch_jump.py "
                "and logs/current_honest_check.log)."
            ),
            "source_sha256": current_digests(TRACKED_EXPERIMENTAL_FILES),
        },
    }
    RECEIPT_PATH.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(f"NUMERICAL RECEIPT GENERATED AND VERIFIED: {RECEIPT_PATH.relative_to(ROOT)}", flush=True)


def check_receipt() -> None:
    if not RECEIPT_PATH.is_file():
        raise RuntimeError(f"missing numerical verification receipt: {RECEIPT_PATH}")
    receipt = json.loads(RECEIPT_PATH.read_text())
    if receipt.get("result") != "PASS":
        raise RuntimeError("numerical verification receipt is not PASS")
    expected_prog = current_digests(TRACKED_PROGRAM_FILES)
    if receipt.get("program_source_sha256") != expected_prog:
        raise RuntimeError(
            "program/ sources do not match NUMERICAL-VERIFICATION.json; re-run "
            "`python3 scripts/verify_numerical_receipt.py --generate`"
        )
    expected_exp = current_digests(TRACKED_EXPERIMENTAL_FILES)
    exp_block = receipt.get("experimental_archive", {})
    if exp_block.get("status") != "EXPERIMENTAL_UNFINISHED_NOT_CERTIFIED":
        raise RuntimeError("experimental archive status tag missing or invalid")
    if exp_block.get("source_sha256") != expected_exp:
        raise RuntimeError(
            "experiments/hamiltonian_lift/ files do not match NUMERICAL-VERIFICATION.json; re-run "
            "`python3 scripts/verify_numerical_receipt.py --generate`"
        )
    live_runs = receipt.get("live_runs", [])
    if len(live_runs) < 6 or not all(r.get("exit_code") == 0 and r.get("passed") is True for r in live_runs):
        raise RuntimeError("NUMERICAL-VERIFICATION.json has missing or failing live_runs")
    audit_suite_logs()
    print(
        f"Numerical verification receipt check: PASS ({len(live_runs)} live runs, "
        f"{len(expected_prog)} program files + {len(expected_exp)} experimental files hash-matched)",
        flush=True,
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--generate", action="store_true")
    group.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.generate:
        generate_receipt()
    else:
        check_receipt()


if __name__ == "__main__":
    main()
