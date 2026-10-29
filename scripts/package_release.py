#!/usr/bin/env python3
"""Verify the current sources and produce a history-free submission bundle.

Uses Python 3.11+ and the same Lean/Node/Tectonic tools as scripts/verify.sh.
The archive is built from an explicit public-file list, never from the whole workspace.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tomllib
from datetime import datetime, timezone
from zipfile import ZIP_DEFLATED, ZipFile
from project_cache import source_digest, artifact_digest


ROOT = Path(__file__).resolve().parent.parent
PUBLIC_FILES = (
    "README.md", "README.zh-CN.md", "REVIEW.md", "PROVENANCE.md", "cache/README.md", ".gitattributes", "LICENSE", "NOTICE", "CITATION.cff", ".zenodo.json", ".gitignore",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain", "SymplecticPacking.lean",
)
PUBLIC_DIRS = ("SymplecticPacking", "verification", "vendor", "scripts", "test", ".github")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def public_sources() -> dict[str, bytes]:
    paths = [ROOT / p for p in PUBLIC_FILES]
    for name in PUBLIC_DIRS:
        paths.extend(p for p in (ROOT / name).rglob("*") if p.is_file())
    paths.extend(p for p in (ROOT / "paper").rglob("*")
                 if p.is_file() and p.suffix != ".pdf" and "build" not in p.relative_to(ROOT / "paper").parts)
    result = {}
    for p in sorted(set(paths)):
        if p.name == ".DS_Store" or p.suffix == ".pyc" or "__pycache__" in p.parts:
            continue
        if p.is_symlink():
            raise RuntimeError(f"public sources contain a symlink: {p.relative_to(ROOT)}")
        result[p.relative_to(ROOT).as_posix()] = p.read_bytes()
    return result


def tree_digest(files: dict[str, bytes]) -> str:
    return sha256("".join(f"{sha256(data)}  {name}\n" for name, data in sorted(files.items())).encode())


def main() -> None:
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    metadata = json.loads((ROOT / ".zenodo.json").read_text())
    citation = (ROOT / "CITATION.cff").read_text()
    version = config["version"]
    if not re.fullmatch(r"\d+\.\d+\.\d+", version):
        raise RuntimeError("expected a three-part release version")
    if metadata["version"] != version or f'version: "{version}"' not in citation:
        raise RuntimeError("Lake, citation and archive metadata versions disagree")
    if f'date-released: "{metadata["publication_date"]}"' not in citation:
        raise RuntimeError("citation and archive dates disagree")

    before = public_sources()
    log = ROOT / ".lake" / "verify" / "submission.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    print("Verifying sources, paper tags, Lean proofs, regressions and both papers...", flush=True)
    with log.open("w") as stream:
        completed = subprocess.run(["bash", "scripts/verify.sh"], cwd=ROOT,
                                   stdout=stream, stderr=subprocess.STDOUT)
    if completed.returncode:
        raise RuntimeError(f"verification failed; see {log}")
    kernel_receipt_path = ROOT / ".lake/verify/kernel-replay.json"
    kernel = json.loads(kernel_receipt_path.read_text()) if kernel_receipt_path.exists() else {}
    expected_kernel_inputs = (source_digest(), artifact_digest())
    if (kernel.get("result") != "PASS" or
            (kernel.get("source_sha256"), kernel.get("artifact_sha256")) != expected_kernel_inputs or
            kernel.get("lean_toolchain") != (ROOT / "lean-toolchain").read_text().strip()):
        with log.open("a") as stream:
            subprocess.run(["bash", "scripts/check_kernel.sh"], cwd=ROOT, check=True,
                           stdout=stream, stderr=subprocess.STDOUT)
        kernel = json.loads(kernel_receipt_path.read_text())
    if tree_digest(before) != tree_digest(public_sources()):
        raise RuntimeError("sources changed during verification; rerun packaging")
    verification_log = log.read_text()
    if "VERIFY PASS" not in verification_log:
        raise RuntimeError("verification did not finish")

    payload = dict(before)
    page_counts = {}
    for doc in ("main", "supplement"):
        pdf = ROOT / "paper" / "build" / f"{doc}.pdf"
        data = pdf.read_bytes()
        if not data.startswith(b"%PDF-"):
            raise RuntimeError(f"invalid PDF: {doc}")
        payload[f"paper/{doc}.pdf"] = data
        match = re.search(rf"{doc}: (\d+) pages, 0 undefined references, 0 multiply defined labels, 0 overfull boxes",
                          verification_log)
        if not match:
            raise RuntimeError(f"missing successful paper check: {doc}")
        page_counts[doc] = int(match[1])

    receipt = {
        "version": version,
        "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_tree_sha256": tree_digest(before),
        "verification_command": "bash scripts/verify.sh",
        "result": "PASS",
        "build_route": "local incremental build using existing dependencies and compiled files",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "paper_pages": page_counts,
        "kernel_replay": kernel,
        "checks": ["source hygiene", "paper declaration tags",
                   "Lean library and verification build", "axiom and explicitness audits",
                   "full proof-dependency independence audit", "checker regression tests",
                   "paper compilation and cross-references"],
    }
    receipt_bytes = (json.dumps(receipt, ensure_ascii=False, indent=2) + "\n").encode()
    payload["RELEASE-VERIFICATION.json"] = receipt_bytes
    payload["KERNEL-REPLAY.json"] = kernel_receipt_path.read_bytes()
    payload["MANIFEST.sha256"] = "".join(
        f"{sha256(data)}  {name}\n" for name, data in sorted(payload.items())).encode()

    out = ROOT / "release"
    out.mkdir(exist_ok=True)
    archive = out / f"symplectic-ball-packing-{version}.zip"
    with ZipFile(archive, "w", compression=ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in sorted(payload.items()):
            z.writestr(name, data)
    with ZipFile(archive) as z:
        if z.testzip() is not None or set(z.namelist()) != set(payload):
            raise RuntimeError("archive integrity check failed")
        for name, expected in payload.items():
            if sha256(z.read(name)) != sha256(expected):
                raise RuntimeError(f"archive content mismatch: {name}")

    for doc in ("main", "supplement"):
        shutil.copyfile(ROOT / "paper" / "build" / f"{doc}.pdf", out / f"{doc}.pdf")
    (out / "verification.json").write_bytes(receipt_bytes)
    outputs = [archive, out / "main.pdf", out / "supplement.pdf", out / "verification.json"]
    (out / "SHA256SUMS").write_text("".join(f"{sha256(p.read_bytes())}  {p.name}\n" for p in outputs))
    print(f"PASS: {archive.name}; {len(before)} source files; PDFs {page_counts}", flush=True)
    print("Archive contents and checksums verified. No Git history or build caches included.", flush=True)


if __name__ == "__main__":
    main()
