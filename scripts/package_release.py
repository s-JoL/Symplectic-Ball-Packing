#!/usr/bin/env python3
"""Verify the current sources and produce a history-free submission bundle.

Uses Python 3.11+ and the same Lean/Node/Tectonic tools as scripts/verify.sh.
The archive is built from an explicit public-file list, never from the whole workspace.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tomllib
from zipfile import ZIP_DEFLATED, ZipFile

from project_cache import artifact_digest, source_digest


ROOT = Path(__file__).resolve().parent.parent
PUBLIC_FILES = (
    "README.md", "README.zh-CN.md", "REVIEW.md", "EPOCH.md", "PROVENANCE.md",
    "cache/README.md", ".gitattributes", "LICENSE", "NOTICE", "CITATION.cff", ".zenodo.json", ".gitignore",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain", "SymplecticPacking.lean",
)
DOCUMENTS = (
    "overview/main",
    "p1/main", "p1/supplement",
    "p2/main", "p2/supplement",
    "p3/main",
    "p4/main",
)
PUBLIC_DIRS = ("SymplecticPacking", "verification", "vendor", "scripts", "test", ".github", "program")
# Explicitly allow-listed experimental research archive (kept outside `program/` and NOT certified).
EXPERIMENTAL_DIRS = ("experiments/hamiltonian_lift",)

MARKDOWN_DOCS_TO_CHECK = (
    "README.md", "README.zh-CN.md", "REVIEW.md", "EPOCH.md", "PROVENANCE.md",
    "paper/README.md", "program/README.md", "verification/README.md",
    "cache/README.md", "verification/PAPER-INDEX.md",
    "experiments/hamiltonian_lift/README.md",
    "experiments/hamiltonian_lift/DIAGNOSTICS.md",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def public_sources() -> dict[str, bytes]:
    paths = [ROOT / p for p in PUBLIC_FILES]
    for name in (*PUBLIC_DIRS, *EXPERIMENTAL_DIRS):
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


def check_relative_markdown_links(payload: dict[str, bytes]) -> None:
    payload_files = set(payload)
    payload_dirs = {str(PurePosixPath(p).parent) for p in payload_files}
    # Strip fenced code blocks before scanning markdown links.
    fence_re = re.compile(r"```.*?```", re.DOTALL)
    link_re = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
    for doc in MARKDOWN_DOCS_TO_CHECK:
        text = fence_re.sub("", payload[doc].decode("utf-8"))
        base = PurePosixPath(doc).parent
        for raw_target in link_re.findall(text):
            target = raw_target.strip().split("#", 1)[0]
            if not target or re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target):
                continue
            # Resolve POSIX relative path manually.
            parts: list[str] = []
            for part in (base / PurePosixPath(target)).parts:
                if part in ("", "."):
                    continue
                if part == "..":
                    if not parts:
                        raise RuntimeError(f"{doc}: link escapes archive root: {raw_target}")
                    parts.pop()
                else:
                    parts.append(part)
            resolved = "/".join(parts)
            # `cache/README.md` is shipped while binary `cache/lean/*` is intentionally omitted from history-free zip.
            if resolved in payload_files or resolved in payload_dirs:
                continue
            raise RuntimeError(f"{doc}: broken relative link inside release archive: {raw_target} -> {resolved}")


def main() -> None:
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    metadata = json.loads((ROOT / ".zenodo.json").read_text())
    citation = (ROOT / "CITATION.cff").read_text()
    # The release version is the publication version (citation and archive metadata). The Lake
    # package version is the version of the Lean development, which may be older: changing it
    # would change the proof-source digest without changing any proof.
    version = metadata["version"]
    if not re.fullmatch(r"\d+\.\d+\.\d+", version) or not re.fullmatch(r"\d+\.\d+\.\d+", config["version"]):
        raise RuntimeError("expected three-part versions")
    if f'version: "{version}"' not in citation:
        raise RuntimeError("citation and archive metadata versions disagree")
    if f'date-released: "{metadata["publication_date"]}"' not in citation:
        raise RuntimeError("citation and archive dates disagree")

    print("Checking source-bound numerical verification receipt...", flush=True)
    subprocess.run([sys.executable, "scripts/verify_numerical_receipt.py", "--check"], cwd=ROOT, check=True)

    before = public_sources()
    log = ROOT / ".lake" / "verify" / "submission.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    print("Verifying sources, paper tags, Lean proofs, regressions, overview, and all four papers...", flush=True)
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

    numerical_receipt_rel = "program/release-check/NUMERICAL-VERIFICATION.json"
    numerical_receipt = json.loads(before[numerical_receipt_rel].decode("utf-8"))

    payload = dict(before)
    page_counts = {}
    for doc in DOCUMENTS:
        pdf = ROOT / "paper" / doc.split("/")[0] / "build" / f"{doc.split('/')[1]}.pdf"
        data = pdf.read_bytes()
        if not data.startswith(b"%PDF-"):
            raise RuntimeError(f"invalid PDF: {doc}")
        payload[f"paper/{doc}.pdf"] = data
        match = re.search(rf"{doc}: (\d+) pages, 0 undefined references, 0 multiply defined labels, 0 overfull boxes",
                          verification_log)
        if not match:
            raise RuntimeError(f"missing successful paper check: {doc}")
        page_counts[doc] = int(match[1])

    check_relative_markdown_links(payload)

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
        "numerical_verification_receipt": {
            "path": numerical_receipt_rel,
            "sha256": sha256(before[numerical_receipt_rel]),
            "verified_at_utc": numerical_receipt["verified_at_utc"],
            "result": numerical_receipt["result"],
            "live_runs_count": len(numerical_receipt["live_runs"]),
        },
        "experimental_unverified_dirs": list(EXPERIMENTAL_DIRS),
        "checks": [
            "source hygiene and bundle reproducibility",
            "paper declaration tags",
            "Lean library and verification build (including RK4Convergence)",
            "axiom and explicitness audits",
            "full proof-dependency independence audit",
            "checker regression tests",
            "overview and four-paper compilation and cross-references",
            "source-bound numerical verification receipt check",
            "archive relative-link integrity check",
        ],
    }
    receipt_bytes = (json.dumps(receipt, ensure_ascii=False, indent=2) + "\n").encode()
    payload["RELEASE-VERIFICATION.json"] = receipt_bytes
    payload["KERNEL-REPLAY.json"] = kernel_receipt_path.read_bytes()
    payload["MANIFEST.sha256"] = "".join(
        f"{sha256(data)}  {name}\n" for name, data in sorted(payload.items())).encode()

    out = ROOT / "release"
    if out.exists():
        shutil.rmtree(out)
    out.mkdir()
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

    pdfs = []
    for doc in DOCUMENTS:
        paper, name = doc.split("/")
        target = out / f"{paper}-{name}.pdf"
        shutil.copyfile(ROOT / "paper" / paper / "build" / f"{name}.pdf", target)
        pdfs.append(target)
    (out / "verification.json").write_bytes(receipt_bytes)
    outputs = [archive, *pdfs, out / "verification.json"]
    (out / "SHA256SUMS").write_text("".join(f"{sha256(p.read_bytes())}  {p.name}\n" for p in outputs))
    print(f"PASS: {archive.name}; {len(before)} source files; PDFs {page_counts}", flush=True)
    print("Archive contents, relative links, numerical receipt, and checksums verified.", flush=True)


if __name__ == "__main__":
    main()
