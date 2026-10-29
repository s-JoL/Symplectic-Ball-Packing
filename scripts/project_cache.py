#!/usr/bin/env python3
"""Pack/restore only Lean build artifacts, using the pinned toolchain's leantar.

The optional cache is bound to all Lean sources and dependency configuration.
It is an acceleration artifact; use check_kernel.sh for fresh kernel replay.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT / "cache" / "lean"
PART_SIZE = 40 * 1024 * 1024


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def source_digest() -> str:
    paths = [ROOT / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "SymplecticPacking.lean")]
    for name in ("SymplecticPacking", "verification", "vendor", "test"):
        paths.extend((ROOT / name).rglob("*.lean"))
    h = hashlib.sha256()
    for p in sorted(paths):
        h.update(f"{digest(p)}  {p.relative_to(ROOT).as_posix()}\n".encode())
    return h.hexdigest()


def artifact_digest() -> str:
    h = hashlib.sha256()
    for p in sorted((ROOT / ".lake/build/lib/lean").rglob("*.olean")):
        h.update(f"{digest(p)}  {p.relative_to(ROOT / '.lake/build/lib/lean').as_posix()}\n".encode())
    return h.hexdigest()


def leantar() -> str:
    lean = subprocess.check_output(["elan", "which", "lean"], cwd=ROOT, text=True).strip()
    tool = Path(lean).with_name("leantar" + (".exe" if os.name == "nt" else ""))
    if not tool.is_file():
        raise RuntimeError("the pinned Lean toolchain does not contain leantar")
    return str(tool)


def pack() -> None:
    # Run all source/Lean/audit/regression gates before exporting the artifacts.
    subprocess.run(["bash", "scripts/verify.sh", "--lean"], cwd=ROOT, check=True)
    key = source_digest()
    traces = sorted((ROOT / ".lake/build/lib/lean").rglob("*.trace"))
    if not traces:
        raise RuntimeError("no compiled project modules; run the verification first")
    tool = leantar()
    with tempfile.TemporaryDirectory(prefix="symplectic-cache-") as d:
        tmp = Path(d)
        def compress(trace: Path) -> Path:
            rel = trace.relative_to(ROOT / ".lake/build/lib/lean").with_suffix("")
            stem = trace.name.removesuffix(".trace")
            files = [p for p in trace.parent.glob(stem + ".*") if p.is_file() and p != trace]
            ir = ROOT / ".lake/build/ir" / rel.parent
            files += [p for p in ir.glob(stem + ".*")
                      if p.is_file() and not p.name.endswith(".setup.json")]
            out = tmp / (".".join(rel.parts) + ".ltar")
            subprocess.run([tool, str(out), str(trace.relative_to(ROOT)),
                            *[str(p.relative_to(ROOT)) for p in sorted(files)]], cwd=ROOT, check=True)
            return out
        with ThreadPoolExecutor(max_workers=min(os.cpu_count() or 1, 8)) as pool:
            archives = list(pool.map(compress, traces))
        archive = tmp / "lean-cache.tar"
        with tarfile.open(archive, "w", format=tarfile.USTAR_FORMAT) as tar:
            for p in archives:
                info = tarfile.TarInfo(p.name)
                info.size = p.stat().st_size
                info.mode = 0o644
                with p.open("rb") as f:
                    tar.addfile(info, f)
        if source_digest() != key:
            raise RuntimeError("proof sources changed while packing")
        CACHE.mkdir(parents=True, exist_ok=True)
        previous = CACHE / "manifest.json"
        old_parts = json.loads(previous.read_text()).get("parts", []) if previous.exists() else []
        parts = []
        with archive.open("rb") as f:
            i = 0
            while block := f.read(PART_SIZE):
                i += 1
                name = f"lean-cache.part{i:02d}"
                target = CACHE / name
                target.write_bytes(block)
                parts.append({"name": name, "bytes": len(block), "sha256": digest(target)})
        manifest = {"schema": 1, "format": "tar-of-leantar", "source_sha256": key,
                    "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                    "modules": len(traces), "archive_bytes": archive.stat().st_size,
                    "archive_sha256": digest(archive), "parts": parts}
        previous.write_text(json.dumps(manifest, indent=2) + "\n")
        current = {p["name"] for p in parts}
        for old in old_parts:
            if old["name"] not in current and Path(old["name"]).name == old["name"]:
                (CACHE / old["name"]).unlink(missing_ok=True)
        print(f"CACHE PACK PASS: {len(traces)} modules; {archive.stat().st_size / 1024**2:.1f} MiB; {len(parts)} parts")


class CacheNotApplicable(RuntimeError):
    pass


def restore() -> None:
    if not (CACHE / "manifest.json").exists():
        raise CacheNotApplicable("no bundled cache; build from source")
    manifest = json.loads((CACHE / "manifest.json").read_text())
    if manifest.get("schema") != 1 or manifest.get("format") != "tar-of-leantar":
        raise RuntimeError("unsupported cache manifest")
    if manifest["lean_toolchain"] != (ROOT / "lean-toolchain").read_text().strip():
        raise CacheNotApplicable("cache toolchain mismatch")
    if manifest["source_sha256"] != source_digest():
        raise CacheNotApplicable("cache proof-source digest mismatch; build from source or repack")
    tool = leantar()
    with tempfile.TemporaryDirectory(prefix="symplectic-restore-") as d:
        tmp = Path(d)
        archive = tmp / "lean-cache.tar"
        with archive.open("wb") as out:
            for part in manifest["parts"]:
                name = part["name"]
                if Path(name).name != name or not name.startswith("lean-cache.part"):
                    raise RuntimeError("invalid cache part name")
                p = CACHE / name
                if p.stat().st_size != part["bytes"] or digest(p) != part["sha256"]:
                    raise RuntimeError(f"cache checksum mismatch: {name}")
                with p.open("rb") as f:
                    for block in iter(lambda: f.read(1024 * 1024), b""):
                        out.write(block)
        if archive.stat().st_size != manifest["archive_bytes"] or digest(archive) != manifest["archive_sha256"]:
            raise RuntimeError("cache archive checksum mismatch")
        inputs = []
        with tarfile.open(archive) as tar:
            members = tar.getmembers()
            if len(members) != manifest["modules"]:
                raise RuntimeError("cache module count mismatch")
            for member in members:
                if not member.isfile() or Path(member.name).name != member.name or not member.name.endswith(".ltar"):
                    raise RuntimeError("invalid cache archive member")
                p = tmp / member.name
                with tar.extractfile(member) as src, p.open("wb") as dst:
                    dst.write(src.read())
                inputs.append(str(p))
        # The native format preserves proof terms exactly; traces are reconstructed
        # by the same utility used for the official Mathlib cache.
        subprocess.run([tool, "-C", str(ROOT), "-f", "-x", *inputs], cwd=ROOT, check=True)
    print(f"CACHE RESTORE PASS: {manifest['modules']} modules; source {manifest['source_sha256'][:16]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("pack", "restore"))
    args = parser.parse_args()
    try:
        {"pack": pack, "restore": restore}[args.command]()
    except CacheNotApplicable as e:
        parser.exit(2, f"project cache not applicable: {e}\n")
    except (OSError, RuntimeError, KeyError, ValueError, subprocess.CalledProcessError, tarfile.TarError) as e:
        parser.exit(1, f"project cache: {e}\n")


if __name__ == "__main__":
    main()
