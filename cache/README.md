# Optional Lean proof cache

The bundled cache is **32.2 MiB for 722 modules**. `lean/manifest.json` describes a cache of this project's compiled Lean modules, compressed
with the pinned toolchain's `leantar` (the format used by Mathlib). Parts are capped at 40 MiB
for ordinary Git hosting. The manifest records the toolchain, proof-source digest, module
count, total size, and SHA-256 checksums. No Git LFS or extra compression program is required.

From the repository root:

```sh
lake exe cache get
bash scripts/verify.sh --lean
bash scripts/check_kernel.sh
```

The bundled cache is for the archived proof sources. The current executable
algorithm adds Lean modules, so its source digest differs: build current project
sources with the commands above. `python3 scripts/project_cache.py restore` is
optional on matching revisions; a source mismatch exits with code 2 before
extracting anything. CI automatically chooses a source build in that case.

The project cache contains `.olean`, `.ilean`, generated C, artifact hashes, and freshness
traces. It excludes Mathlib's dependency cache, executables, the multi-gigabyte `.setup.json`
files, PDF build intermediates, research notes, and Git history. The history-free source-and-PDF
submission bundle excludes these optional binary cache parts altogether.

Checksums detect damaged or mismatched cache data. A successful cache restore is not a proof
check. Kernel replay checks stored proof terms with Lean's kernel; a clean source build checks
source elaboration without this project cache. The [reviewer guide](../REVIEW.md) explains the
difference. To regenerate the cache after changing proof sources, run:

```sh
python3 scripts/project_cache.py pack
```

Packing first runs every source, Lean, axiom, explicitness, independence, and regression gate.
The cache is keyed by sources rather than a commit hash so that it can be included in the same
single source commit without a circular commit reference.
