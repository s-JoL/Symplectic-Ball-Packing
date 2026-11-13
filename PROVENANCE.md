# Publication and provenance

## Version 1.1.0

Liang Song, version **1.1.0**, 13 November 2026. Version 1.1.0 reorganises the work into four papers and adds
two accompanying Python programs. The all-version DOI
[10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575) resolves to the latest version; the version DOI of
1.1.0 is assigned by Zenodo on deposit. The record keeps the series title *Explicit Hamiltonian ball packings in every
dimension*, the title of version 1.0.1; the four papers carry their own titles.

1. The single paper of 1.0.1 is split and shortened. **Paper I** (`paper/p1`) gives the shortest complete
   route to the equal-ball theorem in the four-ball (Theorem A, robustness, the Epoch data for k ≥ 10).
   **Paper II** (`paper/p2`) contains the general theorem for all admissible data in every dimension, the
   corollaries (Siegel–Yao criterion, Biran's k ≥ 9, a cone of unequal balls, full Epoch data) and the
   finite-output algorithm. No theorem or proof of 1.0.1 is removed.
2. **Paper III** (`paper/p3`), *Elementary packings of the four-ball and their limits*, and **Paper IV** (`paper/p4`),
   *Closed-form symplectic packings of the four-ball by equal balls*, are new; neither is formalised in Lean.
   **`program/`** is new: `solution_epoch.py` provides a fast numerical implementation for the Epoch ODE interface
   built from Paper III's constructions over a covered range of `(k, ε)`, and `solution_embedding.py` (built
   deterministically from modular sources in `program/embedding_src/`) evaluates the closed-form C⁴ packing embeddings
   and cancellation-free inverses proved in Paper IV, accompanied by float64 and 100-digit `mpmath` checkers.
3. Corrected citation: Traynor, *Symplectic packing constructions*, J. Differential Geom. **42**
   (1995), 411–429 (1.0.1 cited a duplicate record).
4. The reference scripts added to `main` after 1.0.1 (`examples/packing.py`, `examples/k10.py`,
   `verification/Executable.lean`) are superseded by `program/` and remain in the Git history.
5. **Lean sources, statements and proofs are byte-identical to 1.0.1**, as are the Lake package
   version and the optional project cache. The paper-tag index is regenerated from the new paper sources
   and names the same 1240 declarations.

## Version 1.0.1

Liang Song, *Explicit Hamiltonian ball packings in every dimension*, version **1.0.1**,
29 October 2026. The archive includes the manuscript, supplement and Lean development.

- Version DOI: [10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498).
- All-version DOI: [10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575).
- Deposited files: [Zenodo record](https://zenodo.org/records/23763498).
- Fixed GitHub release: [v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/releases/tag/v1.0.1).
- Fixed source tree: [v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/v1.0.1).
- Fixed reviewer guide: [guide at v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.1/REVIEW.md).

Use the version DOI when citing a version. The all-version DOI resolves to the latest
published version. A later change to `main` does not alter a fixed release or its DOI files.

### Changes from 1.0.0

1. The six-dimensional relative Moser paragraph now uses the compact support bound
   `‖X‖² ≤ 6`: the correction has `|X₀|² ≤ 2` and `‖X′‖² ≤ 4`. The Lean support bound was already 6.
2. Rational auxiliary capacities are obtained by density in a nonempty real open set,
   after a sufficiently small positive increase in each coordinate.
3. The formalisation appendix records the existing compact swept support set and its
   containment in the explicit support ball.
4. The verification guide notes the separation between per-push CI and the `full-build` / `kernel-replay` workflows.
5. The scalar comparator's opening comment identifies the fixed mollifier construction,
   separately from the general polyhedral log-sum-exp construction.

No Lean definition, theorem statement or proof changed. Release packaging runs the source checks,
Lean build, axiom/explicitness/independence audits, regression tests, paper builds,
and a fresh kernel replay bound to the current proof sources and compiled objects.

### Checking the 1.0.1 release

The matching GitHub and Zenodo downloads contain `main.pdf`, `supplement.pdf`,
`symplectic-ball-packing-1.0.1.zip`, `verification.json`, `PUBLICATION-PROVENANCE.json`,
and `SHA256SUMS`. The ZIP contains the history-free public sources and PDFs,
`RELEASE-VERIFICATION.json`, `KERNEL-REPLAY.json` and `MANIFEST.sha256`.
It excludes Git history and optional binary proof caches.

After downloading the six deposited files into one directory, run:

```sh
shasum -a 256 -c SHA256SUMS
```

Inside the extracted ZIP, run the same command with `MANIFEST.sha256`.
The external `PUBLICATION-PROVENANCE.json` binds the release commit and Git tree to the
file hashes and proof-verification receipt. Keeping it outside the Git tree and ZIP
avoids a self-referential commit or archive hash.

### Original 1.0.0 archive and compatibility links

The original [version DOI](https://doi.org/10.5281/zenodo.23756576) and its seven files
remain unchanged. Its former GitHub release page and tag were removed after a Git
committer-identity correction. The corrected publication commit
[`baf33f27ba2d4eae32dcae795d5c9a79a39ad368`](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/baf33f27ba2d4eae32dcae795d5c9a79a39ad368)
has the same original file tree, `7d20dc4221190aecf89b3dff49e674db750f8f9c`.
The compatibility **branch** `v1.0.0` preserves previously shared
[source-file links](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.0/REVIEW.md);
it is not a release tag.

The original 1.0.0 archive preserves its original commit and provenance file, to which its
OpenTimestamps proof applies. For the corrected manuscript and formalisation, cite version 1.0.1 or later.
