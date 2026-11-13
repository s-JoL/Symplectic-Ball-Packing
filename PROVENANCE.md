# Publication and provenance

## Version 1.2.0

Liang Song, version **1.2.0**, 13 November 2026. Version 1.2.0 extends the four-paper layout introduced at Git tag
`v1.1.0` (`dc469737bd9a17df9002eec2338ed734877509d3`) with the 4-page series overview (`paper/overview`), formal
perturbed fixed-step RK4 containment and quantitative trajectory-certificate theorems (`verification/RK4Convergence.lean`,
Paper I Corollary D), an expanded Paper IV (`paper/p4`) with a self-contained inverse-certificate proof and
radial–Alexander generator analysis (§8), strengthened checks for the existing closed-form `C⁴` embedding evaluator
and AST-transformed `mpmath` checker (`program/embedding_src/`, `program/solution_embedding.py`, `program/check_embedding_mp.py`), the
Epoch problem guide (`EPOCH.md`), a reproducible numerical verification receipt
(`program/release-check/NUMERICAL-VERIFICATION.json`), and a separately labelled experimental archive
(`experiments/hamiltonian_lift/`, excluded from `program/` and certified deliverables). The
all-version DOI [10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575) resolves to the latest deposited
version; the version DOI of 1.2.0 is assigned by Zenodo on deposit. The record keeps the series title
*Explicit Hamiltonian ball packings in every dimension*, the title of version 1.0.1; the four papers carry their own
titles.

1. **Papers I and II (`paper/p1`, `paper/p2`):** The single paper of 1.0.1 was split in 1.1.0 into **Paper I**
   (shortest complete route to the equal-ball theorem in the four-ball for all `k ≥ 10` and `ε ∈ (0, 1)`, robustness,
   Epoch data, plus in 1.2.0 Corollary D on uniform perturbed fixed-step RK4 containment with explicit `δ₀` and `N₀`)
   and **Paper II** (general capacities in dimension four and all higher dimensions, Siegel–Yao criterion, Biran's
   `k ≥ 9`, unequal-ball cone, full Epoch data, and the uniform terminating rational polynomial-cutoff algorithm). No
   theorem or proof of 1.0.1 is removed.
2. **Papers III and IV (`paper/p3`, `paper/p4`) and `program/`:** **Paper III** (*Elementary packings of the four-ball
   and their limits*) proves toric/window constructions and three density obstructions. **Paper IV** (*Closed-form
   symplectic packings of the four-ball by equal balls*) proves the ODE-free `C⁴` symplectic embedding chain, exact-real
   non-membership `Preimage` certificates (including Lemma 7.4), universal parameter validity `(H0)–(H15)` for all
   `k ≥ 10` and `ε ∈ (0, 1)`, and a radial–Alexander generator formula in terms of a normalised primitive with abstract
   ODE trajectory certificates (Proposition 8.1). The global lift of these direct maps remains unfinished.
   **`program/`** contains two accompanying Python implementations: `solution_epoch.py`
   (fast PyTorch Hamiltonians in Epoch's ODE format over Paper III's elementary `(k, ε)` regime) and
   `solution_embedding.py` (built deterministically from `program/embedding_src/`, with `check_embedding.py` and
   100-digit `mpmath` `check_embedding_mp.py`).
3. **Lean 4 formalisation (`SymplecticPacking/`, `verification/`):** **All 525 Lean source files in `SymplecticPacking/`,
   `Problem.lean`, `Statement.lean`, `Computability.lean`, and `EpochComputability.lean` are byte-identical to 1.0.1 and
   1.1.0.** Version 1.2.0 adds `verification/RK4Convergence.lean` (`epoch_rk4_convergence`,
   `epoch_exact_rk4_convergence`, `picard_lindelof_curve_unique`, `picard_lindelof_epoch_certificate`), updates the
   audit entry points (`verification/Kernel.lean`, `verification/Audit/Independence.lean`), repacks the optional project
   cache (723 compiled modules with corresponding current sources), and re-runs a fresh kernel replay of the full imported declaration closure of
   `verification.Kernel`.
4. **Bibliography corrections:** Traynor, *Symplectic packing constructions*, J. Differential Geom. **42** (1995),
   411–429 (corrected in 1.1.0); Opshtein, *Symplectic packings in dimension 4 and singular curves*, J. Symplectic Geom. **13** (2015),
   305–342 (unified across Papers I–III in 1.2.0).

## Version 1.1.0

Liang Song, version **1.1.0**, 13 November 2026 (Git tag `v1.1.0`, commit
[`dc469737bd9a17df9002eec2338ed734877509d3`](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/v1.1.0)). Split the
1.0.1 manuscript into Papers I and II, added Papers III and IV (§§1–7), and included both accompanying programs:
`program/solution_epoch.py` (superseding `examples/packing.py`, `examples/k10.py`, and `verification/Executable.lean`)
and `program/solution_embedding.py`, its modular sources `program/embedding_src/`, deterministic builder and direct
`mpmath` source checker. The shared Lean library and principal theorem/algorithm sources remained unchanged from
1.0.1. Version 1.2.0 revises and extends these existing deliverables; it does not first introduce Paper IV or the
direct embedding program.

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

### Checking a release archive

The matching GitHub and Zenodo downloads contain the PDFs, `symplectic-ball-packing-<version>.zip`,
`verification.json`, `PUBLICATION-PROVENANCE.json` (on archived releases), and `SHA256SUMS`. The ZIP contains the
history-free public sources and PDFs, `RELEASE-VERIFICATION.json`, `KERNEL-REPLAY.json` and `MANIFEST.sha256`
(and in 1.2.0, `program/release-check/NUMERICAL-VERIFICATION.json` plus the separately labelled
`experiments/hamiltonian_lift/` research archive). It excludes Git history and optional binary proof caches.

After downloading the deposited files into one directory, run:

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
