# Symplectic Ball Packing

**Explicit Hamiltonian ball packings in every dimension**

Paper, complete supplement, and Lean 4 proofs by Liang Song.

[![Verification](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23756576.svg)](https://doi.org/10.5281/zenodo.23756576)

Version **1.0.1**, 29 October 2026. [Archived publication and files](https://doi.org/10.5281/zenodo.23763498) ·
[Fixed release](https://github.com/s-JoL/Symplectic-Ball-Packing/releases/tag/v1.0.1) · [Publication and provenance](PROVENANCE.md).

This revision corrects two supplementary arguments and three documentation/comment issues;
Lean definitions, theorem statements and proofs are unchanged. See the
[revision notes](PROVENANCE.md#changes-from-100). The optional proof cache and verification
receipts correspond to this version.

For fixed links, use the [source tree](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/v1.0.1)
and [reviewer guide](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.1/REVIEW.md).
The [original 1.0.0 DOI archive](https://doi.org/10.5281/zenodo.23756576) remains available;
its former GitHub release page is unavailable.

[Paper](paper/main.pdf) · [Supplement](paper/supplement.pdf) · [Reviewer guide](REVIEW.md) · [中文导读](README.zh-CN.md) · [Formal statements](verification/Statement.lean)

## What this work does

Symplectic ball packing asks how balls can be moved into a larger ball while preserving the
standard symplectic form. This work gives a single explicit Hamiltonian construction: a
smooth, compactly supported time-dependent function whose flow performs the packing from
prescribed initial positions. Its main packing, stability, and computability theorems are
formalised in Lean 4.

For every integer **k ≥ 10** and **0 < ε < 1**, the construction moves the k closed unit balls
centred at `(3i, 0, 0, 0)`, `0 ≤ i < k`, into the four-dimensional ball of radius

```text
R = (k / (1 − ε/4))^(1/4),     occupied volume fraction = k/R^4 = 1 − ε/4 > 1 − ε.
```

The formulas work for all admissible inputs. A separate uniform computability theorem gives
a terminating algorithm with finite output, a rational polynomial times a fixed smooth
cutoff. This is a mathematical construction and computability result; the algorithm has no
practical runtime bound. The paper explains its relation to Epoch AI's
[program submission requirements](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing).

## Results at a glance

Here `B(c) = {z : π‖z‖² ≤ c}` denotes a ball of **capacity** c; the source balls are closed,
the target is open, and the prescribed source balls must be pairwise disjoint. The general
results assume n ≥ 2, k ≥ 1, C > 0, and every cᵢ > 0.

| Result | Precise scope | Lean entry |
|---|---|---|
| Four-ball motion (Theorem A) | k ≥ 10 unit balls, density 1 − ε/4 | [`four_dim_theorem`](verification/Statement.lean) |
| Robustness (Proposition B) | Explicit vector-field error margin for density > 1 − ε | [`four_dim_stability`](verification/Statement.lean) |
| General motion (Theorem C) | n ≥ 3: Σcᵢⁿ < Cⁿ and cᵢ+cⱼ < C; n = 2: Σcᵢ² < C² and 3cᵢ < C | [`main_theorem`](verification/Statement.lean) |
| Finite-output algorithm | One oracle program, certified output, termination on every admissible input | [`original_name_algorithm`](verification/Computability.lean), [`epoch_name_algorithm`](verification/EpochComputability.lean) |
| Further consequences | Higher-dimensional packing criterion; four-ball stability for k ≥ 9; unequal capacities in a specified cone | [`Statement.lean`](verification/Statement.lean) |

The construction develops the twisted disc-bundle mechanism of the OpenAI preprint
*Symplectic Ball Packings in Higher Dimensions* (2026). The four-dimensional ingredients are
a linear comparison identity, explicit planar rearrangements, a Fermat cubic model with a
symmetry-controlled return to the ball, and one global Hamiltonian motion. The construction
and its sufficiency proofs avoid packing existence theorems, J-holomorphic curves, and
Seiberg–Witten theory. The necessity direction of the higher-dimensional criterion uses the
classical obstructions, including the holomorphic-line two-ball obstruction.

## Read a small part first

- **For a referee:** [REVIEW.md](REVIEW.md) gives the claims, hypotheses, novelty, proof route,
  formal counterparts, and verification boundaries in one place.
- **For a formalisation reviewer:** read [`Problem.lean`](verification/Problem.lean), then
  [`Statement.lean`](verification/Statement.lean). The problem definitions import Mathlib
  alone. [`Algorithm.lean`](verification/Algorithm.lean) ties the statements to the defined
  Hamiltonian; the two computability entry files specify the finite-output algorithms.
- **For a first explanation, including AI-assisted reading:** start with the
  [中文导读](README.zh-CN.md). The [paper-to-Lean index](verification/PAPER-INDEX.md) locates
  individual supporting results without reading the entire development.

## Verify

Requirements: [Elan](https://github.com/leanprover/elan), Node.js 22 or newer, Python 3.11 or
newer. The optional project cache uses `leantar`, included in the pinned Lean toolchain.
Tectonic 0.15.0 builds the papers. Lean and
all Lean dependencies are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
git clone https://github.com/s-JoL/Symplectic-Ball-Packing.git
cd Symplectic-Ball-Packing
lake exe cache get                      # official Mathlib dependency cache
python3 scripts/project_cache.py restore # optional, checksum-checked project cache
bash scripts/verify.sh --lean            # source checks, all Lean targets and audit regressions
```

Success ends with `VERIFY PASS`. The script re-elaborates the main review entries, paper-tag
axiom gates, independence gate, and checker regressions even after a cache restore.
The cache is an acceleration artifact: a cache hit alone
does not re-check an imported proof. For kernel replay, after the build run:

```sh
bash scripts/check_kernel.sh
```

This uses the pinned toolchain's `leanchecker --fresh` to replay the complete declaration
closure into a fresh kernel environment. It reuses compiled proof terms and avoids tactic
elaboration. It uses the same Lean kernel, rather than an independently implemented checker;
see the [verification guide](verification/README.md) for the remaining trust boundary.

For a source rebuild, start with an empty `.lake/build`, omit the optional project-cache
restore, and run the commands above. This can take several hours. The CI workflow
[`full-build.yml`](.github/workflows/full-build.yml) does exactly that with only Mathlib's
cache and includes fresh kernel replay. [`verify.yml`](.github/workflows/verify.yml) uses the
bundled project cache, rechecks the short source entries and audit/regression gates, and
uploads the papers and logs. [`kernel-replay.yml`](.github/workflows/kernel-replay.yml)
provides the stronger full kernel replay as a separate manual workflow. Every requested
check is fatal; cache-based review and full kernel replay are reported separately.

With Tectonic installed, `bash scripts/verify.sh` additionally compiles both papers and checks
citations, cross-references, duplicate labels, and overfull boxes. The PDF files linked above
are included for direct reading; the TeX sources are in [`paper/`](paper/README.md).

## What is trusted

The Lean kernel; the formal definitions in `verification/Problem.lean`; Mathlib and the
vendored generic geometry; and the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
Axiom gates reject any additional axiom, including `sorryAx`. Explicitness, algorithm
uniformity, and proof-dependency independence are checked by metaprograms with positive and
negative regression cases; those metaprograms are not themselves formally verified.

The unmodified upstream library and its provenance are retained in [`vendor/NOTICE`](vendor/NOTICE).
The definitions of the packing Hamiltonians and finite-output algorithms are this project's
own. Formal correctness concerns the exact Lean statements; their correspondence with the
mathematical problem remains an essential part of human review.

## Citation, authorship, and reuse

Use [`CITATION.cff`](CITATION.cff) to cite *Explicit Hamiltonian ball packings in every dimension*.
The version DOI is [10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498).
Liang Song is the sole author and is responsible for the manuscript. The mathematics, Lean
formalisation, and text were produced with AI systems in a research environment designed and
directed by Liang Song. The manuscript records the authorship and AI contribution in full.

Licensed under [Apache-2.0](LICENSE), with upstream attribution in [NOTICE](NOTICE) and
[vendor/NOTICE](vendor/NOTICE). `python3 scripts/package_release.py` produces a verified,
history-free source-and-PDF bundle and checksum manifest locally; it runs all build gates and
requires a kernel-replay receipt bound to the current proof sources and objects (running the
replay if necessary). It does not publish the bundle.
