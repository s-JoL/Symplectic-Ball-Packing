# Symplectic Ball Packing

**Explicit Hamiltonian ball packings, with Lean 4 proofs.** By Liang Song.

[![Verification](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

Version **1.1.0**. The previous version, 1.0.1, is archived under
[DOI 10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498); see [PROVENANCE.md](PROVENANCE.md).
[中文导读](README.zh-CN.md) · [Reviewer guide](REVIEW.md)

## The result

For every integer **k ≥ 10** and **0 < ε < 1**, one explicit smooth compactly supported
Hamiltonian on ℝ × ℝ⁴ has a time-one map that carries the k closed unit balls centred at
`(3i − 3, 0, 0, 0)`, `1 ≤ i ≤ k`, into the ball of radius

```text
R = (k / (1 − ε/4))^(1/4),     occupied volume fraction  k/R⁴ = 1 − ε/4.
```

Biran proved in 1997 that such packings exist, using J-holomorphic curves and Seiberg–Witten theory,
which give no motion; explicit full packings by k ≥ 10 equal balls were known only for square k. Here the
motion is given by formulas, for every k ≥ 10, without those methods. This answers the mathematical part of the
construction problem posed by [Epoch AI](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing).
All main theorems of Papers I–II are checked in Lean 4 against a problem statement written from Mathlib alone,
using only the three standard axioms. The construction is designed for proof. Two separate programs accompany it: one runs in Epoch's numerical
interface for a range of (k, ε); the other evaluates explicit packing embeddings for every k ≥ 10 and every ε.

## Papers and programs

| | Paper | Main results | Lean |
|---|---|---|---|
| I | *Explicit Hamiltonian full packings of the four-ball by equal balls* — [paper](paper/p1/main.pdf) (21 pp), [supplement](paper/p1/supplement.pdf) | Theorem A above, with the shortest complete route; robustness under perturbation of the vector field (Prop. B); the Epoch data for k ≥ 10 | yes |
| II | *Explicit Hamiltonian ball packings: general capacities, higher dimensions and the Siegel–Yao criterion* — [paper](paper/p2/main.pdf) (22 pp), [supplement](paper/p2/supplement.pdf) | One explicit Hamiltonian for all admissible data: in ℝ⁴ every packing with Σcᵢ² < C², 3cᵢ < C; in ℝ²ⁿ, n ≥ 3, every packing allowed by the volume and two-ball inequalities. Biran's theorem that B⁴ is fully packed by k ≥ 9 equal balls, without J-holomorphic curves or Seiberg–Witten theory. A terminating algorithm with finite output | yes |
| III | *Elementary packings of the four-ball and their limits* — [paper](paper/p3/main.pdf) (13 pp) | Toric and window constructions: n(n+1) balls in B(n+½); density ≥ 1 − 1/√k for every k; ten balls at density 360/361. Obstructions explaining why these methods stop short of density 1 for non-square k | no |
| | [`program/`](program/README.md) — `solution_epoch.py` | A runnable Hamiltonian in Epoch's interface built from the same kind of constructions as Paper III (lattice layouts found by search, windows, sheared windows): k = 10 down to ε = 0.005, squares to ε ≈ 0.002, every k ≤ 10⁵ above an explicit ε_min(k). Checked numerically (RK4 at N and 2N, 12/12 test points pass), not proved; the returned Hamiltonian is smooth near the ball trajectories but not globally (see its README) | no |
| | [`program/`](program/README.md) — `solution_embedding.py` | Explicit C⁴ symplectic embeddings packing k unit balls into B⁴((k/(1−ε))^{1/4}) for **every** k ≥ 10 and ε ∈ (0, 1), each a composition of closed-form maps (the geometry of Paper I, without flows). Not a Hamiltonian. Proof for exact arithmetic in preparation; float64 sampling checks pass containment and disjointness in all tested cases, the full check only for k = 10, ε ≥ 0.01 (resolution limits; see its README) | no |

The constructions of Papers I and II develop the twisted disc-bundle mechanism of the OpenAI
preprint *Symplectic Ball Packings in Higher Dimensions* (2026), which treats dimension 2n ≥ 6. The
four-dimensional ingredients are new: a linear comparison identity, a Fermat cubic disc-bundle model and a
return to the ball controlled by a cube-root symmetry.
In dimensions 2n ≥ 6, where that preprint proved existence, Paper II makes every step explicit: a finite
rational iterate in place of the fixed point, explicit planar rearrangements and Moser flows, and explicit
returns to the ball.

## Checking the claims

The formal statements are short. Read [`verification/Problem.lean`](verification/Problem.lean)
(definitions, from Mathlib only), then [`verification/Statement.lean`](verification/Statement.lean)
(the theorems). [REVIEW.md](REVIEW.md) maps them to the papers and states what the checks do and
do not establish.

```sh
git clone https://github.com/s-JoL/Symplectic-Ball-Packing.git
cd Symplectic-Ball-Packing
lake exe cache get                         # Mathlib cache
python3 scripts/project_cache.py restore   # optional: prebuilt project cache
bash scripts/verify.sh                     # source checks, Lean build and audits, papers
```

A build without the project cache takes several hours. Requirements: [Elan](https://github.com/leanprover/elan),
Node.js ≥ 22, Python ≥ 3.11, and [Tectonic](https://tectonic-typesetting.github.io) for the papers.
Details: [`verification/README.md`](verification/README.md).

**Trusted base:** the Lean kernel, Mathlib, `verification/Problem.lean`, and the axioms `propext`,
`Classical.choice`, `Quot.sound`. Explicitness and uniformity of the algorithm are checked by
metaprograms that are not themselves verified. The correspondence between the formal statements and
the mathematics is for human review.

## Citation and authorship

Cite with [`CITATION.cff`](CITATION.cff). Liang Song is the sole author and is responsible for
the work. The mathematics, the Lean formalisation and the text were produced by AI systems in
a research environment designed and directed by Liang Song; each paper states this in full.

Licensed under [Apache-2.0](LICENSE). The vendored library in `vendor/` keeps its own notices
([NOTICE](NOTICE), [vendor/NOTICE](vendor/NOTICE)).
