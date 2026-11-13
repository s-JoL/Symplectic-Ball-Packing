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

More generally, one explicit Hamiltonian realises every four-dimensional packing with `Σcᵢ² < C²` and `3cᵢ < C`—giving
full packings by **k ≥ 9** equal balls—and in dimensions **2n ≥ 6** realises every packing allowed by the volume and
Gromov two-ball inequalities. Biran proved in 1997 that full packings exist for k ≥ 9 in dimension four using
J-holomorphic curves and Seiberg–Witten theory, which produce no motion; explicit full packings by k ≥ 10 equal balls
were previously known only for square k. Here the motions are given by explicit formulas without J-holomorphic curves
or Seiberg–Witten theory, accompanied by a uniform terminating algorithm outputting a rational polynomial times a fixed
spatial cutoff.

All main theorems of Papers I–II are checked in Lean 4 against a problem statement written from Mathlib alone, using
only the three standard axioms. These results resolve the mathematical and computability parts of
[Epoch AI's symplectic ball-packing problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing).
Because the exact smooth non-toric flow is too stiff for fixed-step float64 integration within Epoch's runtime limits,
two Python programs explore complementary numerical routes: one runs in Epoch's ODE Hamiltonian interface over an
elementary `(k, ε)` regime (studied in Paper III); the other evaluates closed-form C⁴ packing embeddings directly
without ODEs for every `k ≥ 10` and `ε ∈ (0, 1)` over ℝ (proved in Paper IV).

## Papers and programs

| | Paper / Program | Main results | Lean |
|---|---|---|---|
| I | *Explicit Hamiltonian full packings of the four-ball by equal balls* — [paper](paper/p1/main.pdf) (21 pp), [supplement](paper/p1/supplement.pdf) | Theorem A above via the shortest direct route (linear comparison identity and Z/3-symmetric return); robustness under vector-field perturbation (Prop. B); the Epoch data for k ≥ 10 | yes |
| II | *Explicit Hamiltonian ball packings: general capacities, higher dimensions and the Siegel–Yao criterion* — [paper](paper/p2/main.pdf) (22 pp), [supplement](paper/p2/supplement.pdf) | One explicit Hamiltonian for all admissible data: in ℝ⁴ every packing with Σcᵢ² < C², 3cᵢ < C (including Biran's full-packing theorem for k ≥ 9 equal balls without J-holomorphic curves or Seiberg–Witten theory); in ℝ²ⁿ, n ≥ 3, every packing allowed by the volume and two-ball inequalities. A uniform terminating algorithm with finite polynomial-cutoff output | yes |
| III | *Elementary packings of the four-ball and their limits* — [paper](paper/p3/main.pdf) (13 pp) | Toric and window constructions: n(n+1) balls in B(n+½); density ≥ 1 − 1/√k for every k; ten balls at density 360/361. Three rigorous obstructions explaining why lattice, balanced-profile, and 8-column configurations stop short of density 1 for non-square k | no |
| IV | *Closed-form symplectic packings of the four-ball by equal balls* — [paper](paper/p4/main.pdf) (14 pp) | Complete exact-real proof for the ODE-free C⁴ embedding chain: Knothe–Rosenblatt strip map, generating-function keyholes with full-disc bounds, C⁴ marked-fibre corridor twists, piecewise closed-form simplex transfer, and analytic validity of `(H0)–(H15)` for all k ≥ 10, ε ∈ (0, 1) | no |
| | [`program/`](program/README.md) — `solution_epoch.py` | Fast PyTorch Hamiltonian generator in Epoch's ODE interface built from Paper III's elementary constructions: k = 10 down to ε = 0.005, squares to ε ≈ 0.002, every k ≤ 10⁵ above an explicit `eps_min(k)`. Checked numerically (RK4 at N and 2N, 12/12 test points pass, ≤ 0.13 s/call); has exterior branch cuts away from trajectories and a C² window seam for k = 10 | no |
| | [`program/`](program/README.md) — `solution_embedding.py` ([`embedding_src/`](program/embedding_src/)) | Closed-form C⁴ symplectic embeddings `Embed(i, X)` and cancellation-free left inverses `Preimage(j, Y)` implementing Paper IV (not a Hamiltonian). Covers all k ≥ 10, ε ∈ (0, 1) over ℝ (in float64, guards against parameter underflow below ε ≈ 10⁻¹⁵); checked on special + random samples in float64 (`check_embedding.py`) and by direct 100-digit execution of the submitted source (`check_embedding_mp.py`) | no |

The constructions of Papers I, II and IV develop the twisted disc-bundle mechanism of the OpenAI
preprint *Symplectic Ball Packings in Higher Dimensions* (2026), which proved packing existence in dimensions 2n ≥ 6.
The four-dimensional ingredients are new: a linear comparison identity (Papers I & IV) and scalar comparison datum
(Paper II), a Fermat cubic disc-bundle model, and a return to the ball avoiding the line at infinity.
In dimensions 2n ≥ 6, Paper II makes every step of the existence proof explicit: a finite rational iterate in place of
the contraction fixed point, explicit planar convex rearrangements and finite-atlas Moser flows, and explicit returns
to the ball.

## Checking the claims

The formal statements are short. Read [`verification/Problem.lean`](verification/Problem.lean)
(definitions, from Mathlib only), then [`verification/Statement.lean`](verification/Statement.lean)
(the theorems). [REVIEW.md](REVIEW.md) maps them to the papers and summarises each verification layer.

```sh
git clone https://github.com/s-JoL/Symplectic-Ball-Packing.git
cd Symplectic-Ball-Packing
lake exe cache get                         # Mathlib cache
python3 scripts/project_cache.py restore   # optional: prebuilt project cache
bash scripts/verify.sh                     # source & bundle checks, Lean build & audits, all four papers
```

A build without the project cache takes several hours. Requirements: [Elan](https://github.com/leanprover/elan),
Node.js ≥ 22, Python ≥ 3.11, and [Tectonic](https://tectonic-typesetting.github.io) for the papers.
Details: [`verification/README.md`](verification/README.md).

**Trusted base:** the Lean kernel, Mathlib, `verification/Problem.lean`, and the axioms `propext`,
`Classical.choice`, `Quot.sound`. Explicitness and uniformity of the algorithm are audited by
metaprograms (`#check_explicit`, `#check_constructive`) described in [`verification/README.md`](verification/README.md).

## Citation and authorship

Cite with [`CITATION.cff`](CITATION.cff). Liang Song is the sole author and is responsible for
the work. The mathematics, the Lean formalisation, the code and the text were produced by AI systems in
a research environment designed and directed by Liang Song; each paper states this in full.

Licensed under [Apache-2.0](LICENSE). The vendored library in `vendor/` keeps its own notices
([NOTICE](NOTICE), [vendor/NOTICE](vendor/NOTICE)).
