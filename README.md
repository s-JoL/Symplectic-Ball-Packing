# Symplectic Ball Packing

**Explicit Hamiltonian ball packings, with Lean 4 proofs.** By Liang Song.

[![Verification](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/s-JoL/Symplectic-Ball-Packing/actions/workflows/verify.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

Version **1.2.0**. Earlier versions are archived under [DOI 10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575)
(version 1.0.1: [DOI 10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498)); see [PROVENANCE.md](PROVENANCE.md).
[中文导读](README.zh-CN.md) · [4-page Overview (PDF)](paper/overview/main.pdf) · [Reviewer guide](REVIEW.md) · [Epoch problem guide](EPOCH.md)

## The result

Uniformly for every integer **k ≥ 10**—including non-square values such as **k = 10, 11, 12, …**—and every arbitrarily
small positive volume deficit **0 < ε < 1**, one explicit smooth (`C^∞`) compactly supported Hamiltonian on ℝ × ℝ⁴ has
a time-one map that carries the k closed unit balls centred at `(3i − 3, 0, 0, 0)`, `1 ≤ i ≤ k`, into the ball of radius

```text
R = (k / (1 − ε/4))^(1/4),     occupied volume fraction  k/R⁴ = 1 − ε/4.
```

More generally, one explicit Hamiltonian realises every four-dimensional packing with `Σcᵢ² < C²` and `3cᵢ < C`—giving
a new proof of Biran's full-packing theorem for **k ≥ 9** equal balls without J-holomorphic curves or
Seiberg–Witten theory—and in dimensions **2n ≥ 6** realises every packing allowed by the volume and
Gromov two-ball inequalities.

Biran established in 1997 the existence of arbitrarily dense equal-ball packings of the four-ball for every k ≥ 9.
Classical explicit full packings include the square-number constructions of Traynor and Schlenk; other constructive
approaches include folding, wrapping, tunnelling, constructions from singular symplectic curves and polarisations, and
almost toric methods. To our knowledge, the present work gives the first uniform explicit construction of a smooth
compactly supported Hamiltonian moving the prescribed source balls to arbitrarily dense packings for every non-square
k ≥ 10, within one family valid for all k ≥ 10 and every positive volume deficit. The construction and its
finite-output algorithm do not invoke J-holomorphic curves, Seiberg–Witten theory, or prior packing-existence theorems.

Lean 4 checks a named Hamiltonian against an independently stated specification: global smoothness (`C^∞`), uniform
compact spatial support, existence of global trajectories, and target containment for **every** integral curve starting
in **every** source ball. Separate formal theorems establish symplecticity and pairwise disjointness of the time-one
images, halting and certified finite output of the uniform rational polynomial-cutoff algorithm, quantitative
trajectory certificates, and eventual target containment for perturbed fixed-step RK4. The theorem statements,
constants and their computational scope are mapped in [EPOCH.md](EPOCH.md).

Papers I–II solve the mathematical construction and computability parts of
[Epoch AI's symplectic ball-packing problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing), and
Lean also proves the RK4 convergence-to-containment theorem above; producing a submission that meets the published
`float64` interface and runtime limits across all `(k, ε)` remains a separate implementation objective (see
[EPOCH.md](EPOCH.md)). Two accompanying Python programs in [`program/`](program/README.md) complement the formal proofs:
`solution_epoch.py` passes documented sampled `float64` RK4 and per-call timing checks over an elementary `(k, ε)` regime,
and `solution_embedding.py` evaluates Paper IV's closed-form `C⁴` packing embeddings and exact-real inverse certificates
directly without ODEs for every `k ≥ 10` and `ε ∈ (0, 1)`.

## Papers and programs

| | Paper / Program | Main results & regularity | Lean |
|---|---|---|---|
| — | *Explicit Hamiltonian ball packings: overview and reader's guide* — [overview](paper/overview/main.pdf) (4 pp) | Navigation guide to Papers I–IV, principal theorems, logical dependencies, and verification layers (no new proofs) | — |
| I | *Explicit Hamiltonian full packings of the four-ball by equal balls* — [paper](paper/p1/main.pdf), [supplement](paper/p1/supplement.pdf) | Globally `C^∞` compactly supported `H_{k, ε}` for all k ≥ 10 (Theorem A) via the linear comparison identity and Z/3-symmetric return; robustness under vector-field perturbation (Prop. B); Epoch data for k ≥ 10 (Cor. C); uniform perturbed fixed-step RK4 containment (Cor. D, `RK4Convergence.lean`) | yes |
| II | *Explicit Hamiltonian ball packings: general capacities, higher dimensions and the Siegel–Yao criterion* — [paper](paper/p2/main.pdf), [supplement](paper/p2/supplement.pdf) | Globally `C^∞` explicit Hamiltonian for all admissible data: in ℝ⁴ every packing with Σcᵢ² < C², 3cᵢ < C (including Biran's full-packing theorem for k ≥ 9 equal balls without J-holomorphic curves or Seiberg–Witten theory); in ℝ²ⁿ, n ≥ 3, every packing allowed by the volume and two-ball inequalities. Uniform terminating algorithm with finite polynomial-cutoff output | yes |
| III | *Elementary packings of the four-ball and their limits* — [paper](paper/p3/main.pdf) | Toric and window constructions: n(n+1) balls in B(n+½); density ≥ 1 − 1/√k for every k; ten balls at density 360/361. Density obstructions for lattice and balanced-profile classes at non-square k, and a sharp eight-column bound for k = 10 | no |
| IV | *Closed-form symplectic packings of the four-ball by equal balls* — [paper](paper/p4/main.pdf) | Directly evaluable ODE-free `C⁴` symplectic packing maps `f₀, …, f_{k−1}` on `B⁰(r₊)` (`r₊ > 1`), exact-real non-membership `Preimage` certificates (§§2–7), universal validity of `(H0)–(H15)` for all k ≥ 10, ε ∈ (0, 1), plus a radial–Alexander generator formula in terms of a normalised primitive and abstract ODE trajectory certificates (§8); a global Hamiltonian lift remains unfinished | abstract ODE lemmas; not a formalisation of the maps |
| | [`program/`](program/README.md) — `solution_epoch.py` | Fast PyTorch Hamiltonian generator in Epoch's fixed-step `float64` RK4 interface built from Paper III's elementary constructions: k = 10 down to ε = 0.005, squares to ε ≈ 0.002, every k ≤ 10⁵ above an explicit `eps_min(k)`. Passes documented sampled RK4 containment tests (`≤ 0.13 s/call`); global regularity differs from the smooth Hamiltonian required by the published problem (exterior branch cuts away from trajectories; piecewise `C²` window seam for k = 10) | no |
| | [`program/`](program/README.md) — `solution_embedding.py` ([`embedding_src/`](program/embedding_src/)) | Closed-form `C⁴` symplectic embeddings `Embed(i, X)` and cancellation-free left inverses `Preimage(j, Y)` implementing Paper IV, §§2–7 (not an ODE Hamiltonian). Exact-real coverage: all k ≥ 10, ε ∈ (0, 1); in `float64`, conditioning grows with k and 1/ε (see [`program/README.md`](program/README.md)); checked by `check_embedding.py` and by AST-transformed 100-digit `mpmath` source execution (`check_embedding_mp.py`) | no |

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
and [`verification/RK4Convergence.lean`](verification/RK4Convergence.lean) (the theorems).
[REVIEW.md](REVIEW.md) maps them to the papers and summarises each verification layer.

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
`Classical.choice`, `Quot.sound` (verified by fresh kernel replay `scripts/check_kernel.sh`). Explicitness and
uniformity of the algorithm are audited by metaprograms (`#check_explicit`, `#check_constructive`) described in
[`verification/README.md`](verification/README.md).

## Citation and authorship

Cite with [`CITATION.cff`](CITATION.cff). The manuscripts, mathematical proofs, Lean 4 formalisation, and accompanying
programs of this release were generated by AI models, including GPT-6.1 Sol (OpenAI), Claude Opus 5.5 (Anthropic),
Gemini 4 Carbon (Google), and other models. Liang Song chose the problem, designed and directed the research
environment, organised cross-model review, and takes sole responsibility for the release.

Trustworthiness rests on explicit verification layers: the main theorems of Papers I–II (including the finite-output
algorithm and perturbed fixed-step RK4 target containment) are checked in Lean 4 against an independent specification
importing only Mathlib, using only the three standard axioms and re-verified from scratch by fresh kernel replay;
Papers III–IV give human-readable proofs supported by multi-model cross-review and numerical checks; and program outputs
serve only as numerical corroboration (with unfinished experimental work isolated in
[`experiments/hamiltonian_lift/`](experiments/hamiltonian_lift/README.md)).

Licensed under [Apache-2.0](LICENSE). The vendored library in `vendor/` keeps its own notices
([NOTICE](NOTICE), [vendor/NOTICE](vendor/NOTICE)).
