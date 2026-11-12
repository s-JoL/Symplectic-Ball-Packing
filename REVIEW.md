# Reviewer guide

## The claim to assess first

The central object is a **specified smooth, compactly supported Hamiltonian**, not an existence
assertion. In ℝ⁴, for each k ≥ 10 and 0 < ε < 1, its time-one flow moves the k closed unit balls
at `(3i,0,0,0)`, `0 ≤ i < k`, into the open ball of radius `(k/(1−ε/4))^(1/4)`; the occupied
volume fraction is exactly `1−ε/4`.

Read the abstract and Theorem A of [Paper I](paper/p1/main.pdf), then compare
[`four_dim_theorem`](verification/Statement.lean) with the definitions in
[`Problem.lean`](verification/Problem.lean).

## The three papers and the programs

| Part | Claims | How checked |
|---|---|---|
| I, equal balls in the four-ball ([pdf](paper/p1/main.pdf), [supplement](paper/p1/supplement.pdf)) | Theorem A; Proposition B (robustness); Corollary C (Epoch data, k ≥ 10, ε < 7/8) | Lean, plus the paper |
| II, general capacities and higher dimensions ([pdf](paper/p2/main.pdf), [supplement](paper/p2/supplement.pdf)) | Theorem 1 for all n ≥ 2 (n = 2: Σcᵢ² < C², 3cᵢ < C; n ≥ 3: Σcᵢⁿ < Cⁿ, cᵢ + cⱼ < C); Corollary 2 (Siegel–Yao criterion by explicit flows); Corollary 3 (equal balls: Biran's k ≥ 9 in ℝ⁴, k ≥ 2ⁿ for n ≥ 3); Corollary 4 (a cone of unequal balls in ℝ⁴); Corollary 5 (full Epoch data); the finite-output algorithm | Lean, plus the paper |
| III, elementary packings ([pdf](paper/p3/main.pdf)) | Explicit toric/window packings and obstructions for those classes | The paper only; not formalised |
| [`program/`](program/README.md) `solution_epoch.py` | A Hamiltonian in Epoch's interface for a range of (k, ε) | Numerical integration only (RK4 at N and 2N); the returned Hamiltonian is smooth near the trajectories, not globally |
| [`program/`](program/README.md) `solution_embedding.py` | Explicit C⁴ packing embeddings for every k ≥ 10 and ε | Sampling checks in float64 (containment, disjointness, volume, round trip, continuity); proof document in preparation, not part of this release |

All general statements assume k ≥ 1, C > 0, every cᵢ > 0, and pairwise disjoint closed source balls.
The four-dimensional general theorem is not a classification of all unequal packings. The algorithm
theorem gives termination and correctness, no practical runtime bound. Sufficiency of the Siegel–Yao
criterion in dimension ≥ 6 was first proved in the OpenAI preprint (2026); Paper II gives an explicit
motion. Construction and sufficiency avoid J-holomorphic curves; the necessity direction of Corollary 2
uses the classical obstructions, and the dependency audit detects this.

## Lean names and the papers

The docstrings in `verification/Statement.lean` use the lettering of version 1.0.1, when the work was
one paper. The Lean development is unchanged since then. The Lean theorems are stated for the general
Hamiltonian of Paper II; Paper I's Hamiltonian H_{k,ε} is the same term on the equal-ball data of Theorem A.

| Lean theorem | 1.0.1 label | Version 1.1 |
|---|---|---|
| `four_dim_theorem`, `four_dim_data` | Theorem A | Paper I, Theorem A |
| `four_dim_stability` | Proposition B | Paper I, Proposition B |
| `main_theorem`, `main_time_support`, `main_support_radius` | Theorem C | Paper II, Theorem 1(i), all n ≥ 2 (used by Paper I's Theorem A through `four_dim_data`) |
| `flow_is_integral_curve`, `flow_symplectic_diffeomorphism`, `flow_images_disjoint` | — | Paper II, Theorem 1(i); `flow_images_disjoint` also Paper I, Theorem A |
| `neighbourhood_criterion`, `flow_neighbourhood_embedding` | Corollary D | Paper II, Corollary 2 |
| `equal_balls` | Corollary E | Paper II, Corollary 3 |
| `unequal_cone` | Corollary G | Paper II, Corollary 4 |
| `epoch_packing`, `epoch_theorem` | Corollary F | Paper II, Corollary 5 (contains Paper I, Corollary C) |
| `epoch_theorem_ten` | Corollary F | Epoch's own statement (k ≥ 10, closed ball B(R)); contains Paper I, Corollary C |
| `General.Compile.main_finite` | — | Paper II, finite form (Theorem 5.2) |
| `original_name_algorithm`, `epoch_name_algorithm`, `epoch_name_algorithm_packing` | algorithm theorem | Paper II, Theorem 1(iii) and the algorithm theorem (Theorem 5.3) |
| `#check_explicit General.packingHamiltonian` (metaprogram) | Theorem C(ii) | Paper II, Theorem 1(ii); Paper I's explicitness claim for H_{k,ε} |

## A short formal review

1. [`verification/Problem.lean`](verification/Problem.lean): phase space, symplectic form, balls,
   admissibility and the packing specification, from Mathlib alone. Check the hypotheses and the
   quantifier over **every** integral curve.
2. [`verification/Algorithm.lean`](verification/Algorithm.lean): the named Hamiltonian, by definitional
   equalities.
3. [`verification/Statement.lean`](verification/Statement.lean): the theorems, for those exact terms.
4. [`verification/Computability.lean`](verification/Computability.lean) and
   [`verification/EpochComputability.lean`](verification/EpochComputability.lean): one uniform machine,
   finite output, halting, certified packing.

To locate a particular step, [`PAPER-INDEX.md`](verification/PAPER-INDEX.md) lists the Lean
declarations tagged in each statement of Papers I and II. A tag marked **needed consequence verified**
covers only the version the construction uses.

## What the checks establish

| Check | Establishes |
|---|---|
| Lean build and axiom gates | Accepted proofs of the stated theorems, using only the three standard axioms |
| Explicitness and uniformity audits | The definitions meet the stated syntactic criteria; the machines do not branch classically (metaprograms, not verified) |
| Independence audit | The construction side does not depend on packing existence theorems or curve analysis |
| Fresh kernel replay (`scripts/check_kernel.sh`) | Stored proof terms re-checked in a new kernel environment |
| Paper build | The three papers compile with no undefined references |
| `program/check_epoch.py` | The Hamiltonian's flow packs the sampled sphere points at N and 2N RK4 steps (evidence, not proof) |
| `program/check_embedding.py` | The embeddings pass sampled containment, disjointness, volume, round-trip and continuity checks (evidence, not proof) |

None of these certifies novelty, exposition, the correspondence between prose and formal statements,
or a runtime bound. Commands and the trusted base are in [`verification/README.md`](verification/README.md).
