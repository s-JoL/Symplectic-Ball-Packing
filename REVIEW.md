# Reviewer guide

## The claim to assess first

The central object is a **specified smooth (`C^∞`), compactly supported Hamiltonian**, uniform for **every integer
k ≥ 10—including non-square values such as k = 10, 11, 12, …—and every arbitrarily small positive volume deficit
0 < ε < 1**, not an existence assertion. In ℝ⁴, its time-one flow moves the k closed unit balls at `(3i,0,0,0)`,
`0 ≤ i < k`, into the open ball of radius `(k/(1−ε/4))^(1/4)`; the occupied volume fraction is exactly `1−ε/4`.
(The Lean files index the same k centres 0-based as `epochCenter i = (3i,0,0,0)` for `0 ≤ i < k`, written 1-based as
`(3i−3,0,0,0)` for `1 ≤ i ≤ k` in the papers; Theorem A packs at density `1 − ε/4`, while the Epoch stability,
finite-output algorithm, and perturbed fixed-step RK4 containment theorems pack at `1 − ε/2`, strictly above Epoch's
threshold `1 − ε`.)

Lean 4 checks the named Hamiltonian against an independently stated specification (`verification/Problem.lean`, written
from Mathlib alone): global `C^∞` smoothness, uniform compact spatial support, existence of trajectories, and target
containment for **every** integral curve starting from **every** point of **every** source ball. Separate theorems establish
symplecticity and pairwise disjointness of the time-one ball images, termination and certified output of the uniform
rational polynomial-cutoff algorithm, quantitative Picard–Lindelöf trajectory certificates (`δ e^L`), and uniform
eventual target containment for perturbed fixed-step RK4 (`δ₀ = g/(4e^K)`, `N₀ = ⌈4Me^K/g⌉ + 1`). Everything rests on
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and is re-verified from scratch by fresh
kernel replay (`scripts/check_kernel.sh`).

Read the 4-page [Series Overview](paper/overview/main.pdf), then the abstract, Theorem A, and Corollary D of
[Paper I](paper/p1/main.pdf), and compare [`four_dim_theorem`](verification/Statement.lean) and
[`epoch_rk4_convergence`](verification/RK4Convergence.lean) with the definitions in
[`Problem.lean`](verification/Problem.lean). For a direct item-by-item mapping to Epoch AI's problem and interface, see
[EPOCH.md](EPOCH.md).

## The four papers and the programs

| Part | Claims & regularity | How checked |
|---|---|---|
| I, equal balls in the four-ball ([pdf](paper/p1/main.pdf), [supplement](paper/p1/supplement.pdf)) | Globally `C^∞` Theorem A; Proposition B (robustness); Corollary C (Epoch data, k ≥ 10); Corollary D (uniform perturbed fixed-step RK4 containment) | Lean 4, plus the paper |
| II, general capacities and higher dimensions ([pdf](paper/p2/main.pdf), [supplement](paper/p2/supplement.pdf)) | Globally `C^∞` Theorem 1 for all n ≥ 2 (n = 2: Σcᵢ² < C², 3cᵢ < C; n ≥ 3: Σcᵢⁿ < Cⁿ, cᵢ + cⱼ < C); Corollary 2 (Siegel–Yao criterion by explicit flows); Corollary 3 (equal balls: Biran's k ≥ 9 in ℝ⁴, k ≥ 2ⁿ for n ≥ 3); Corollary 4 (cone of unequal balls in ℝ⁴); Corollary 5 (full Epoch data); the terminating finite-output algorithm | Lean 4, plus the paper |
| III, elementary packings ([pdf](paper/p3/main.pdf)) | Explicit toric/window packings and rigorous obstructions for lattice, balanced-profile and 8-column configurations | The paper (not formalised in Lean); finite identities checked in exact rational arithmetic |
| IV, closed-form equal-ball embeddings ([pdf](paper/p4/main.pdf)) | Directly evaluable ODE-free `C⁴` symplectic embeddings `B⁰(r₊) → B⁰(R)` (`r₊ > 1`), exact-real non-membership left inverses `Preimage` (§§2–7), and a radial-collar generator formula in terms of a normalised primitive with abstract ODE trajectory certificates (§8), for all k ≥ 10, ε ∈ (0, 1) | Human proof of the maps. Lean proves abstract ODE lemmas, without certifying a global lift of these maps (`picard_lindelof_epoch_certificate` assumes `C^∞`) |
| [`program/`](program/README.md) `solution_epoch.py` | PyTorch Hamiltonian generator in Epoch's fixed-step `float64` RK4 interface over an elementary `(k, ε)` range | Passes documented sampled RK4 containment tests at N and 2N steps; global regularity differs from the smooth Hamiltonian required by the published problem (exterior branch cuts away from trajectories; piecewise `C²` across one window seam for k = 10) |
| [`program/`](program/README.md) `solution_embedding.py` ([`embedding_src/`](program/embedding_src/)) | Modular & bundled implementation of Paper IV, §§2–7 `C⁴` embeddings and cancellation-free left inverses | Paper IV for exact reals; numerical checks in `float64` (`check_embedding.py`) and AST-transformed 100-digit `mpmath` source execution (`check_embedding_mp.py`, scoping representative balls for `k > 25` unless `--full-balls` is passed) |

All general statements assume k ≥ 1, C > 0, every cᵢ > 0, and pairwise disjoint closed source balls.
In dimension four the general theorem covers the sufficient regime `Σcᵢ² < C²`, `3cᵢ < C`. Sufficiency
of the Siegel–Yao criterion in dimension ≥ 6 was first proved in the OpenAI preprint (2026); Paper II
realises every admissible packing by an explicit Hamiltonian motion. Construction and sufficiency avoid
J-holomorphic curves; the necessity direction of Corollary 2 uses the classical obstructions, and the
dependency audit verifies this separation.

## Lean names and the papers

The docstrings in `verification/Statement.lean` use the lettering of version 1.0.1, when the work was
one paper. The pre-existing construction and main statements in `SymplecticPacking/` and `Statement.lean` are unchanged
from version 1.0.1; version 1.2.0 (continuing 1.1.0) adds the RK4 and trajectory-certificate theorems in
`verification/RK4Convergence.lean` and extends the audit entry points (`Kernel.lean`, `Audit/Independence.lean`).
The Lean theorems are stated for the general Hamiltonian of Paper II; Paper I's Hamiltonian H_{k,ε} is the same term on
the equal-ball data of Theorem A.

| Lean theorem | 1.0.1 label | Version 1.2.0 |
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
| `epoch_rk4_convergence`, `epoch_exact_rk4_convergence` | — | Paper I, Corollary D: perturbed & exact fixed-step RK4 containment on `epochHamiltonianQ` (`verification/RK4Convergence.lean`) |
| `picard_lindelof_curve_unique`, `picard_lindelof_epoch_certificate` | — | Abstract Lipschitz trajectory uniqueness & `C^∞` quantitative trajectory certificate (Paper IV, Prop. 8.1(ii); `verification/RK4Convergence.lean`) |
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
5. [`verification/RK4Convergence.lean`](verification/RK4Convergence.lean): perturbed fixed-step RK4
   containment (`epoch_rk4_convergence`) and quantitative Picard–Lindelöf trajectory certificates
   (`picard_lindelof_epoch_certificate`).

To locate a particular step, [`PAPER-INDEX.md`](verification/PAPER-INDEX.md) lists the Lean
declarations tagged in each statement of Papers I and II. A tag marked **needed consequence verified**
covers only the version the construction uses.

## What the checks establish

| Check | Establishes |
|---|---|
| Lean build and axiom gates | Accepted proofs of the stated theorems of Papers I–II and `RK4Convergence.lean`, using only the three standard axioms |
| Explicitness and uniformity audits | The definitions meet the stated syntactic criteria; the machines do not branch classically (metaprograms, not verified) |
| Independence audit | The construction side (including `RK4Convergence.lean`) does not depend on packing existence theorems or curve analysis |
| Fresh kernel replay (`scripts/check_kernel.sh`) | The full imported declaration closure of `verification.Kernel`, including the main theorem and algorithm dependencies, re-checked in a fresh kernel environment |
| Paper & bundle build | All four papers compile with zero undefined references or overfull boxes; `solution_embedding.py` matches `program/embedding_src/` byte-for-byte |
| `program/check_epoch.py` | The elementary Hamiltonian's flow packs sampled sphere points at N and 2N RK4 steps across its covered `(k, ε)` table |
| `program/check_embedding.py` & `check_embedding_mp.py` | The closed-form `C⁴` embeddings pass sampled containment, disjointness, volume coverage, and AST-transformed 100-digit `mpmath` source execution |

Human review assesses the correspondence between the mathematical prose and the formal definitions in
`verification/Problem.lean`, as well as the proofs in Papers III and IV. Practical numerical evaluation
and its relationship to the Epoch interface are documented in [EPOCH.md](EPOCH.md) and
[`program/README.md`](program/README.md). Commands and the trusted base are in
[`verification/README.md`](verification/README.md).
