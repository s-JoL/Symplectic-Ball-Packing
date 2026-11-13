# Guide to Epoch AI's Symplectic Ball-Packing Problem

This note maps every mathematical, algorithmic, and engineering requirement of
[Epoch AI's symplectic ball-packing problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing)
to the theorems, Lean 4 declarations, and programs of version **1.2.0** (see also the 4-page
[Series Overview](paper/overview/main.pdf) and [Reviewer Guide](REVIEW.md)).

**Summary.** Papers I–II solve the mathematical construction and computability parts of Epoch's problem uniformly for
**every integer `k ≥ 10` (including all non-square values `k = 10, 11, 12, …`) and every `0 < ε < 1`**, and Lean 4
additionally proves uniform eventual target containment for exact and perturbed fixed-step RK4 applied to the smooth
Hamiltonian (`epoch_rk4_convergence`). Producing a single Python submission that simultaneously meets the published
`float64` interface, global smoothness requirement, and runtime limits across all `(k, ε)` remains a separate
implementation objective.

---

## 1. Item-by-item mapping to Epoch AI's requirements

| Epoch requirement | Paper theorem | Lean 4 declaration (`verification/`) | Accompanying program (`program/`) | Status |
|---|---|---|---|---|
| **1. Source balls & centres:** `k ≥ 10` disjoint closed unit balls centred at `(3i − 3, 0, 0, 0)` (`1 ≤ i ≤ k`, i.e. `(3i, 0, 0, 0)` for `0 ≤ i < k`) | Paper I, Thm A & Cor. C; Paper II, Cor. 5; Paper IV, Thm 1.1 | `epochCenter`, `four_dim_theorem`, `epoch_theorem_ten` (`Statement.lean`) | `solution_epoch.py` (restricted `(k, ε)`); `solution_embedding.py` (maps `B(1)` directly, all `(k, ε)`) | **Hamiltonian flow proved in Lean 4 (Papers I–II); Paper IV gives a human-proved direct-map variant** |
| **2. Target ball & packing density:** time-1 images pairwise disjoint inside closed ball `B(R)` about `0` with `k / R⁴ > 1 − ε` for **every** `k ≥ 10` and `0 < ε < 1` | Paper I, Thm A (`1 − ε/4`) & Cor. C (`1 − ε/2`); Paper II, Cor. 5 (`k ≥ 9`); Paper IV, Thm 1.1 (`1 − ε`, `C⁴` maps) | `four_dim_theorem`, `flow_images_disjoint`, `epoch_packing`, `epoch_theorem_ten` (`Statement.lean`) | `solution_embedding.py` (all `k ≥ 10, ε ∈ (0, 1)` over `ℝ`, ODE-free); `solution_epoch.py` (`ε ≥ eps_min(k)`) | **Hamiltonian flow proved in Lean 4 (Papers I–II); Paper IV gives a human-proved direct-map variant** |
| **3. Smooth Hamiltonian with a well-defined flow:** `H(t, Q, P)` globally smooth (`C^∞`); this project additionally proves uniform compact spatial support | Paper I, Thm A; Paper II, Thm 1(i) & Thm 5.2 (`β_B · P`) | `Problem.PackingSpec`, `main_theorem`, `main_support_radius` (`Problem.lean`, `Statement.lean`) | `solution_epoch.py` has finite regularity (`C⁷` at the keyhole origin, `C³` time junctions, exterior branch cuts, and for `k = 10` a piecewise `C²` window seam); `solution_embedding.py` is `C⁴` map-only | **Proved mathematically in Lean 4**; **not met** by `solution_epoch.py` globally |
| **4. Single uniform algorithm & natural dependence on `(k, ε)`:** one algorithm valid for arbitrarily small `ε > 0`, rather than a separate ad-hoc construction for each value | Paper I, §2.4 (level L1, linear comparison identity); Paper II, Thm 1(ii)–(iii) & Thm 5.3 (halting polynomial-cutoff machine) | `#check_explicit`, `#check_constructive`, `epoch_name_algorithm`, `epoch_name_algorithm_packing` (`EpochComputability.lean`) | `solution_embedding.py` uses one closed-form parameter tuple `PiStar(k, min(ε, 0.01))` (`Paper IV, Def. 7.1`) | **Proved (Lean 4 + metaprogram audits)** |
| **5. Python `solution(k, epsilon) -> str` returning `Hamiltonian(Q, P, t)`** | Paper II, Thm 5.3 proves finite rational polynomial-cutoff output; executable Python compilation and performance remain to be established | `epoch_name_algorithm` | `solution_epoch.py` implements exact signature for `10 ≤ k ≤ 10⁵`, `ε ≥ eps_min(k)`; `solution_embedding.py` returns `Embed`/`Preimage` instead | **Numerical corroboration** on elementary `(k, ε)`; **unmet** across all `(k, ε)` |
| **6. `torch.float64` & `torch.autograd` compatibility** (pure PyTorch, no `numpy`) | — (interface specification) | — | `solution_epoch.py` & `check_epoch.py` run in pure PyTorch `float64` (`autograd` vector field, `numpy` blocked); `solution_embedding.py` is pure PyTorch `float64` | **Numerical corroboration** (`solution_epoch.py` in covered regime) |
| **7. RK4 target containment:** the public specification names RK4; the project proves and tests fixed-step RK4 | Paper I, Cor. D: explicit `δ₀ = g/(4e^K)`, `N₀ = ⌈4Me^K/g⌉ + 1` (`g = R − R_Q`, `M = K + KC`) for exact & perturbed RK4 on `H_{k, ε}` | `rk4Step`, `rk4Iter`, `epoch_rk4_convergence`, `epoch_exact_rk4_convergence` (`RK4Convergence.lean`) | `check_epoch.py` verifies sampled RK4 at `N` and `2N` across 12 benchmark `(k, ε)` pairs for `solution_epoch.py` | **Asymptotic perturbed RK4 containment proved in Lean 4** (`K, C` uninstantiated); **numerical corroboration** in `solution_epoch.py` |
| **8. Runtime limits:** `≤ 10 min` per `solution(k, ε)` call and `≤ 10 s` per `Hamiltonian` call | Paper III proves positive density gaps for specified elementary classes; the implementation threshold `eps_min(k)` also includes its chosen layouts and numerical margins. Paper IV, Rem. 8.3 gives conditioning diagnostics | — | `solution_epoch.py` meets the published per-call limits on its covered regime (`solution ≤ 0.72 s`, single `Hamiltonian` call `≤ 0.13 s`; full `N`/`2N` RK4 checker sweeps over 3000–20000 points take `6.7–1382 s`, see [`program/README.md`](program/README.md)); not available for general `(k, ε)` | **Unmet** across arbitrary `(k, ε)` (separate implementation objective) |
| **9. Grader nearby-pair finite-difference symplecticity check** | Exact flow symplecticity proved in Paper I, Thm A & Paper II, Thm 1(i) (and for maps in Paper IV, Thm 1.1) | `flow_symplectic_diffeomorphism` (`Statement.lean`) | `check_embedding.py` / `check_embedding_mp.py` check normalised Richardson Jacobian symplecticity on `Embed`; not bounded for RK4 on `H_{k, ε}` | **Exact flow symplecticity proved in Lean 4**; grader finite-difference check **unmet** across all `(k, ε)` |

---

The finite-output theorem is a mathematical algorithm with certified halting and packing output: it supplies a
finite rational polynomial times a fixed cutoff. Its certificate search is explicit and uniform in the input.
The theorem gives no practical output-size or runtime bound; compiling and evaluating that output within Epoch’s
limits remains open. Compact support is an additional property of the construction, not a requirement added to
Epoch’s specification.

## 2. Highlights of the formal RK4 and trajectory-certificate theorems

`verification/RK4Convergence.lean` establishes two general ODE results and specialises RK4 to Paper I's smooth
Hamiltonian `H_{k, ε}` (`epochHamiltonianQ k ε`), using only `[propext, Classical.choice, Quot.sound]`:

1. **Uniform perturbed fixed-step RK4 containment (`epoch_rk4_convergence`, Paper I Corollary D):**
   Put `R_Q = (k / (1 − ε/4))^(1/4)`, `R = (k / (1 − ε/2))^(1/4)`, and `g = R − R_Q > 0`. Given any global space-time
   Lipschitz constant `K ≥ 0` and supremum bound `C ≥ 0` for `X_{H_{k, ε}}` on `[0, 1] × ℝ⁴`, set `M = K + K C` and
   ```text
   δ₀ = g / (4 exp(K)) > 0,      N₀ = ⌈4 M exp(K) / g⌉ + 1 ≥ 1.
   ```
   Then for every `N ≥ N₀`, every `1 ≤ i ≤ k`, every `x` with `|x − sᵢ| ≤ 1`, and every sequence `y₀, …, y_N ∈ ℝ⁴` with initial
   perturbation `|y₀ − x| ≤ δ₀` and per-step state-update perturbation
   `|y_{m+1} − RK4(H_{k, ε}, m/N, 1/N, y_m)| ≤ δ₀ / N`, the terminal iterate satisfies `|y_N| ≤ R` (`k / R⁴ = 1 − ε/2`).
   - *Boundary:* `K` and `C` come from compactness and smoothness and are not numerically instantiated, so this theorem
     provides no executable step-count or precision budget, and it does not cover the grader's nearby-pair numerical
     symplecticity check or a `float64` implementation.
2. **Quantitative Picard–Lindelöf trajectory certificates (`picard_lindelof_curve_unique`,
   `picard_lindelof_epoch_certificate`; Paper IV Proposition 8.1(ii)):**
   If `X_H(t, ·)` is `L`-Lipschitz on `[0, 1]` and candidate curves `γ_t^{(i)}(u)` satisfy the uniform velocity-defect
   bound `‖∂_t γ_t^{(i)}(u) − X_H(t, γ_t^{(i)}(u))‖ ≤ δ` on `[0, 1]`, Grönwall's inequality bounds the time-1 endpoint
   deviation by `δ e^L`, so a strict target margin `R − R_0 ≥ δ e^L` absorbs a rigorously bounded trajectory residual.
   (`picard_lindelof_curve_unique` requires Lipschitzness alone; `picard_lindelof_epoch_certificate` assumes `H ∈ C^∞`,
   and finite point sampling is a diagnostic rather than a global uniform input `δ`.)

---

## 3. Official deliverables vs. experimental archive in the `1.2.0` release

- **Certified formal & mathematical deliverables:** Papers I–IV + Overview (`paper/`), and the Lean 4 formalisation +
  fresh kernel replay (`SymplecticPacking/`, `verification/`).
- **Official numerical corroboration (`program/`, verified against [`program/release-check/NUMERICAL-VERIFICATION.json`](program/release-check/NUMERICAL-VERIFICATION.json)):**
  `solution_epoch.py` + `check_epoch.py`, and `solution_embedding.py` (`embedding_src/`) + `check_embedding.py` +
  `check_embedding_mp.py`.
- **Clearly labelled experimental research archive (`experiments/hamiltonian_lift/`):**
  Included in the release archive via an explicit allow-list solely for research transparency and reproducibility—**not**
  part of `program/` and **not** counted among passed deliverables. It archives an unfinished 6-stage prototype
  `solution_hamiltonian.py` attempting to lift Paper IV's `Chain3` to a global `C³` Hamiltonian, together with
  [`repro_branch_jump.py`](experiments/hamiltonian_lift/repro_branch_jump.py) and
  [`logs/current_honest_check.log`](experiments/hamiltonian_lift/logs/current_honest_check.log) documenting why straight
  radial sheet unwrapping still exhibits integer-turn branch jumps in cutoff collars near `|Z₀| → 0` (e.g. `k = 12,
  ε = 0.001`).

  Cross-review also identified an unapplied local potential-matching correction, recorded in
  [`DIAGNOSTICS.md`](experiments/hamiltonian_lift/DIAGNOSTICS.md). The preserved failure logs do not isolate every
  cause of the prototype's phase jumps.
