import Mathlib

/-!
# The problem

Mathlib-only definitions of everything the statements in `verification/Statement.lean`,
`Computability.lean` and `EpochComputability.lean` refer to. Nothing in this file depends on
the construction.

**Phase space.** `ℝ^{2n}` is `E n = EuclideanSpace ℝ (Fin (2 * n))` with coordinates
`y = (q₁, …, qₙ, p₁, …, pₙ)`: index `j < n` is `q_{j+1}`, index `n + j` is `p_{j+1}`
(`qIdx`, `pIdx`). Under `z_j = q_j + i p_j` this is `ℂⁿ` with its Euclidean norm, so the
capacity of `z` is `π |z|² = π ‖y‖²`. For `n = 2` the coordinates are `(q₁, q₂, p₁, p₂)`, the
convention of the four-dimensional construction (`SymplecticPacking.E4`).

**Symplectic form and Hamiltonian vector field.** `ω₀ = Σ_j dq_j ∧ dp_j`, and the
Hamiltonian vector field of a time-dependent `H` is defined by `ι_{X_H} ω₀ = dH`, i.e.
`q̇_j = ∂H/∂p_j`, `ṗ_j = -∂H/∂q_j`.

**Balls.** The closed ball of capacity `c` centred at `s` is `{y | π ‖y - s‖² ≤ c}` (Euclidean
radius `√(c/π)`); the target is the open ball `{y | π ‖y‖² < C}`.
-/

noncomputable section

namespace SymplecticPacking.Problem

open Metric Set
open scoped ContDiff

/-- Phase space `ℝ^{2n}`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- Index of the coordinate `q_{j+1}`. -/
def qIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨j, by omega⟩

/-- Index of the coordinate `p_{j+1}`. -/
def pIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨n + j, by omega⟩

/-- The standard symplectic form `ω₀ = Σ_j dq_j ∧ dp_j`. -/
def omega0 {n : ℕ} (x y : E n) : ℝ :=
  ∑ j : Fin n, (x (qIdx j) * y (pIdx j) - x (pIdx j) * y (qIdx j))

/-- Partial derivative `∂f/∂y_i`. -/
def partialDeriv {n : ℕ} (f : E n → ℝ) (i : Fin (2 * n)) (y : E n) : ℝ :=
  fderiv ℝ f y (EuclideanSpace.single i 1)

/-- Hamiltonian vector field of a time-dependent `H`, convention `ι_{X_H} ω₀ = dH`:
`q̇_j = ∂H/∂p_j`, `ṗ_j = -∂H/∂q_j`. -/
def hamVF {n : ℕ} (H : ℝ → E n → ℝ) (t : ℝ) (y : E n) : E n :=
  WithLp.toLp 2 fun i : Fin (2 * n) =>
    if h : (i : ℕ) < n then partialDeriv (H t) ⟨i + n, by omega⟩ y
    else -partialDeriv (H t) ⟨i - n, by have := i.isLt; omega⟩ y

/-- The closed ball of capacity `c` centred at `s`: `{y | π ‖y - s‖² ≤ c}`. -/
def capBall {n : ℕ} (s : E n) (c : ℝ) : Set (E n) := {y | Real.pi * ‖y - s‖ ^ 2 ≤ c}

/-- The open ball of capacity `c` centred at `s`: `{y | π ‖y - s‖² < c}`. -/
def capBallOpen {n : ℕ} (s : E n) (c : ℝ) : Set (E n) := {y | Real.pi * ‖y - s‖ ^ 2 < c}

/-- **Admissible input** `(n, k, C, c)`: `n ≥ 2`, `k ≥ 1`, positive capacities, the volume
inequality `Σ c_i^n < C^n`, and
* for `n = 2`: `3 c_i < C` for every `i`;
* for `n ≥ 3`: `c_i + c_j < C` for all `i ≠ j` (Gromov's two-ball inequality). -/
structure Admissible (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Prop where
  two_le : 2 ≤ n
  one_le : 1 ≤ k
  C_pos : 0 < C
  c_pos : ∀ i, 0 < c i
  volume : ∑ i, c i ^ n < C ^ n
  dim_two : n = 2 → ∀ i, 3 * c i < C
  pair : 3 ≤ n → ∀ i j, i ≠ j → c i + c j < C

/-- The closed source balls `s_i + B(c_i)` are pairwise disjoint. -/
def BallsDisjoint (n k : ℕ) (c : Fin k → ℝ) (s : Fin k → E n) : Prop :=
  ∀ i j, i ≠ j → Disjoint (capBall (s i) (c i)) (capBall (s j) (c j))

/-- **Packing specification** for `H : ℝ × ℝ^{2n} → ℝ`: `H` is jointly `C^∞`, compactly
supported in space uniformly in time; from every point of every closed source ball
`B_i = s_i + B(c_i)` a global integral curve of `X_H` exists, and *every* integral curve on
`[0,1]` starting in `B_i` ends in the open target ball `{π |y|² < C}`. (So the statement is
neither vacuous nor dependent on a choice of solution.) -/
structure PackingSpec (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (H : ℝ → E n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)
  compactSupport : ∃ K : Set (E n), IsCompact K ∧ ∀ t, ∀ y ∉ K, H t y = 0
  exists_curve : ∀ i, ∀ x ∈ capBall (s i) (c i),
    ∃ γ : ℝ → E n, γ 0 = x ∧ IsIntegralCurve γ (hamVF H)
  maps_into : ∀ i, ∀ x ∈ capBall (s i) (c i),
    ∀ γ : ℝ → E n, γ 0 = x → IsIntegralCurveOn γ (hamVF H) (Icc 0 1) →
      γ 1 ∈ capBallOpen 0 C

/-! ### The Epoch AI problem (`n = 2`, equal unit balls) -/

/-- Centre of the `i`-th unit ball (0-based `i`): `(3i, 0, 0, 0)`, i.e. Epoch's
`(3i-3, 0, 0, 0)` with 1-based `i`. -/
def epochCenter (i : ℕ) : E 2 := EuclideanSpace.single 0 (3 * (i : ℝ))

/-- **Epoch specification** for `(k, ε)` with radius `R`: `H` is a smooth function of
`(t, y) ∈ ℝ × ℝ⁴`, compactly supported in `y` uniformly in `t`; every closed unit ball `B_i`
is carried by the time-`1` flow into the closed ball `B(R)` centred at the origin, with
`k / R⁴ > 1 - ε`. -/
structure EpochSpecR (k : ℕ) (ε R : ℝ) (H : ℝ → E 2 → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E 2 => H p.1 p.2)
  compactSupport : ∃ K : Set (E 2), IsCompact K ∧ ∀ t, ∀ y ∉ K, H t y = 0
  radius_pos : 0 < R
  density : 1 - ε < (k : ℝ) / R ^ 4
  exists_curve : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1,
    ∃ γ : ℝ → E 2, γ 0 = x ∧ IsIntegralCurve γ (hamVF H)
  maps_into : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1,
    ∀ γ : ℝ → E 2, γ 0 = x → IsIntegralCurveOn γ (hamVF H) (Icc 0 1) →
      γ 1 ∈ closedBall (0 : E 2) R

/-- The Epoch specification with the radius existentially quantified. -/
def EpochSpec (k : ℕ) (ε : ℝ) (H : ℝ → E 2 → ℝ) : Prop := ∃ R, EpochSpecR k ε R H

end SymplecticPacking.Problem
