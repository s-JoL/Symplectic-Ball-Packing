import SymplecticPacking.General.Ham.Basic

/-!
# Hypotheses on a common isotopy (dimension `2n`, per-ball radii)

Dimension `2n`, a radius quadruple `r₁ᵢ < r₂ᵢ < r₃ᵢ < ρᵢ` per ball, arbitrary start centres
`sᵢ`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Problem
open scoped ContDiff

/-- Hypotheses on a common isotopy `F i t`:
* jointly smooth in `(t, u)` on `ℝ × B(ρᵢ)`;
* symplectic in `u` for every `t`;
* injective on `B̄(r₃ᵢ)`, with pairwise disjoint images of the `B̄(r₃ᵢ)` for every `t`;
* constant in `t` for `t ≤ 0` and for `t ≥ 1`;
* starting at the translations `u ↦ sᵢ + u`;
* uniformly bounded images. -/
structure CommonIsotopy {n k : ℕ} (F : Fin k → ℝ → E n → E n) (s : Fin k → E n)
    (r1 r2 r3 ρ : Fin k → ℝ) : Prop where
  radii : ∀ i, 0 < r1 i ∧ r1 i < r2 i ∧ r2 i < r3 i ∧ r3 i < ρ i
  smooth : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × E n => F i p.1 p.2) (univ ×ˢ ball 0 (ρ i))
  sympl : ∀ i t, ∀ u ∈ ball (0 : E n) (ρ i), IsSymplecticLinear (fderiv ℝ (F i t) u)
  inj : ∀ i t, InjOn (F i t) (closedBall 0 (r3 i))
  disj : ∀ i j t, i ≠ j →
    Disjoint (F i t '' closedBall 0 (r3 i)) (F j t '' closedBall 0 (r3 j))
  const_left : ∀ i t, t ≤ 0 → F i t = F i 0
  const_right : ∀ i t, 1 ≤ t → F i t = F i 1
  start : ∀ i u, F i 0 u = s i + u
  bounded : ∃ S, ∀ i t, ∀ u ∈ closedBall (0 : E n) (r3 i), ‖F i t u‖ ≤ S

end SymplecticPacking.General.Ham
