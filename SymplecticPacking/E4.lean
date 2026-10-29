import Mathlib
import SymplecticPacking.Params

/-!
# The four-dimensional phase space

Phase space `ℝ⁴ = E4` with coordinates `(q₁, q₂, p₁, p₂)`, its standard symplectic form, and the
flat step and box cutoff of `sec:pre-flat` and `sec:cpl-box`. For `n = 2` these agree with the
definitions of `verification/Problem.lean` (`Branch2/Bridge.lean`).
-/

noncomputable section

namespace SymplecticPacking

/-- Phase space `ℝ⁴` with coordinates `(q₁, q₂, p₁, p₂)` (indices `0,1,2,3`). -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The standard symplectic form `ω₀ = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`. -/
def omega0 (x y : E4) : ℝ := x 0 * y 2 - x 2 * y 0 + x 1 * y 3 - x 3 * y 1

/-- A linear map `A : ℝ⁴ → ℝ⁴` is symplectic if `ω₀(Ax, Ay) = ω₀(x, y)`. -/
def IsSymplecticLinear (A : E4 →L[ℝ] E4) : Prop := ∀ x y, omega0 (A x) (A y) = omega0 x y

/-! ### Flat step and box cutoff -/

/-- The flat step `S` of `sec:pre-flat` is Mathlib's `Real.smoothTransition`. -/
abbrev flatStep : ℝ → ℝ := Real.smoothTransition

/-- One-coordinate box cutoff of `sec:cpl-box`: `1` for `|y| ≤ B/2`, `0` for `|y| ≥ 3B/4`. -/
def boxCutoff1 (B y : ℝ) : ℝ :=
  1 - flatStep ((y ^ 2 - (B / 2) ^ 2) / ((3 * B / 4) ^ 2 - (B / 2) ^ 2))

namespace Params
variable (P : Params)
/-- `R₀ = ρ^{-1/2}`. -/
def R0 : ℝ := P.rho ^ (-(1 / 2 : ℝ))

end Params

end SymplecticPacking
