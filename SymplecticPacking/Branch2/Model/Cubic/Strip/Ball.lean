import SymplecticPacking.Strip.Ball
import SymplecticPacking.Branch2.Model.Cubic.Base

/-!
# The enlarged capacities and the ball estimate

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Strip.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:str-balls` (paper `def:str-enlarged`, `lem:str-ball`): the enlarged capacities
`ρ < ρ̄ < ρ̂ < a` and the ball estimate: a point of the ball of capacity `ρ̄` (or `ρ̂`) at fibre
level `p` is sent by the strip map to an `x` smaller than the layer width `h_i(p)`.
(`ρ̄_i = (ρ_i + a_i)/2` is `CubicData.rhoBar i`, `def:str-enlarged`.)
-/

noncomputable section

namespace SymplecticPacking.Strip.Cubic

open scoped Real

variable (P : Branch2.VCubic)

/-! The strip parameters of ball `i` are `ρ̄_i = P.rhoBar i`, `δ_i = P.deltaStrip i`,
`ρ̂_i = P.rhoHat i` (`CubicData`); their order is `VCubic.rho_lt_rhoBar`,
`VCubic.rhoBar_lt_rhoHat`, `VCubic.rhoHat_lt_a`. -/

theorem rhoBar_eq (i : ℕ) : P.rhoBar i = P.a i - P.deltaStrip i := by
  unfold Branch2.CubicData.deltaStrip; ring

theorem rhoHat_eq (i : ℕ) : P.rhoHat i = P.a i - 3 / 4 * P.deltaStrip i := by
  unfold Branch2.CubicData.rhoHat Branch2.CubicData.deltaStrip; ring

/-- **`lem:str-ball` (12)** for ball `i`. Let `w = π|z_b|²`, `p = π|z_f|²` and `x` the first
component of `Ψ_strip(z_b)` (with `δ = δ_i`). If `w + p ≤ ρ̄_i`, then
`x < w + δ/2 ≤ a_i - p - δ/2 < h_i(p)`; if `w + p < ρ̂_i`, then `x < a_i - p - δ/4 < h_i(p)`;
in both cases `p < a_i < h`. -/
theorem x_lt_hi {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ P.k) (zb zf : ℂ) :
    (π * ‖zb‖ ^ 2 + π * ‖zf‖ ^ 2 ≤ P.rhoBar i →
      (psiStrip (P.deltaStrip i) zb).re < π * ‖zb‖ ^ 2 + P.deltaStrip i / 2 ∧
      π * ‖zb‖ ^ 2 + P.deltaStrip i / 2 ≤ P.a i - π * ‖zf‖ ^ 2 - P.deltaStrip i / 2 ∧
      P.a i - π * ‖zf‖ ^ 2 - P.deltaStrip i / 2 < P.hi i (π * ‖zf‖ ^ 2) ∧
      π * ‖zf‖ ^ 2 < P.a i ∧ P.a i < P.h) ∧
    (π * ‖zb‖ ^ 2 + π * ‖zf‖ ^ 2 < P.rhoHat i →
      (psiStrip (P.deltaStrip i) zb).re < P.a i - π * ‖zf‖ ^ 2 - P.deltaStrip i / 4 ∧
      P.a i - π * ‖zf‖ ^ 2 - P.deltaStrip i / 4 < P.hi i (π * ‖zf‖ ^ 2) ∧
      π * ‖zf‖ ^ 2 < P.a i ∧ P.a i < P.h) := by
  set δ := P.deltaStrip i
  set w := π * ‖zb‖ ^ 2
  set p := π * ‖zf‖ ^ 2
  have hδ : 0 < δ := P.deltaStrip_pos h1 hk
  have hx := psiStrip_x_lt hδ zb
  have hw : 0 ≤ w := by positivity
  have hhi : P.a i - p < P.hi i p := lt_of_le_of_lt (le_max_left _ _) (P.hi_gt_pos_part i p)
  have hbar := rhoBar_eq P i
  have hhat := rhoHat_eq P i
  have hah := P.a_lt_h h1 hk
  constructor
  · intro h
    refine ⟨hx, by linarith, by linarith, by linarith, hah⟩
  · intro h
    refine ⟨by linarith, by linarith, by linarith, hah⟩

end SymplecticPacking.Strip.Cubic
