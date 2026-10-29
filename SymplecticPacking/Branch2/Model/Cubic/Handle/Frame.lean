import SymplecticPacking.Handle.Frame
import SymplecticPacking.Branch2.Model.Cubic.Handle.Twist

/-!
# The first Moser path in the `𝒜⁺`-frame

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (notation and standing facts): `OmegaT_frameA`, the transfer of the first Moser
path to the `𝒜⁺`-frame chart `chartA` of `Handle/Frame.lean`: over the band `𝒜⁺`,
`chartA^* Ω_t = ω_V + κ_t ν + dp ∧ (a_𝒜 + t ∂_p α₁)` with `a_𝒜 = −3λ_C`, i.e. the angular form
`a_loc = −3η_H` of the `Zunit` frame becomes `a_𝒜` (`Bundle.angularForm_frameA`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus frameA ZnzSet lambdaCu lambdaCv etaHu etaHv Zunit pp)
open SymplecticPacking.Bundle.Cubic (kappaT kappa1 alpha1 OmegaT OmegaT_split)
open SymplecticPacking.Qhat (omega2)
open scoped ContDiff Real

attribute [local irreducible] frameA Zunit lambdaCu lambdaCv etaHu etaHv Bundle.sigmaC

/-! ### The frame function -/

/-! ### The charts -/

/-! ### Algebra of split forms under the rotation -/

/-! ### Transfer of `Ω_t` to the `𝒜⁺`-frame -/

/-- **`Ω_t` in the `𝒜⁺`-frame** (eq:fer-Omega0-local with `a_𝒜`): over the band,
`chartA^* Ω_t = ω_V + κ_t ν + dp ∧ (−3λ_C + t ∂_p α₁)`. -/
theorem OmegaT_frameA (P : Branch2.VCubic) (t : ℝ) {X : E4} (hX : X ∈ bandE) :
    pull2 chartA (OmegaT P t) X = splitForm (2 * π * X 0) (2 * π * X 1)
      (-3 * lambdaCu (X 2) (X 3) + t * pp (alpha1 P).cu (X 2) (X 3) (pE X))
      (-3 * lambdaCv (X 2) (X 3) + t * pp (alpha1 P).cv (X 2) (X 3) (pE X))
      (kappaT P t (X 2) (X 3) (pE X)) := by
  have h0 := band_Znz hX
  have hF1 := norm_frameA_of hX
  obtain ⟨hAu, hAv⟩ := Bundle.angularForm_frameA h0
  simp only at hAu hAv
  rw [deriv_frameA_u h0] at hAu
  rw [deriv_frameA_v h0] at hAv
  obtain ⟨F, hF⟩ : ∃ F, F = frameA (X 2) (X 3) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = fderiv ℝ FΦ (X 2, X 3) := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m, m = (D (1, 0) / F).im := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m, m = (D (0, 1) / F).im := ⟨_, rfl⟩
  have hFΦ : FΦ (X 2, X 3) = F := hF.symm
  rw [← hF] at hF1 hAu hAv
  rw [← hDdef] at hAu hAv
  rw [← hm1] at hAu
  rw [← hm2] at hAv
  have hD : ∀ a b : ℝ, D (a, b) = F * (Complex.I * ((a * m1 + b * m2 : ℝ) : ℂ)) := by
    intro a b
    have hr := fderiv_FΦ_rot h0 (a, b)
    rw [← hDdef, hFΦ] at hr
    have him : (D (a, b) / F).im = a * m1 + b * m2 := by
      rw [clm_pair_C, add_div, mul_div_assoc, mul_div_assoc, Complex.add_im, Complex.im_ofReal_mul,
        Complex.im_ofReal_mul, hm1, hm2]
    rw [hr, him]
  ext v w
  rw [Forms.pull2_apply, fderiv_chartA_apply hX, fderiv_chartA_apply hX, OmegaT_split]
  simp only [dc_apply, chartA_apply2, chartA_apply3, pE_chartA hX]
  rw [← hDdef, ← hF]
  have e1 : ∀ Y : E4, F * wL Y + wL X * D (Y 2, Y 3) =
      F * (wL Y + Complex.I * ((Y 2 * m1 + Y 3 * m2 : ℝ) : ℂ) * wL X) := by
    intro Y; rw [hD]; ring
  have hx0 : chartA X 0 = (F * wL X).re := by simp [chartA, hF]
  have hx1 : chartA X 1 = (F * wL X).im := by simp [chartA, hF]
  rw [hx0, hx1, e1, e1, splitForm_rot hF1, splitForm_twist]
  conv_rhs => rw [← mk_wL v, ← mk_wL w]
  rw [wL_re, wL_im]
  have c1 : -3 * etaHu (X 2) (X 3) + t * pp (alpha1 P).cu (X 2) (X 3) (pE X) + m1 / (2 * π) =
      -3 * lambdaCu (X 2) (X 3) + t * pp (alpha1 P).cu (X 2) (X 3) (pE X) := by
    rw [hAu]; ring
  have c2 : -3 * etaHv (X 2) (X 3) + t * pp (alpha1 P).cv (X 2) (X 3) (pE X) + m2 / (2 * π) =
      -3 * lambdaCv (X 2) (X 3) + t * pp (alpha1 P).cv (X 2) (X 3) (pE X) := by
    rw [hAv]; ring
  rw [c1, c2]

end SymplecticPacking.Handle.Cubic
