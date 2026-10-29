import SymplecticPacking.HighDim.Comparator.PlanarMorseInverse
import SymplecticPacking.HighDim.Comparator.PlanarDensityExtension

/-!
# Positivity and the exact flat germ of the planar density
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
include hξ hL hne hb

lemma a0_eq_inv_lin : D.a0 y = 1 / Real.sqrt (D.alphaU y / 2) := by
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  unfold a0
  rw [show 2 / D.alphaU y = (D.alphaU y / 2)⁻¹ by field_simp]
  rw [Real.sqrt_inv, one_div]

lemma a0_pos_from_pieces : 0 < D.a0 y := by
  rw [D.a0_eq_inv_lin y hξ hL hne hb]
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  positivity

/-- Common radius on which both signed Morse inverses are exactly linear. -/
def densityRadius : ℝ :=
  min (Real.sqrt (D.alphaU y / 2) * D.epsU) (D.wellV.lin * D.wellV.eps)

lemma densityRadius_pos : 0 < D.densityRadius y := by
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  have he := D.epsU_pos y hξ hL hne hb
  have hv := D.wellV_hyp y hξ hL hne hb
  exact lt_min (by positivity) (mul_pos (Branch2.Planar.Well.lin_pos hv)
    (Branch2.Planar.Well.eps_pos hv))

omit hξ hL hne hb in
lemma deriv_linear_closed {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a c : ℝ} (ha : 0 < a)
    (hlin : ∀ x, |x| ≤ a → f x = c * x) {x : ℝ} (hx : |x| ≤ a) : deriv f x = c := by
  apply Inner.deriv_eq_of_closed hf ha (fun t ht => ?_) hx
  have heq : f =ᶠ[𝓝 t] fun x => c * x := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with u hu
    exact hlin u hu.le
  rw [heq.deriv_eq]
  simpa using ((hasDerivAt_id t).const_mul c).deriv

lemma XU_deriv_flat {u : ℝ} (hu : |u| ≤ D.densityRadius y) : deriv (D.XU y) u = D.a0 y := by
  have hr := D.densityRadius_pos y hξ hL hne hb
  have hu' := hu.trans (min_le_left _ _)
  apply deriv_linear_closed (D.XU_smooth y hξ hL hne hb)
    (hr.trans_le (min_le_left _ _)) (fun x hx => ?_) hu'
  rw [D.XU_linear y hξ hL hne hb hx, D.a0_eq_inv_lin y hξ hL hne hb]
  ring

lemma XV_deriv_flat {v : ℝ} (hv : |v| ≤ D.densityRadius y) : deriv D.XV v = D.b0 := by
  have hr := D.densityRadius_pos y hξ hL hne hb
  apply deriv_linear_closed (D.XV_smooth y hξ hL hne hb)
    (hr.trans_le (min_le_right _ _)) (fun x hx => ?_) (hv.trans (min_le_right _ _))
  change D.wellV.X x = D.b0 * x
  rw [Branch2.Planar.Well.X_linear (D.wellV_hyp y hξ hL hne hb) hx]
  unfold b0
  ring

lemma Js_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Js y p.1 p.2) := by
  have hu := (contDiff_infty_iff_deriv.mp (D.XU_smooth y hξ hL hne hb)).2
  have hv := (contDiff_infty_iff_deriv.mp (D.XV_smooth y hξ hL hne hb)).2
  exact (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
    (contDiff_fst.mul (hu.comp (reCLM.contDiff.comp contDiff_snd)))).mul
    (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
    (contDiff_fst.mul (hv.comp (imCLM.contDiff.comp contDiff_snd))))

lemma Js_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (w : ℂ) : 0 < D.Js y s w := by
  have ha := D.a0_pos_from_pieces y hξ hL hne hb
  have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
  have hu := D.XU_deriv_pos y hξ hL hne hb w.re
  have hv := Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb) w.im
  have convex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < (1 - s) * a + s * b := by
    by_cases h0 : s = 0
    · simp [h0, ha]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs.2) ha.le)
        (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm h0)) hb)
  exact mul_pos (convex _ _ ha hu) (convex _ _ hb0 hv)

lemma Js_flat (s : ℝ) (w : ℂ) (hw : ‖w‖ ≤ D.densityRadius y) : D.Js y s w = D.a0 y * D.b0 := by
  unfold Js
  rw [D.XU_deriv_flat y hξ hL hne hb (Complex.abs_re_le_norm w |>.trans hw),
    D.XV_deriv_flat y hξ hL hne hb (Complex.abs_im_le_norm w |>.trans hw)]
  ring

/-- The concrete density has a positive proper extension without changing the energy disc. -/
theorem densityExtension_hyp {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, Inner.FlatDensity (DensityExtension.extend (D.Js y) (D.a0 y * D.b0) R)
      (-δ) (1 + δ) (D.a0 y * D.b0) (D.densityRadius y) := by
  exact DensityExtension.exists_flat_density (D.Js_smooth y hξ hL hne hb)
    (mul_pos (D.a0_pos_from_pieces y hξ hL hne hb) (D.b0_pos_of_pieces y hξ hL hne hb)) hR
    (D.densityRadius_pos y hξ hL hne hb) (D.Js_flat y hξ hL hne hb)
    (fun _ hs => D.Js_pos y hξ hL hne hb hs)

end SymplecticPacking.HighDim.PlanarGen.Input
