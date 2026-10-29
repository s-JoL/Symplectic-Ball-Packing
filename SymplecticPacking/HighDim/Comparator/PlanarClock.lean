import SymplecticPacking.HighDim.Comparator.PlanarMargins

/-!
# The explicit clock and chart-domain control
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
include hξ hL hne hb hbM

lemma dP_pos_from_pieces : 0 < D.dP := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hk := kappa_pos hξ hL
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have ht : 0 < D.tol := by unfold tol; positivity
  unfold dP
  positivity

lemma dTh_pos_from_pieces : 0 < D.dTh := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have ht : 0 < D.tol := by unfold tol; positivity
  have hn := nu_pos hξ hL
  have hA : 0 < D.Ebar + D.tol + 1 := by positivity
  have hAn : 0 < D.Ebar + D.tol + 1 + D.nu := by positivity
  have hr : (D.Ebar + D.tol + 1) / (D.Ebar + D.tol + 1 + D.nu) < 1 :=
    (div_lt_one hAn).mpr (by linarith)
  have hs : Real.sqrt ((D.Ebar + D.tol + 1) / (D.Ebar + D.tol + 1 + D.nu)) < 1 :=
    (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hr)
  unfold dTh
  linarith

lemma ds_pos_from_pieces : 0 < D.ds := by
  unfold ds
  exact lt_min (by norm_num) (lt_min
    (div_pos (D.dP_pos_from_pieces y hξ hL hne hb hbM)
      (mul_pos two_pos (D.Xbar_pos y hξ hL hne hb hbM)))
    (div_pos (D.dTh_pos_from_pieces y hξ hL hne hb hbM)
      (mul_pos two_pos (D.Ybar_pos y hξ hL hne hb hbM))))

lemma lambda0_bounds : 0 < D.lambda0 ∧ D.lambda0 ≤ 1 / 2 := by
  have hr := r0_pos hξ hL
  have hX := D.Xbar_pos y hξ hL hne hb hbM
  have hY := D.Ybar_pos y hξ hL hne hb hbM
  exact ⟨lt_min (lt_min (by norm_num) (div_pos hr (by positivity)))
    (div_pos zero_lt_one (by positivity)), (min_le_left _ _).trans (min_le_left _ _)⟩

lemma lam_smooth : ContDiff ℝ ∞ D.lam := by
  unfold lam
  exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).add contDiff_const).div_const _)))

lemma lam_range (s : ℝ) : 0 ≤ D.lam s ∧ D.lam s ≤ 1 := by
  have hl := D.lambda0_bounds y hξ hL hne hb hbM
  have h1 := Real.smoothTransition.nonneg (2 * s)
  have h2 := Real.smoothTransition.nonneg ((s - 1 + D.ds) / D.ds)
  have h3 := Real.smoothTransition.le_one (2 * s)
  have h4 := Real.smoothTransition.le_one ((s - 1 + D.ds) / D.ds)
  unfold lam
  constructor
  · exact add_nonneg (mul_nonneg hl.1.le h1) (mul_nonneg (by linarith [hl.2]) h2)
  · nlinarith

lemma lam_early_bound {s : ℝ} (hs : s ≤ 1 - D.ds) : D.lam s ≤ D.lambda0 := by
  have hd := D.ds_pos_from_pieces y hξ hL hne hb hbM
  have hz := Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith : s - 1 + D.ds ≤ 0) hd.le)
  unfold lam
  rw [hz, mul_zero, add_zero]
  exact mul_le_of_le_one_right (D.lambda0_bounds y hξ hL hne hb hbM).1.le (Real.smoothTransition.le_one _)

lemma lam_zero_from_pieces : D.lam 0 = 0 := by
  have hd : D.ds ≤ 1 / 4 := min_le_left _ _
  unfold lam
  rw [mul_zero, Real.smoothTransition.zero_of_nonpos (by norm_num : (0 : ℝ) ≤ 0)]
  have hz := Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (show 0 - 1 + D.ds ≤ 0 by linarith) (D.ds_pos_from_pieces y hξ hL hne hb hbM).le)
  rw [hz]
  ring

lemma lam_one_from_pieces : D.lam 1 = 1 := by
  have hd := D.ds_pos_from_pieces y hξ hL hne hb hbM
  unfold lam
  rw [mul_one, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2), sub_self, zero_add,
    div_self hd.ne', Real.smoothTransition.one_of_one_le (le_refl 1)]
  ring

lemma lambda0_mul_bounds : D.lambda0 * D.Xbar ≤ D.r0 / 2 ∧ D.lambda0 * D.Ybar ≤ 1 / 4 := by
  have hX := D.Xbar_pos y hξ hL hne hb hbM
  have hY := D.Ybar_pos y hξ hL hne hb hbM
  have hx := (le_div_iff₀ (mul_pos two_pos hX)).mp
    (show D.lambda0 ≤ D.r0 / (2 * D.Xbar) from (min_le_left _ _).trans (min_le_right _ _))
  have hy := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hY)).mp
    (show D.lambda0 ≤ 1 / (4 * D.Ybar) from min_le_right _ _)
  constructor <;> linarith

/-- Every intermediate rescaled chart stays away from the radial and angular singularities. -/
theorem qin_chart_domain {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    0 < D.vstar y + D.lam s * (D.fs y s z).re ∧ |D.lam s * (D.fs y s z).im| < 1 / 2 := by
  have hl := D.lam_range y hξ hL hne hb hbM s
  have hx := D.fs_coordinate_bounds y hξ hL hne hb hbM hs hz
  have hr := D.vstar_uniform_bounds y hξ hL hne hb
  have hr0 := r0_pos hξ hL
  rw [abs_mul, abs_of_nonneg hl.1]
  rcases le_or_gt s (1 - D.ds) with hearly | hlate
  · have hclock := D.lam_early_bound y hξ hL hne hb hbM hearly
    have hc := D.lambda0_mul_bounds y hξ hL hne hb hbM
    have hcx := (mul_le_mul hclock hx.1 (abs_nonneg _) (D.lambda0_bounds y hξ hL hne hb hbM).1.le).trans hc.1
    have hcy := (mul_le_mul hclock hx.2 (abs_nonneg _) (D.lambda0_bounds y hξ hL hne hb hbM).1.le).trans hc.2
    have hax : |D.lam s * (D.fs y s z).re| ≤ D.r0 / 2 := by rwa [abs_mul, abs_of_nonneg hl.1]
    exact ⟨by linarith [(abs_le.mp hax).1, hr.1], by linarith⟩
  · have hm := D.late_Fs_margins y hξ hL hne hb hbM hs hlate.le
      (D.normalizer_energy y hξ hL hne hb hbM hs hz).le
    change D.dP / 2 < D.vstar y + (D.fs y s z).re ∧
      D.vstar y + (D.fs y s z).re < 1 - D.dP / 2 ∧
      |(D.fs y s z).im| < 1 / 2 - D.dTh / 2 at hm
    have hp := D.dP_pos_from_pieces y hξ hL hne hb hbM
    have ht := D.dTh_pos_from_pieces y hξ hL hne hb hbM
    have hv := (D.vstar_spec y hξ hL hne hb).1.1
    constructor
    · have hc : D.vstar y + D.lam s * (D.fs y s z).re =
          (1 - D.lam s) * D.vstar y + D.lam s * (D.vstar y + (D.fs y s z).re) := by ring
      rw [hc]
      by_cases h0 : D.lam s = 0
      · simp [h0, hv]
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hl.2) hv.le)
          (mul_pos (lt_of_le_of_ne hl.1 (Ne.symm h0)) (by linarith [hm.1]))
    · have hc := mul_le_of_le_one_left (abs_nonneg (D.fs y s z).im) hl.2
      linarith [hm.2.2]

end SymplecticPacking.HighDim.PlanarGen.Input
