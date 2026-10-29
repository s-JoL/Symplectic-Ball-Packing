import SymplecticPacking.HighDim.Comparator.PlanarChart
import SymplecticPacking.HighDim.Comparator.PlanarGenOrdinary

/-!
# The normalized and rescaled inner family
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

lemma src_isOpen : IsOpen {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag} :=
  isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) continuous_const

/-- The prescribed inner family is jointly smooth in time and source. -/
theorem qin_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.qin y p.1 p.2)
    (Icc 0 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag}) := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  have hg : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (D.lam p.1, D.fs y p.1 p.2))
      (Icc 0 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag}) :=
    ((D.lam_smooth y hξ hL hne hb hbM).comp contDiff_fst).contDiffOn.prodMk
      (D.fs_smooth y hξ hL hne hb hbM)
  have hh := (Chart.Clam_smooth (D.vstar y) hp).comp hg
    (fun p hp => (D.qin_chart_domain y hξ hL hne hb hbM hp.1 hp.2).1)
  exact hh

lemma fs_differentiableAt {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) : DifferentiableAt ℝ (D.fs y s) z := by
  have hh := (D.fs_smooth y hξ hL hne hb hbM).comp
    ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (show MapsTo (fun u : ℂ => (s, u)) {u : ℂ | Real.pi * ‖u‖ ^ 2 < D.pdag}
      (Icc 0 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag}) from fun _ hu => ⟨hs, hu⟩)
  exact (hh.contDiffAt ((D.src_isOpen y hξ hL hne hb hbM).mem_nhds hz)).differentiableAt (by simp)

lemma qin_differentiableAt {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) : DifferentiableAt ℝ (D.qin y s) z := by
  have hh := (D.qin_smooth y hξ hL hne hb hbM).comp
    ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (show MapsTo (fun u : ℂ => (s, u)) {u : ℂ | Real.pi * ‖u‖ ^ 2 < D.pdag}
      (Icc 0 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag}) from fun _ hu => ⟨hs, hu⟩)
  exact (hh.contDiffAt ((D.src_isOpen y hξ hL hne hb hbM).mem_nhds hz)).differentiableAt (by simp)

/-- Every map in the inner family has Jacobian determinant one. -/
theorem qin_det {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    LinearMap.det (fderiv ℝ (D.qin y s) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  have hdom := (D.qin_chart_domain y hξ hL hne hb hbM hs hz).1
  have hC := (Chart.Clam_slice_contDiffAt (D.vstar y) hp hdom).differentiableAt (by simp)
  change LinearMap.det (fderiv ℝ (Chart.Clam (D.vstar y) (D.lam s) ∘ D.fs y s) z : ℂ →ₗ[ℝ] ℂ) = 1
  rw [fderiv_comp z hC (D.fs_differentiableAt y hξ hL hne hb hbM hs hz),
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    Chart.Clam_det (D.vstar y) hp (D.lam_range y hξ hL hne hb hbM s).1 hdom,
    D.fs_det y hξ hL hne hb hbM hs hz, mul_one]

/-- The inner family remains injective throughout the deformation. -/
theorem qin_injOn {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    InjOn (D.qin y s) {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag} := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  intro u hu v hv huv
  have hdomU := D.qin_chart_domain y hξ hL hne hb hbM hs hu
  have hdomV := D.qin_chart_domain y hξ hL hne hb hbM hs hv
  apply D.fs_injOn y hξ hL hne hb hbM hs hu hv
  apply Chart.Clam_injOn (D.vstar y) hp (D.lam_range y hξ hL hne hb hbM s).1 _ _ huv
  · simpa only [Chart.chartDom, mem_setOf_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hdomU
  · simpa only [Chart.chartDom, mem_setOf_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hdomV

/-- The initial map is the prescribed affine symplectic chart. -/
theorem qin_zero (z : ℂ) : D.qin y 0 z = D.bpt y + D.A0 y z := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  unfold qin
  rw [D.lam_zero_from_pieces y hξ hL hne hb hbM, D.fs_zero y hξ hL hne hb]
  change Chart.Clam (D.vstar y) 0 _ = _
  rw [Chart.Clam_zero_eq (D.vstar y) hp, Chart.DC0_apply]
  unfold A0 A11 A22
  change D.bpt y + _ = D.bpt y + _
  congr 1
  simp only [ofReal_re, add_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, zero_mul, zero_add, mul_one]
  simp only [Chart.rb, rb]
  push_cast
  ring

/-- At time one the rescaled chart is the original polar chart. -/
theorem qin_one {z : ℂ} (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    D.qin y 1 z = Branch2.Planar.chart (D.vstar y) (D.fs y 1 z) := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  have hdom := (D.qin_chart_domain y hξ hL hne hb hbM ⟨zero_le_one, le_rfl⟩ hz).1
  rw [D.lam_one_from_pieces y hξ hL hne hb hbM, one_mul] at hdom
  unfold qin
  rw [D.lam_one_from_pieces y hξ hL hne hb hbM]
  change Chart.Clam (D.vstar y) 1 _ = _
  rw [Chart.Clam_eq (D.vstar y) hp one_pos (by simpa using hdom.le), one_smul, ofReal_one, div_one]
  ring

lemma Pmin_pos_from_pieces : 0 < D.Pmin := by
  unfold Pmin
  exact div_pos (lt_min (r0_pos hξ hL) (D.dP_pos_from_pieces y hξ hL hne hb hbM)) (by norm_num)

lemma chart_coefficient_bound :
    (Real.pi * D.rb y)⁻¹ + 2 * Real.pi * D.rb y ≤ D.MC := by
  have hp := (D.vstar_spec y hξ hL hne hb).1
  have hrb : 0 < D.rb y := Real.sqrt_pos.mpr (div_pos hp.1 Real.pi_pos)
  have hmin := D.Pmin_pos_from_pieces y hξ hL hne hb hbM
  have hmin4 : 4 * D.Pmin ≤ D.r0 := by
    unfold Pmin
    linarith [min_le_left D.r0 D.dP]
  have hvs := (D.vstar_uniform_bounds y hξ hL hne hb).1
  have hsquare : (Real.pi * D.rb y) ^ 2 = Real.pi * D.vstar y := by
    unfold rb
    rw [mul_pow, Real.sq_sqrt (div_pos hp.1 Real.pi_pos).le]
    field_simp
  have hsmall : 2 * Real.sqrt (Real.pi * D.Pmin) ≤ Real.pi * D.rb y := by
    have hs := Real.sq_sqrt (mul_pos Real.pi_pos hmin).le
    have hg := mul_le_mul_of_nonneg_left (hmin4.trans hvs) Real.pi_pos.le
    apply (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (Real.pi * D.Pmin)) (mul_pos Real.pi_pos hrb).le).mp
    nlinarith [hsquare, hs, hg]
  have hbig : Real.pi * D.rb y ≤ Real.sqrt (Real.pi * Pmax) := by
    have hs := Real.sq_sqrt (mul_pos Real.pi_pos (by norm_num [Pmax] : (0 : ℝ) < Pmax)).le
    have hg := mul_le_mul_of_nonneg_left (hp.2.le.trans (by norm_num [Pmax] : (1 : ℝ) ≤ Pmax)) Real.pi_pos.le
    apply (sq_le_sq₀ (mul_pos Real.pi_pos hrb).le (Real.sqrt_nonneg _)).mp
    nlinarith [hsquare, hs, hg]
  have hrecip := one_div_le_one_div_of_le (mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hmin))) hsmall
  unfold MC
  simpa only [one_div, mul_assoc] using add_le_add hrecip (mul_le_mul_of_nonneg_left hbig two_pos.le)

/-- Uniform image bound used by the five-segment support construction. -/
theorem qin_bound {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) : ‖D.qin y s z - D.bpt y‖ ≤ D.Bstar := by
  have hp := (D.vstar_spec y hξ hL hne hb).1.1
  have hcoord := D.fs_coordinate_bounds y hξ hL hne hb hbM hs hz
  have hnorm : ‖D.fs y s z‖ ≤ Real.sqrt (D.Xbar ^ 2 + D.Ybar ^ 2) := by
    have hu := (sq_le_sq₀ (abs_nonneg _) (D.Xbar_pos y hξ hL hne hb hbM).le).mpr hcoord.1
    have hv := (sq_le_sq₀ (abs_nonneg _) (D.Ybar_pos y hξ hL hne hb hbM).le).mpr hcoord.2
    rw [sq_abs] at hu hv
    rw [← Real.sqrt_sq (norm_nonneg _)]
    apply Real.sqrt_le_sqrt
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hh := Chart.Clam_norm_sub (D.vstar y) hp (D.lam s) (D.fs y s z)
  have hcoef := D.chart_coefficient_bound y hξ hL hne hb hbM
  exact hh.trans (mul_le_mul hcoef hnorm (norm_nonneg _) (by
    unfold MC
    have hmin := D.Pmin_pos_from_pieces y hξ hL hne hb hbM
    positivity))

/-- At the terminal time the whole source disc is strictly inside the support radius. -/
theorem qin_bound_one {z : ℂ} (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) : ‖D.qin y 1 z‖ ≤ D.Rq := by
  have hs : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hm := D.late_Fs_margins y hξ hL hne hb hbM hs
    (show 1 - D.ds ≤ 1 by linarith [D.ds_pos_from_pieces y hξ hL hne hb hbM])
    (D.normalizer_energy y hξ hL hne hb hbM hs hz).le
  change D.dP / 2 < D.vstar y + (D.fs y 1 z).re ∧
    D.vstar y + (D.fs y 1 z).re < 1 - D.dP / 2 ∧ _ at hm
  rw [D.qin_one y hξ hL hne hb hbM hz]
  have hdom := (D.qin_chart_domain y hξ hL hne hb hbM hs hz).1
  rw [D.lam_one_from_pieces y hξ hL hne hb hbM, one_mul] at hdom
  have hmoment := Branch2.Planar.chart_moment hdom.le
  unfold Rq
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith [hm.2.1]

/-- All seven concrete inner-family properties. -/
theorem innerHyp : D.InnerHyp y where
  smooth := D.qin_smooth y hξ hL hne hb hbM
  q_zero := D.qin_zero y hξ hL hne hb hbM
  injOn := fun _ hs => D.qin_injOn y hξ hL hne hb hbM hs
  diff := fun _ hs _ hz => D.qin_differentiableAt y hξ hL hne hb hbM hs hz
  det := fun _ hs _ hz => D.qin_det y hξ hL hne hb hbM hs hz
  bound := fun _ hs _ hz => D.qin_bound y hξ hL hne hb hbM hs hz
  bound_one := fun _ hz => D.qin_bound_one y hξ hL hne hb hbM hz

/-- The finite coefficient envelopes imply the complete hypotheses of the five-segment path. -/
theorem yHyp_of_pieces : D.YHyp y := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hv := D.vstar_uniform_bounds y hξ hL hne hb
  have ha := D.alphaU_bounds y hξ hL hne hb
  exact ⟨hξ, hL, hM, D.b0_pos_of_pieces y hξ hL hne hb, hv.1, hv.2, ha.1, ha.2,
    D.innerHyp y hξ hL hne hb hbM⟩

/-- Ordinariness follows from the coefficients, without an inner-family assumption. -/
theorem ordinary_of_pieces : Qhat.OrdinaryPath (D.pathData y) :=
  ordinary_of_yhyp (D.yHyp_of_pieces y hξ hL hne hb hbM)

end SymplecticPacking.HighDim.PlanarGen.Input
