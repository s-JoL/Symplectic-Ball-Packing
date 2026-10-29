import SymplecticPacking.HighDim.Comparator.PlanarPotentialBounds

/-!
# Critical-point properties without quantitative slope hypotheses

Existence and uniqueness hold for every nonempty affine family. The quantitative
slope bound is needed only for the uniform neighbourhood estimates.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
    (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
include hξ hL hne

theorem U0_convex_basic : ConvexOn ℝ univ (D.U0 y) := by
  rw [D.U0_eq_lse_potential y]
  have hs := LSE.potential_smooth hne D.clse
  apply convexOn_univ_of_deriv2_nonneg (hs.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp))
  intro v
  change 0 ≤ deriv (deriv (LSE.potential (D.pieces y) D.clse)) v
  rw [LSE.potential_second hne (clse_pos hξ).ne']
  exact mul_nonneg (clse_pos hξ).le (LSE.variance_nonneg hne _ _)

theorem U_smooth_basic : ContDiffOn ℝ ∞ (D.U y) (Ioo (0 : ℝ) 1) := by
  change ContDiffOn ℝ ∞ (fun v => D.U0 y v + D.kappa * (1 / v + 1 / (1 - v))) _
  exact (D.U0_smooth y hne).contDiffOn.add (contDiffOn_const.mul
    ((contDiffOn_const.div contDiffOn_id (fun v hv => hv.1.ne')).add
      (contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id) (fun v hv => (sub_pos.mpr hv.2).ne'))))

theorem U_strictConvex_basic : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (D.U y) := by
  have he : D.U y = D.U0 y + fun v => D.kappa * (1 / v + 1 / (1 - v)) := rfl
  rw [he]
  refine ((D.U0_convex_basic y hξ hL hne).subset (subset_univ _) (convex_Ioo _ _)).add_strictConvexOn ?_
  refine ⟨convex_Ioo _ _, fun x hx z hz hxz a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hh := Branch2.Planar.PlanarInput.barrier_strict (c := 0) hx hz hxz ha hb hab
  simp only [sub_zero] at hh
  have hk := kappa_pos hξ hL
  nlinarith [mul_lt_mul_of_pos_left hh hk]

theorem U_proper_basic :
    Tendsto (D.U y) (𝓝[>] (0 : ℝ)) atTop ∧ Tendsto (D.U y) (𝓝[<] (1 : ℝ)) atTop := by
  have hk := kappa_pos hξ hL
  have hU0 := (D.U0_smooth y hne).continuous
  constructor
  · have hc : ContinuousAt (fun v => D.U0 y v + D.kappa * (1 / (1 - v))) 0 := by
      refine hU0.continuousAt.add (continuousAt_const.mul
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) ?_))
      norm_num
    have hh := (tendsto_inv_nhdsGT_zero.const_mul_atTop hk).atTop_add
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine hh.congr fun v => ?_
    simp only [U]
    ring
  · have hc : ContinuousAt (fun v => D.U0 y v + D.kappa * (1 / v)) 1 := by
      exact hU0.continuousAt.add (continuousAt_const.mul (continuousAt_const.div continuousAt_id one_ne_zero))
    have hsub : Tendsto (fun v : ℝ => 1 - v) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hh := (show Continuous (fun v : ℝ => 1 - v) from continuous_const.sub continuous_id).tendsto 1
        simpa using hh.mono_left nhdsWithin_le_nhds
      · exact Filter.mem_of_superset self_mem_nhdsWithin (fun v (hv : v < 1) => sub_pos.mpr hv)
    have hh := ((tendsto_inv_nhdsGT_zero.comp hsub).const_mul_atTop hk).atTop_add
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine hh.congr fun v => ?_
    simp only [U, Function.comp_apply]
    ring

theorem exists_minimum_basic : ∃ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, D.U y p ≤ D.U y v := by
  have hh : (0 : ℝ) < 1 := zero_lt_one
  set c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  obtain ⟨hl, hr⟩ := D.U_proper_basic y hξ hL hne
  have e1 : {x | D.U y c < D.U y x} ∈ 𝓝[>] (0 : ℝ) := hl (eventually_gt_atTop _)
  have e2 : {x | D.U y c < D.U y x} ∈ 𝓝[<] (1 : ℝ) := hr (eventually_gt_atTop _)
  obtain ⟨a₁, ha₁, hsub1⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp e1
  obtain ⟨b₁, hb₁, hsub2⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp e2
  simp only [mem_Ioi] at ha₁
  simp only [mem_Iio] at hb₁
  set a := min (a₁ / 2) (c / 2)
  set b := max ((b₁ + 1) / 2) ((c + 1) / 2)
  have ha0 : 0 < a := lt_min (by linarith) (by norm_num [c])
  have hac : a < c := (min_le_right _ _).trans_lt (by norm_num [c])
  have haa : a < a₁ := (min_le_left _ _).trans_lt (by linarith)
  have hcb : c < b := lt_of_lt_of_le (by norm_num [c]) (le_max_right _ _)
  have hbh : b < 1 := max_lt (by linarith) (by norm_num [c])
  have hbb : b₁ < b := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨c, hac.le, hcb.le⟩
    ((D.U_smooth_basic y hξ hL hne).continuousOn.mono hsub)
  refine ⟨p, hsub hp, fun v hv => ?_⟩
  have hpc : D.U y p ≤ D.U y c := hmin ⟨hac.le, hcb.le⟩
  by_cases hva : v < a
  · have hv' := hsub1 ⟨hv.1, by linarith⟩
    change D.U y c < D.U y v at hv'
    linarith
  by_cases hvb : b < v
  · have hv' := hsub2 ⟨by linarith, hv.2⟩
    change D.U y c < D.U y v at hv'
    linarith
  exact hmin ⟨not_lt.mp hva, not_lt.mp hvb⟩

theorem exists_unique_critical_basic : ∃! p, p ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) p = 0 := by
  obtain ⟨p, hp, hmin⟩ := D.exists_minimum_basic y hξ hL hne
  have hloc : IsLocalMin (D.U y) p := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with v hv using hmin v hv
  refine ⟨p, ⟨hp, hloc.deriv_eq_zero⟩, fun v ⟨hv, hv0⟩ => ?_⟩
  have hm := (D.U_strictConvex_basic y hξ hL hne).strictMonoOn_deriv
    (fun v hv => ((D.U_smooth_basic y hξ hL hne).contDiffAt (isOpen_Ioo.mem_nhds hv)).differentiableAt (by simp))
  exact hm.injOn hv hp (by rw [hv0, hloc.deriv_eq_zero])

theorem vstar_spec_basic : D.vstar y ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) (D.vstar y) = 0 := by
  have h := D.exists_unique_critical_basic y hξ hL hne
  unfold vstar
  rw [dif_pos h]
  exact Explicit.the_spec h

theorem deriv_U_basic {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (D.U y) v = deriv (D.U0 y) v + D.kappa * (-(v ^ 2)⁻¹ + ((1 - v) ^ 2)⁻¹) := by
  have h0 := ((D.U0_smooth y hne).differentiable (by simp) v).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => 1 / t) (-(v ^ 2)⁻¹) v := by
    simpa only [one_div] using hasDerivAt_inv hv.1.ne'
  have h2 : HasDerivAt (fun t : ℝ => 1 / (1 - t)) (((1 - v) ^ 2)⁻¹) v := by
    have hh := ((hasDerivAt_id' v).const_sub 1).inv (sub_pos.mpr hv.2).ne'
    simp only [one_div]
    exact hh.congr_deriv (by rw [neg_neg, one_div])
  exact (h0.add ((h1.add h2).const_mul D.kappa)).deriv

theorem U_second_formula_basic {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (D.U y)) v = deriv (deriv (D.U0 y)) v +
      2 * D.kappa * ((v ^ 3)⁻¹ + ((1 - v) ^ 3)⁻¹) := by
  have he : deriv (D.U y) =ᶠ[𝓝 v] fun t => deriv (D.U0 y) t +
      D.kappa * (-(t ^ 2)⁻¹ + ((1 - t) ^ 2)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    exact D.deriv_U_basic y hξ hL hne ht
  rw [he.deriv_eq]
  have h0 := (((contDiff_infty_iff_deriv.mp (D.U0_smooth y hne)).2).differentiable (by simp) v).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2)⁻¹) (2 / v ^ 3) v := by
    have hh := (((hasDerivAt_id v).pow 2).inv (pow_ne_zero 2 hv.1.ne')).neg
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp [hv.1.ne']
      <;> ring
  have h2 : HasDerivAt (fun t : ℝ => ((1 - t) ^ 2)⁻¹) (2 / (1 - v) ^ 3) v := by
    have hh := ((((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).pow 2).inv
      (pow_ne_zero 2 (sub_pos.mpr hv.2).ne'))
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub, mul_neg_one]
      field_simp [(sub_pos.mpr hv.2).ne']
      <;> ring
  have hh : HasDerivAt (fun t => deriv (D.U0 y) t +
      D.kappa * (-(t ^ 2)⁻¹ + ((1 - t) ^ 2)⁻¹))
      (deriv (deriv (D.U0 y)) v + D.kappa * (2 / v ^ 3 + 2 / (1 - v) ^ 3)) v :=
    h0.add ((h1.add h2).const_mul D.kappa)
  convert hh.deriv using 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem U_second_pos_basic {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (deriv (D.U y)) v := by
  rw [D.U_second_formula_basic y hξ hL hne hv]
  have hn : 0 ≤ deriv (deriv (D.U0 y)) v := by
    rw [D.U0_eq_lse_potential y, LSE.potential_second hne (clse_pos hξ).ne']
    exact mul_nonneg (clse_pos hξ).le (LSE.variance_nonneg hne _ _)
  have hk := kappa_pos hξ hL
  have h1 : 0 < (v ^ 3)⁻¹ := inv_pos.mpr (pow_pos hv.1 3)
  have h2 : 0 < ((1 - v) ^ 3)⁻¹ := inv_pos.mpr (pow_pos (sub_pos.mpr hv.2) 3)
  positivity

end SymplecticPacking.HighDim.PlanarGen.Input
