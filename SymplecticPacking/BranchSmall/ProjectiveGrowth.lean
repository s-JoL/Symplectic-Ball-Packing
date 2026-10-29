import Mathlib

/-!
# Vanishing normal components near a projective hyperplane

A smooth vector field on a compact annulus whose first component vanishes on
`Z_* = 0` has that component bounded by a constant times `|Z_*|`. This is the
analytic estimate needed when passing a homogeneous lift to an affine chart.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open scoped ContDiff

section normal
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Uniform first-order vanishing on a compact annulus, with a compact time parameter. -/
theorem annulus_normal_component_bound {U : Set (ℝ × (ℂ × F))} (hU : IsOpen U)
    (hIU : Icc (0 : ℝ) 1 ×ˢ ({x : ℂ × F | x ≠ 0}) ⊆ U)
    {Y : ℝ → (ℂ × F) → (ℂ × F)}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × (ℂ × F) => Y p.1 p.2) U)
    (hzero : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : F, v ≠ 0 → (Y s (0, v)).1 = 0)
    {c R : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : ℂ × F,
      c ≤ ‖x‖ → ‖x‖ ≤ R → ‖(Y s x).1‖ ≤ L * ‖x.1‖ := by
  let K : Set (ℂ × F) := {x | c / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ × F) R).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R from hx.2)
  have hKU : Icc (0 : ℝ) 1 ×ˢ K ⊆ U := by
    intro p hp
    apply hIU ⟨hp.1, ?_⟩
    intro hz
    have := hp.2.1
    rw [hz, norm_zero] at this
    linarith
  let H : ℝ × (ℂ × F) → ℂ := fun p => (Y p.1 p.2).1
  have hH : ContDiffOn ℝ ∞ H U := hY.fst
  let D : ℝ × (ℂ × F) → (ℂ × F) →L[ℝ] ℂ := fun p =>
    (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (ℂ × F))
  have hD : ContinuousOn D (Icc (0 : ℝ) 1 ×ˢ K) :=
    (((hH.fderiv_of_isOpen (m := ∞) hU (by simp)).continuousOn).clm_comp continuousOn_const).mono hKU
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hD
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hH.continuousOn.mono hKU)
  let L : ℝ := max (max B 0) (max A 0 * (2 / c))
  have hL0 : 0 ≤ L := (le_max_right B 0).trans (le_max_left _ _)
  refine ⟨L, hL0, ?_⟩
  intro s hs x hcx hxR
  have hxK : x ∈ K := ⟨by linarith, hxR⟩
  by_cases hxstar : c / 2 ≤ ‖x.1‖
  · have hscale : (1 : ℝ) ≤ (2 / c) * ‖x.1‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    calc
      ‖(Y s x).1‖ ≤ max A 0 := (hA (s, x) ⟨hs, hxK⟩).trans (le_max_left _ _)
      _ ≤ (max A 0 * (2 / c)) * ‖x.1‖ := by nlinarith [le_max_right A 0]
      _ ≤ L * ‖x.1‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · have htail : c ≤ ‖x.2‖ := by
      rw [Prod.norm_def] at hcx
      apply le_of_not_gt
      intro htail
      have hstar : ‖x.1‖ < c := by linarith
      exact not_lt_of_ge hcx (max_lt hstar htail)
    have htail0 : x.2 ≠ 0 := by intro hz; rw [hz, norm_zero] at htail; linarith
    let S : Set (ℂ × F) := Metric.closedBall (0 : ℂ) ‖x.1‖ ×ˢ ({x.2} : Set F)
    have hS : Convex ℝ S := (convex_closedBall _ _).prod (convex_singleton _)
    have hSK : S ⊆ K := by
      intro y hy
      have hy1 : ‖y.1‖ ≤ ‖x.1‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy.1
      have hy2 : y.2 = x.2 := hy.2
      constructor
      · rw [Prod.norm_def, hy2]
        exact (by linarith : c / 2 ≤ ‖x.2‖).trans (le_max_right _ _)
      · rw [Prod.norm_def, hy2]
        exact max_le (hy1.trans (norm_fst_le x |>.trans hxR)) (norm_snd_le x |>.trans hxR)
    have hdiff (y : ℂ × F) (hy : y ∈ S) : DifferentiableAt ℝ (fun y => (Y s y).1) y := by
      exact ((hH.contDiffAt (hU.mem_nhds (hKU ⟨hs, hSK hy⟩))).differentiableAt (by simp)).comp y
        (differentiableAt_const s |>.prodMk differentiableAt_id)
    have hbound (y : ℂ × F) (hy : y ∈ S) : ‖fderiv ℝ (fun y => (Y s y).1) y‖ ≤ max B 0 := by
      have hd := ((hH.contDiffAt (hU.mem_nhds (hKU ⟨hs, hSK hy⟩))).differentiableAt (by simp)).hasFDerivAt.comp y
        ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
      have he : fderiv ℝ (fun y => (Y s y).1) y = D (s, y) := by convert! hd.fderiv using 1
      rw [he]
      exact (hB (s, y) ⟨hs, hSK hy⟩).trans (le_max_left _ _)
    have hzS : ((0 : ℂ), x.2) ∈ S := ⟨by simp [norm_nonneg], rfl⟩
    have hxS : x ∈ S := ⟨by simp, rfl⟩
    have hm := hS.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hzS hxS
    rw [hzero s hs x.2 htail0, sub_zero] at hm
    have hnorm : ‖x - ((0 : ℂ), x.2)‖ = ‖x.1‖ := by simp [Prod.norm_def]
    rw [hnorm] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))


/-- A globally smooth lift needs only a ball bound. An extra fixed coordinate avoids the
puncture in the annular estimate. -/
theorem smooth_normal_component_bound {Y : ℝ → (ℂ × F) → (ℂ × F)}
    (hY : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × F) => Y p.1 p.2))
    (hzero : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : F, (Y s (0, v)).1 = 0) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : ℂ × F,
      ‖x‖ ≤ R → ‖(Y s x).1‖ ≤ L * ‖x.1‖ := by
  let Y' : ℝ → (ℂ × (ℝ × F)) → (ℂ × (ℝ × F)) :=
    fun s x => ((Y s (x.1, x.2.2)).1, 0)
  have hY' : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × (ℝ × F)) => Y' p.1 p.2) :=
    (hY.comp (contDiff_fst.prodMk
      (contDiff_snd.fst.prodMk contDiff_snd.snd.snd))).fst.prodMk contDiff_const
  obtain ⟨L, hL, hbound⟩ := annulus_normal_component_bound (U := univ) isOpen_univ
    (subset_univ _) hY'.contDiffOn
    (fun s hs v _ => hzero s hs v.2) (c := 1) (R := max 1 R) zero_lt_one
  refine ⟨L, hL, ?_⟩
  intro s hs x hx
  have hc : (1 : ℝ) ≤ ‖(x.1, ((1 : ℝ), x.2))‖ := by
    simp only [Prod.norm_def, norm_one]
    exact (le_max_left (1 : ℝ) ‖x.2‖).trans (le_max_right _ _)
  have hR : ‖(x.1, ((1 : ℝ), x.2))‖ ≤ max 1 R := by
    simp only [Prod.norm_def, norm_one]
    exact max_le ((norm_fst_le x |>.trans hx).trans (le_max_right _ _))
      (max_le (le_max_left _ _) ((norm_snd_le x |>.trans hx).trans (le_max_right _ _)))
  exact hbound s hs (x.1, ((1 : ℝ), x.2)) hc hR

end normal
end SymplecticPacking.BranchSmall.VT
