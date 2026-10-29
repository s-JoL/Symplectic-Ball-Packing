import SymplecticPacking.HighDim.Comparator.PlanarModification
import SymplecticPacking.HighDim.Comparator.Smoothing
import SymplecticPacking.HighDim.Comparator.PlanarJointInverse

/-!
# Analytic data of the polytope slice family
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m q : ℕ}

theorem sliceInput_pieces_ne_nil (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) (y : Moments m) :
    (sliceInput Δ F j ell Lν R η₀ ξ).pieces y ≠ [] := by
  cases F with
  | nil => exact False.elim (hF rfl)
  | cons a F => simp [sliceInput]

theorem sliceInput_slope_bound (Δ : Polytope m q) (F : PolyFn m) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) (y : Moments m)
    (hell0 : 0 ≤ ell y) (hell : ell y ≤ lenBound Δ j R) :
    ∀ p ∈ (sliceInput Δ F j ell Lν R η₀ ξ).pieces y,
      |p.2| ≤ (sliceInput Δ F j ell Lν R η₀ ξ).L := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  have hs : 0 ≤ (F.map fun a => |a.coef j|).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  have ha' : |a.coef j| ≤ (F.map fun a => |a.coef j|).sum :=
    List.single_le_sum (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  change |a.coef j * ell y| ≤ _
  rw [abs_mul, abs_of_nonneg hell0]
  have h1 := mul_le_mul_of_nonneg_right ha' hell0
  have h2 := mul_le_mul_of_nonneg_left hell hs
  change |a.coef j| * ell y ≤ (F.map fun a => |a.coef j|).sum * lenBound Δ j R + 1
  linarith

theorem sliceInput_slope_strict_bound (Δ : Polytope m q) (F : PolyFn m) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) (y : Moments m)
    (hell0 : 0 ≤ ell y) (hell : ell y ≤ lenBound Δ j R) :
    ∀ p ∈ (sliceInput Δ F j ell Lν R η₀ ξ).pieces y,
      |p.2| < (sliceInput Δ F j ell Lν R η₀ ξ).L := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  have hs : 0 ≤ (F.map fun a => |a.coef j|).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  have ha' : |a.coef j| ≤ (F.map fun a => |a.coef j|).sum :=
    List.single_le_sum (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  change |a.coef j * ell y| < _
  rw [abs_mul, abs_of_nonneg hell0]
  have h1 := mul_le_mul_of_nonneg_right ha' hell0
  have h2 := mul_le_mul_of_nonneg_left hell hs
  change |a.coef j| * ell y < (F.map fun a => |a.coef j|).sum * lenBound Δ j R + 1
  linarith

theorem sliceInput_U0_eq_lse (Δ : Polytope m q) (F : PolyFn m) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) (y : Moments m) (v : ℝ) :
    (sliceInput Δ F j ell Lν R η₀ ξ).U0 y v =
      HighDim.lse (sliceInput Δ F j ell Lν R η₀ ξ).clse F (Function.update y j (ell y * v)) := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  apply congrArg (fun t : ℝ => D.clse⁻¹ * Real.log t)
  change ((F.map fun a => (a.eval (Function.update y j 0), a.coef j * ell y)).map
      fun p => Real.exp (D.clse * (p.1 + p.2 * v))).sum =
    (F.map fun a => Real.exp (D.clse * a.eval (Function.update y j (ell y * v)))).sum
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  change Real.exp (D.clse * (a.eval (Function.update y j 0) + a.coef j * ell y * v)) = _
  have he : a.eval (Function.update y j 0) + a.coef j * ell y * v =
      a.eval (Function.update y j (ell y * v)) := by
    rw [AffinePiece.eval_update, AffinePiece.eval_update]
    ring
  rw [he]

theorem sliceInput_U0_joint_smooth (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    {ell : Moments m → ℝ} (hell : ContDiff ℝ ∞ ell) (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) :
    ContDiff ℝ ∞ (fun p : Moments m × ℝ => (sliceInput Δ F j ell Lν R η₀ ξ).U0 p.1 p.2) := by
  simp_rw [sliceInput_U0_eq_lse]
  apply (lse_smooth _ hF).comp
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self, Function.comp_apply] using (hell.comp contDiff_fst).mul contDiff_snd
  · simp only [Function.update_of_ne hi]
    change ContDiff ℝ ∞ ((fun y : Moments m => y i) ∘ (Prod.fst : Moments m × ℝ → Moments m))
    exact (contDiff_apply ℝ ℝ i).comp contDiff_fst

/-- The derivative in the scalar variable is smooth jointly with all moment parameters. -/
theorem joint_partial_deriv {f : Moments m → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun p : Moments m × ℝ => deriv (f p.1) p.2) := by
  have hf' : ContDiff ℝ ∞ (Function.uncurry fun (p : Moments m × ℝ) (v : ℝ) => f p.1 v) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hd : ContDiff ℝ ∞ (fun p : Moments m × ℝ => fderiv ℝ (f p.1) p.2) :=
    ContDiff.fderiv (f := fun (p : Moments m × ℝ) (v : ℝ) => f p.1 v) hf' contDiff_snd (by simp)
  exact hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem sliceInput_U_deriv_joint (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    {ell : Moments m → ℝ} (hell : ContDiff ℝ ∞ ell) (Lν : Fin q → Moments m → ℝ)
    {R η₀ ξ : ℝ} (hR : 0 ≤ R) (hξ : 0 < ξ) (y : Moments m) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => deriv
      ((sliceInput Δ F j ell Lν R η₀ ξ).U p.1) p.2) (y, v) := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  have hL : 0 ≤ D.L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have h0 := (joint_partial_deriv (f := D.U0)
    (sliceInput_U0_joint_smooth Δ hF j hell Lν R η₀ ξ)).contDiffAt (x := (y, v))
  have h1 : ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (p.2 ^ 2)⁻¹) (y, v) :=
    (contDiffAt_snd.pow 2).inv (pow_ne_zero 2 hv.1.ne')
  have h2 : ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => ((1 - p.2) ^ 2)⁻¹) (y, v) :=
    ((contDiffAt_const.sub contDiffAt_snd).pow 2).inv (pow_ne_zero 2 (sub_pos.mpr hv.2).ne')
  have hs : ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => deriv (D.U0 p.1) p.2 +
      D.kappa * (-(p.2 ^ 2)⁻¹ + ((1 - p.2) ^ 2)⁻¹)) (y, v) :=
    h0.add (contDiffAt_const.mul (h1.neg.add h2))
  apply hs.congr_of_eventuallyEq
  have hne : ∀ q, D.pieces q ≠ [] := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hv)] with p hp
  exact D.deriv_U_basic p.1 hξ hL (hne p.1) hp

/-- The genuinely defined critical point is jointly smooth in every moment parameter. -/
theorem sliceInput_vstar_smooth (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    {ell : Moments m → ℝ} (hell : ContDiff ℝ ∞ ell) (Lν : Fin q → Moments m → ℝ)
    {R η₀ ξ : ℝ} (hR : 0 ≤ R) (hξ : 0 < ξ) :
    ContDiff ℝ ∞ (sliceInput Δ F j ell Lν R η₀ ξ).vstar := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  have hL : 0 ≤ D.L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hne : ∀ q, D.pieces q ≠ [] := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ
  have hroot : ∀ y, D.vstar y ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) (D.vstar y) = 0 :=
    fun y => D.vstar_spec_basic y hξ hL (hne y)
  apply contDiff_iff_contDiffAt.mpr
  intro y
  apply contDiffAt_unique_zero (U := univ) (V := Ioo (0 : ℝ) 1) isOpen_univ isOpen_Ioo (mem_univ y)
    (sliceInput_U_deriv_joint Δ hF j hell Lν hR hξ y (hroot y).1)
    (D.U_second_pos_basic y hξ hL (hne y) (hroot y).1).ne'
    (fun q _ => hroot q)
  intro q _ t ht hzero
  exact (D.exists_unique_critical_basic q hξ hL (hne q)).unique ⟨ht, hzero⟩ (hroot q)

end SymplecticPacking.HighDim.PlanarGen
