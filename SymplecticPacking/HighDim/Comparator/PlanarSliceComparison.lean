import SymplecticPacking.HighDim.Comparator.PlanarCoreComparison

/-!
# Endpoint comparison for the affine slices
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real
variable {m q : ℕ}

/-- The explicit temperature gives a global softmax error of at most `ξ/64`. -/
theorem sliceInput_smoothing_bounds (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) (R η₀ : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (y : Moments m) (v : ℝ) :
    PolyFn.eval F (Function.update y j (ell y * v)) ≤ (sliceInput Δ F j ell Lν R η₀ ξ).U0 y v ∧
      (sliceInput Δ F j ell Lν R η₀ ξ).U0 y v ≤
        PolyFn.eval F (Function.update y j (ell y * v)) + ξ / 64 := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  have hc : 0 < D.clse := D.clse_pos hξ
  have hn : (0 : ℝ) < F.length := by exact_mod_cast List.length_pos_of_ne_nil hF
  have hlog : Real.log F.length ≤ (F.length : ℝ) + 1 := by
    linarith [Real.log_le_sub_one_of_pos hn]
  have heq : ξ / 64 * D.clse = (F.length : ℝ) + 1 := by
    change ξ / 64 * (8 * ((F.length : ℝ) + 1) / (ξ / 8)) = _
    field_simp
    ring
  have herr : Real.log F.length / D.clse ≤ ξ / 64 := by
    rw [div_le_iff₀ hc, heq]
    exact hlog
  rw [sliceInput_U0_eq_lse]
  exact ⟨HighDim.eval_le_lse hc hF _, (HighDim.lse_le_eval hc hF _).trans (by linarith)⟩

/-- The full slice endpoint satisfies a strict comparison with error below the requested tolerance. -/
theorem sliceInput_core_comparison (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) {R η₀ ξ : ℝ} (hR : 0 < R) (hξ : 0 < ξ)
    {y : Moments m} (hy : ∀ i, |y i| ≤ 4 * R) (hell0 : 0 ≤ ell y)
    (hell : ell y ≤ lenBound Δ j R) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 ≤ 1 - 8 * (sliceInput Δ F j ell Lν R η₀ ξ).eta) :
    PolyFn.eval F (Function.update y j
      (ell y * (Real.pi * ‖(sliceInput Δ F j ell Lν R η₀ ξ).qin y 1 z‖ ^ 2))) <
      Branch2.Cmp.rearr 1 (fun v => PolyFn.eval F (Function.update y j (ell y * v)))
        (Real.pi * ‖z‖ ^ 2) + ξ := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  have hL : 0 ≤ D.L := sliceInput_L_nonneg Δ F j _ _ hR.le _ _
  have hne : D.pieces y ≠ [] := sliceInput_pieces_ne_nil Δ hF j _ _ _ _ _ y
  have hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L := sliceInput_slope_bound Δ F j _ _ _ _ _ y hell0 hell
  have hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M := sliceInput_value_bound Δ F j _ _ hR.le _ _ y hy hell0 hell
  have hcore := D.core_comparison y hξ hL hne hb hbM hz
  let g := fun v => PolyFn.eval F (Function.update y j (ell y * v))
  have hg : Continuous g := (PolyFn.eval_continuous F).comp (by fun_prop)
  have hI : Real.pi * ‖z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := by
    have hη := Input.eta_pos hξ hL (D := D)
    constructor
    · positivity
    · linarith
  have hr := Branch2.Cmp.rearr_le_add (D.U0_smooth y hne).continuous.continuousOn hg.continuousOn hI
    (fun v _ => (sliceInput_smoothing_bounds Δ hF j ell Lν R η₀ hξ y v).2)
  have hlo := (sliceInput_smoothing_bounds Δ hF j ell Lν R η₀ hξ y
    (Real.pi * ‖D.qin y 1 z‖ ^ 2)).1
  change g (Real.pi * ‖D.qin y 1 z‖ ^ 2) < _
  change D.U0 y (Real.pi * ‖D.qin y 1 z‖ ^ 2) <
    Branch2.Cmp.rearr 1 (D.U0 y) (Real.pi * ‖z‖ ^ 2) + 23 * ξ / 64 at hcore
  linarith

/-- The interval minimum is the indexed infimum used by the high-dimensional comparator. -/
theorem rearr_eq_iInf {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) {I : ℝ}
    (hI : I ∈ Icc (0 : ℝ) 1) :
    Branch2.Cmp.rearr 1 g I = ⨅ a : Icc (0 : ℝ) (1 - I), max (g a) (g (a + I)) := by
  haveI : Nonempty (Icc (0 : ℝ) (1 - I)) := ⟨⟨0, le_rfl, by linarith [hI.2]⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun a => Branch2.Cmp.rearr_le hg hI.1 a.property)
  · obtain ⟨a, ha, heq⟩ := Branch2.Cmp.rearr_attained hg hI
    rw [heq]
    have hbelow : BddBelow (Set.range (fun a : Icc (0 : ℝ) (1 - I) => max (g a) (g (a + I)))) := by
      refine ⟨Branch2.Cmp.rearr 1 g I, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact Branch2.Cmp.rearr_le hg hI.1 b.property
    exact ciInf_le hbelow (⟨a, ha⟩ : Icc (0 : ℝ) (1 - I))

end SymplecticPacking.HighDim.PlanarGen
