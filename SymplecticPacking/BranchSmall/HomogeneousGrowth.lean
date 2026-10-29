import SymplecticPacking.BranchSmall.HomogeneousReturn
import SymplecticPacking.BranchSmall.ProjectedGrowth

/-!
# Compact homogeneous representatives of the return field

The compact shell extension is used only to obtain uniform analytic bounds. Its
normal coordinate is antisymmetrized under the infinity reflection, so it vanishes
on the infinity hyperplane without changing the field on the unit sphere.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

variable {m : ℕ}

theorem exists_return_homogeneous_shell_extension (a : Fin m → ℂ) {b lo hi : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (hlo : 0 < lo) :
    ∃ Y : ℝ → HomogeneousInput m → HomogeneousInput m,
      ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => Y p.1 p.2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexCartesian z ∈ phaseShell lo hi →
        Y s z = complexCartesian.symm (homogeneousConeField (homogeneousCartesian a 1)
          (1 / Real.pi) b s (complexCartesian z))) ∧
      (∀ s z, z none = 0 → Y s z none = 0) := by
  have hc : 0 < 1 / Real.pi := one_div_pos.mpr Real.pi_pos
  obtain ⟨Φ, Ψ, _, _, _, _, _, _, V, hV, _, hVe⟩ :=
    exists_homogeneousCone_shell_flow (homogeneousCartesian_smooth a 1)
      (fun _ hz => homogeneousCartesian_nonzero a 1 hz) (homogeneousCartesian_euler a 1)
      (homogeneousCartesian_J a 1) (c := 1 / Real.pi) (d := b) (a := lo) (b := hi)
      hc hb0 hb hlo
  let R := complexDiagonal (infinitySign (ι := Option (Fin m)))
  let W : ℝ → HomogeneousInput m → HomogeneousInput m :=
    fun s z => complexCartesian.symm (V (s, complexCartesian z))
  have hW : ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => W p.1 p.2) :=
    complexCartesian.symm.contDiff.comp (hV.comp
      (contDiff_fst.prodMk (complexCartesian.contDiff.comp contDiff_snd)))
  let Y : ℝ → HomogeneousInput m → HomogeneousInput m := fun s z i =>
    match i with
    | none => (W s z none - W s (R z) none) / 2
    | some j => W s z (some j)
  have hY : ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => Y p.1 p.2) := by
    apply contDiff_pi.mpr
    intro i
    cases i with
    | none =>
      exact (((contDiff_apply ℝ ℂ none).comp hW).sub
        ((contDiff_apply ℝ ℂ none).comp (hW.comp
          (contDiff_fst.prodMk (R.contDiff.comp contDiff_snd))))).div_const 2
    | some j => exact (contDiff_apply ℝ ℂ (some j)).comp hW
  refine ⟨Y, hY, ?_, ?_⟩
  · intro s hs z hz
    have hzc : complexCartesian z ≠ 0 := phaseShell_nonzero hlo hz
    have hzK : complexCartesian z ∈ phaseShell lo hi := hz
    have hRz : phaseSq (complexCartesian (R z)) = phaseSq (complexCartesian z) := by
      rw [show complexCartesian (R z) = phaseDiagonal infinitySign (complexCartesian z) from
        (phaseDiagonal_cartesian infinitySign z).symm]
      change phaseDot (phaseDiagonal infinitySign (complexCartesian z))
        (phaseDiagonal infinitySign (complexCartesian z)) = phaseDot _ _
      rw [phaseDiagonal_dot _ infinitySign_unit]
    have hRzK : complexCartesian (R z) ∈ phaseShell lo hi := by
      change lo ≤ phaseSq (complexCartesian (R z)) ∧ phaseSq (complexCartesian (R z)) ≤ hi
      rw [hRz]
      exact hz
    have hEq := homogeneousConeField_linear_invariant (homogeneousCartesian_smooth a 1)
      (fun _ hz => homogeneousCartesian_nonzero a 1 hz) (homogeneousCartesian_euler a 1)
      (homogeneousCartesian_J a 1) (phaseUnitDiagonal infinitySign infinitySign_unit)
      (phaseDiagonal homogeneousInfinityOutputSign) (homogeneousCartesian_infinity a 1)
      (phaseDiagonal_dot _ infinitySign_unit) (phaseDiagonal_area _ infinitySign_unit)
      (phaseDiagonal_dot _ homogeneousInfinityOutputSign_unit)
      (phaseDiagonal_area _ homogeneousInfinityOutputSign_unit) hc (mul_nonneg hs.1 hb0)
      (by nlinarith [hs.2]) hzc
    have hWr : W s (R z) = R (W s z) := by
      dsimp only [W]
      rw [hVe s hs _ hRzK, hVe s hs _ hzK]
      have hh := congrArg (fun p => complexCartesian.symm p) hEq
      simpa only [phaseUnitDiagonal_apply, phaseDiagonal_cartesian,
        phaseDiagonal, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hh
    have hWz : W s z = complexCartesian.symm
        (homogeneousConeField (homogeneousCartesian a 1) (1 / Real.pi) b s (complexCartesian z)) := by
      dsimp only [W]
      rw [hVe s hs _ hzK]
    rw [← hWz]
    funext i
    cases i with
    | none =>
      change (W s z none - W s (R z) none) / 2 = W s z none
      rw [hWr]
      change (W s z none - (-1 : ℂ) * W s z none) / 2 = _
      ring
    | some j => rfl
  · intro s z hz
    have hRz : R z = z := (complexDiagonal_infinity_fixed z).mpr hz
    change (W s z none - W s (R z) none) / 2 = 0
    rw [hRz, sub_self, zero_div]


/-- Global linear growth of the affine return field. The proof normalizes with
the sup norm; its reciprocal is bounded by `1 + ‖x‖`, so no asymptotic estimate is hidden. -/
theorem returnField_linearGrowth_homogeneous (a : Fin m → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : Affine m,
      ‖returnField a b s x‖ ≤ C * (1 + ‖x‖) := by
  obtain ⟨Y, hY, hYeq, hYzero⟩ := exists_return_homogeneous_shell_extension a hb0 hb
    (lo := 1) (hi := (Fintype.card (Option (Option (Fin m))) : ℝ)) zero_lt_one
  obtain ⟨C, hC⟩ := projectedField_linearGrowth hY hYzero
  refine ⟨C, ?_⟩
  intro s hs x
  obtain ⟨_, hz, hQ, hShell⟩ := normAffineLift_properties x
  have hf := returnField_eq_homogeneous a (mul_nonneg hs.1 hb0) (by nlinarith [hs.2]) (normAffineLift x) hz
  rw [hQ, ← hYeq s hs (normAffineLift x) hShell] at hf
  rw [hf]
  exact hC s hs x

end SymplecticPacking.BranchSmall.VT
