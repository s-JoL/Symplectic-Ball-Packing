import SymplecticPacking.BranchSmall.HomogeneousFamily
import SymplecticPacking.BranchSmall.ProjectedGrowth

/-!
# Uniform bounds for the scaled normal Moser fields
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {m : ℕ}
theorem exists_scaled_homogeneous_shell_extension (a : Fin m → ℂ) {T : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) {b lo hi : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (hlo : 0 < lo) :
    ∃ Y : ℝ → HomogeneousInput m → HomogeneousInput m,
      ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => Y p.1 p.2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexCartesian z ∈ phaseShell lo hi →
        Y s z = complexCartesian.symm (homogeneousConeField (homogeneousCartesian a (T s))
          (1 / Real.pi) b 1 (complexCartesian z))) ∧
      (∀ s z, z none = 0 → Y s z none = 0) := by
  have hc : 0 < 1 / Real.pi := one_div_pos.mpr Real.pi_pos
  let H : ℝ × PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))) :=
    fun p => homogeneousConeField (homogeneousCartesian a (T p.1)) (1 / Real.pi) b 1 p.2
  let U : Set (ℝ × PlanePhase (Option (Option (Fin m)))) := univ ×ˢ {z | z ≠ 0}
  let K : Set (ℝ × PlanePhase (Option (Option (Fin m)))) := Icc 0 1 ×ˢ phaseShell lo hi
  have hU : IsOpen U := isOpen_univ.prod isOpen_ne
  have hK : IsCompact K := isCompact_Icc.prod (phaseShell_isCompact lo hi)
  have hKU : K ⊆ U := fun p hp => ⟨mem_univ _, phaseShell_nonzero hlo hp.2⟩
  have hH : ContDiffOn ℝ ∞ H U := homogeneousConeField_parameter_contDiffOn a hT hT0 hc hb0 hb
  obtain ⟨χ, _, _, _, _, _, hV, _, hVe0⟩ := exists_smooth_compact_extension hK hU hKU hH
  let V : ℝ × PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))) := fun p => χ p • H p
  have hV : ContDiff ℝ ∞ V := hV
  have hVe (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z) (hz : z ∈ phaseShell lo hi) :
      V (s, z) = homogeneousConeField (homogeneousCartesian a (T s)) (1 / Real.pi) b 1 z :=
    by
      have hp : (s, z) ∈ K := ⟨hs, hz⟩
      exact (hVe0.filter_mono (nhds_le_nhdsSet hp)).self_of_nhds
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
    have hEq := homogeneousConeField_linear_invariant (s := 1) (d := b)
      (homogeneousCartesian_smooth a (T s))
      (fun _ hz => homogeneousCartesian_nonzero a (T s) hz) (homogeneousCartesian_euler a (T s))
      (homogeneousCartesian_J a (T s)) (phaseUnitDiagonal infinitySign infinitySign_unit)
      (phaseDiagonal homogeneousInfinityOutputSign) (homogeneousCartesian_infinity a (T s))
      (phaseDiagonal_dot _ infinitySign_unit) (phaseDiagonal_area _ infinitySign_unit)
      (phaseDiagonal_dot _ homogeneousInfinityOutputSign_unit)
      (phaseDiagonal_area _ homogeneousInfinityOutputSign_unit) hc (by simpa only [one_mul] using hb0)
      (by simpa only [one_mul] using hb) hzc
    have hWr : W s (R z) = R (W s z) := by
      dsimp only [W]
      rw [hVe s hs _ hRzK, hVe s hs _ hzK]
      have hh := congrArg (fun p => complexCartesian.symm p) hEq
      simpa only [phaseUnitDiagonal_apply, phaseDiagonal_cartesian,
        phaseDiagonal, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hh
    have hWz : W s z = complexCartesian.symm
        (homogeneousConeField (homogeneousCartesian a (T s)) (1 / Real.pi) b 1 (complexCartesian z)) := by
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




theorem normalReturnField_parameter_contDiff (a : Fin m → ℂ) {T : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine m => normalReturnField a b (T p.1) p.2) := by
  have hLam := normalAmbientPrimitive_parameter_contDiff a hT hT0 (1 / Real.pi) b
  have hLam0 := normalAmbientPrimitive_parameter_contDiff a hT hT0 (1 / Real.pi) 0
  have hΩ := spatialExterior_contDiffOn (E := Affine m) (U := univ)
    (α := fun s => normalAmbientPrimitive a (1 / Real.pi) b (T s)) isOpen_univ hLam.contDiffOn
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hi := normalAmbientForm_isInvertible a (one_div_pos.mpr Real.pi_pos) hb0 hb (T p.1) p.2
  have hΩp := hΩ.contDiffAt (x := p) (by simp)
  have hinv := hi.contDiffAt_map_inverse.comp p hΩp
  simpa only [normalReturnField, normalAmbientForm, Function.comp_apply, ContinuousLinearMap.neg_apply] using
    (hinv.clm_apply (hLam.sub hLam0).contDiffAt).neg


theorem normalReturnField_parameter_linearGrowth (a : Fin m → ℂ) {T : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : Affine m,
      ‖normalReturnField a b (T s) x‖ ≤ C * (1 + ‖x‖) := by
  obtain ⟨Y, hY, hYeq, hYzero⟩ := exists_scaled_homogeneous_shell_extension a hT hT0 hb0 hb
    (lo := 1) (hi := (Fintype.card (Option (Option (Fin m))) : ℝ)) zero_lt_one
  obtain ⟨C, hC⟩ := projectedField_linearGrowth hY hYzero
  refine ⟨C, ?_⟩
  intro s hs x
  obtain ⟨_, hz, hQ, hShell⟩ := normAffineLift_properties x
  have hf := normalReturnField_eq_homogeneous a (T s) hb0 hb (normAffineLift x) hz
  rw [hQ, ← hYeq s hs (normAffineLift x) hShell] at hf
  rw [hf]
  exact hC s hs x

end SymplecticPacking.BranchSmall.VT
