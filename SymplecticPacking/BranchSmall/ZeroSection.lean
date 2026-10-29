import SymplecticPacking.BranchSmall.ReturnPotential

/-!
# The vector transfer fixes the zero section

The horizontal field vanishes at zero normal coordinate. The return covector
vanishes on the complete intersection, so the Moser field vanishes there too.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics

section generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem flowI_stationary {V : ℝ → E → E} (t₀ t : ℝ) (y : E)
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, V s y = 0) : flowI V t₀ y t = y := by
  classical
  have hconst : IsSolI V t₀ y (fun _ => y) := by
    refine ⟨rfl, fun _ => rfl, fun s hs => ?_⟩
    rw [hy s hs]
    exact hasDerivWithinAt_const _ _ _
  unfold flowI
  split_ifs with hu
  · exact congrFun (SymplecticPacking.Explicit.the_eq hu hconst) t
  · rfl
end generic

variable {q : ℕ}

@[simp] theorem radialInj_zero (b : ℝ) (z : Affine q) : radialInj b z 0 = (z, 0) := by
  exact Prod.ext rfl (funext fun j => by simp [radialInj])

@[simp] theorem toC_zero : toC (0 : PlanePhase (Fin q)) = 0 := by
  ext j <;> rfl

theorem transportField_zero_normal (a : Fin q → ℂ) (b T : ℝ) (z : Affine q) :
    transportField a b T (z, 0) = 0 := by
  classical
  unfold transportField
  split_ifs with hu
  · apply hu.unique (SymplecticPacking.Explicit.the_spec hu)
    constructor
    · simp only [Prod.fst_zero, Prod.snd_zero, map_zero, smul_zero, sub_self]
    · intro k _
      simp only [map_zero, zero_apply]
  · rfl

theorem graphPot_hasFDerivAt_zero (a : Fin q → ℂ) (z : Affine q)
    (hz : equations a z = 0) : HasFDerivAt (graphPot a) (0 : Affine q →L[ℝ] ℝ) z := by
  have hE := (complexCartesian (ι := Fin q)).toContinuousLinearMap.hasFDerivAt.comp z
    ((equations_hasFDerivAt a z).restrictScalars ℝ)
  have hW := (phaseSq_hasFDerivAt (complexCartesian (equations a z))).comp z hE
  have hW0 : HasFDerivAt (fun z => wsq (equations a z)) (0 : Affine q →L[ℝ] ℝ) z := by
    simpa only [hz, map_zero, phaseDot.map_zero, zero_smul, smul_zero, zero_comp, complexCartesian_sq, wsq,
      Function.comp_def, ContinuousLinearEquiv.coe_coe] using hW
  have hN := (((contDiff_const (c := (1 : ℝ))).add nsq_contDiff').pow 2).differentiable (by simp) z |>.hasFDerivAt
  have hNI := hN.differentiableAt.inv (pow_ne_zero 2 (one_add_nsq_pos z).ne')
  have hQ := hW0.fun_mul hNI.hasFDerivAt
  have hQ0 : HasFDerivAt (fun z => wsq (equations a z) / (1 + nsq z) ^ 2) (0 : Affine q →L[ℝ] ℝ) z := by
    simpa only [hz, wsq, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero,
      zero_smul, sub_zero, zero_div, smul_zero, add_zero, div_eq_mul_inv, Pi.inv_apply] using hQ
  have hL := (hQ0.const_add 1).log (by
    simp only [hz, wsq, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero,
      zero_div, add_zero, ne_eq, one_ne_zero, not_false_eq_true])
  change HasFDerivAt (graphPot a) _ z at hL
  simpa only [hz, wsq, Pi.zero_apply, Complex.normSq_zero,
    Finset.sum_const_zero, zero_div, add_zero, smul_zero] using hL

theorem graphPot_dc_zero (a : Fin q → ℂ) (z : Affine q) (hz : equations a z = 0) :
    dcForm (graphPot a) z = 0 := by
  simp only [dcForm, (graphPot_hasFDerivAt_zero a z hz).fderiv, zero_comp, smul_zero]

theorem returnField_zero_locus (a : Fin q → ℂ) (b s : ℝ) (z : Affine q)
    (hz : equations a z = 0) : returnField a b s z = 0 := by
  classical
  unfold returnField
  split_ifs with hu
  · apply hu.unique (SymplecticPacking.Explicit.the_spec hu)
    intro v
    simp only [map_zero, zero_apply, graphPot_dc_zero a z hz, mul_zero]
  · rfl

theorem transport_zero_normal (a : Fin q → ℂ) (b : ℝ) (z : Affine q) :
    transport a b (z, 0) = (z, 0) :=
  flowI_stationary 0 1 (z, 0) fun s _ => transportField_zero_normal a b s z

theorem returnInv_zero_locus (a : Fin q → ℂ) (b : ℝ) (z : Affine q)
    (hz : equations a z = 0) : returnInv a b z = z :=
  flowI_stationary 1 0 z fun s _ => returnField_zero_locus a b s z hz

end SymplecticPacking.BranchSmall.VT
