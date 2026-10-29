import SymplecticPacking.BranchSmall.KahlerCalculus
import SymplecticPacking.BranchSmall.TransferPotentials

/-!
# Identification of the return potential with the explicit normal ambient form

This is an equality of the `dcForm` and `normalAmbientPrimitive` constructions,
so the existing positive-form theorem applies without an extra geometric hypothesis.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

section linearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem dcForm_add {Φ Ψ : E → ℝ} (hΦ : Differentiable ℝ Φ) (hΨ : Differentiable ℝ Ψ) :
    dcForm (fun z => Φ z + Ψ z) = dcForm Φ + dcForm Ψ := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  simp only [dcForm, fderiv_fun_add (hΦ z) (hΨ z), smul_apply,
    ContinuousLinearMap.comp_apply, add_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem dcForm_const_mul {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ) (a : ℝ) :
    dcForm (fun z => a * Φ z) = a • dcForm Φ := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  simp only [dcForm, fderiv_const_mul (hΦ z), smul_apply,
    ContinuousLinearMap.comp_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ddcForm_add {Φ Ψ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ) :
    ddcForm (fun z => Φ z + Ψ z) = ddcForm Φ + ddcForm Ψ := by
  have hdcΦ : ContDiff ℝ ∞ (dcForm Φ) := by
    unfold dcForm
    exact ((hΦ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const).const_smul _
  have hdcΨ : ContDiff ℝ ∞ (dcForm Ψ) := by
    unfold dcForm
    exact ((hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const).const_smul _
  unfold ddcForm
  rw [dcForm_add (hΦ.differentiable (by simp)) (hΨ.differentiable (by simp))]
  funext z
  exact euclideanExteriorOneForm_add (hdcΦ.differentiable (by simp) z)
    (hdcΨ.differentiable (by simp) z)

theorem ddcForm_const_mul {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (a : ℝ) :
    ddcForm (fun z => a * Φ z) = a • ddcForm Φ := by
  have hdcΦ : ContDiff ℝ ∞ (dcForm Φ) := by
    unfold dcForm
    exact ((hΦ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const).const_smul _
  unfold ddcForm
  rw [dcForm_const_mul (hΦ.differentiable (by simp))]
  funext z
  exact euclideanExteriorOneForm_smul a (hdcΦ.differentiable (by simp) z)

end linearity

variable {q : ℕ}

theorem normalPolynomial_one_sq (a : Fin q → ℂ) (z : Affine q) :
    1 + phaseSq (complexCartesian (normalPolynomial a 1 z)) =
      (1 + nsq z) ^ 2 + wsq (equations a z) := by
  have h : normalPolynomial a 1 z = joinedVeronese (affineComplex q z, equations a z) := by
    funext i
    cases i <;> simp [normalPolynomial, joinedVeronese]
  rw [h, joinedVeronese_sq, complexCartesian_affineComplex, ← nsq_eq_phaseSq, complexCartesian_sq]
  rfl

theorem returnPot_decomposition (a : Fin q → ℂ) (b s : ℝ) :
    returnPot a b s = fun z =>
      (1 - 2 * (s * b)) * Real.log (1 + nsq z) +
        (s * b) * fsPotential (normalPolynomial a 1 z) := by
  funext z
  have hpos := one_add_nsq_pos z
  have heq : 1 + wsq (equations a z) / (1 + nsq z) ^ 2 =
      ((1 + nsq z) ^ 2 + wsq (equations a z)) / (1 + nsq z) ^ 2 := by
    field_simp
  have hnonneg := wsq_nonneg (equations a z)
  have hlog : Real.log (1 + wsq (equations a z) / (1 + nsq z) ^ 2) =
      Real.log ((1 + nsq z) ^ 2 + wsq (equations a z)) - 2 * Real.log (1 + nsq z) := by
    rw [heq, Real.log_div (by positivity : (1 + nsq z) ^ 2 + wsq (equations a z) ≠ 0)
      (pow_ne_zero 2 hpos.ne'), Real.log_pow]
    norm_num
  simp only [returnPot, graphPot, fsPotential, normalPolynomial_one_sq, hlog]
  ring

theorem dcForm_normalPolynomial (a : Fin q → ℂ) :
    dcForm (fsPotential ∘ normalPolynomial a 1) =
      primitivePullback (affineFSPrimitive (1 / Real.pi))
        (fun z => complexCartesian (normalPolynomial a 1 z)) :=
  fsPotential_comp_dc ((normalPolynomial_smooth a 1).differentiable (by simp))

theorem returnPot_dc (a : Fin q → ℂ) (b s : ℝ) :
    dcForm (returnPot a b s) = normalAmbientPrimitive a (1 / Real.pi) (s * b) 1 := by
  have hfs : Differentiable ℝ (fun z : Affine q => Real.log (1 + nsq z)) :=
    ((contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne').differentiable
      (by simp)
  have hnp : Differentiable ℝ (fsPotential ∘ normalPolynomial a 1) :=
    (fsPotential_contDiff.differentiable (by simp)).comp
      (((normalPolynomial_smooth a 1).restrict_scalars ℝ).differentiable (by simp))
  rw [returnPot_decomposition]
  change dcForm (fun z => (1 - 2 * (s * b)) * Real.log (1 + nsq z) +
    (s * b) * (fsPotential ∘ normalPolynomial a 1) z) = _
  rw [dcForm_add (hfs.const_mul _) (hnp.const_mul _),
    dcForm_const_mul hfs, dcForm_const_mul hnp, dcForm_logPot, dcForm_normalPolynomial]
  rfl

theorem returnPot_ddc (a : Fin q → ℂ) (b s : ℝ) :
    ddcForm (returnPot a b s) = normalAmbientForm a (1 / Real.pi) (s * b) 1 := by
  unfold ddcForm normalAmbientForm
  rw [returnPot_dc]

end SymplecticPacking.BranchSmall.VT
