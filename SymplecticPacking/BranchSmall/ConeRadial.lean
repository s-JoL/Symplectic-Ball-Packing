import SymplecticPacking.BranchSmall.BundlePotential

/-!
# Radial contraction in the explicit normal cone

This identity identifies horizontal graph transport, for positive graph parameter,
with a scalar multiple of the scaled exact Moser field.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

section leibniz
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exterior_fun_smul {f : E → ℝ} {α : E → E →L[ℝ] ℝ} {p : E}
    (hf : DifferentiableAt ℝ f p) (hα : DifferentiableAt ℝ α p) (u v : E) :
    euclideanExteriorOneForm (fun y => f y • α y) p u v =
      f p * euclideanExteriorOneForm α p u v +
        fderiv ℝ f p u * α p v - fderiv ℝ f p v * α p u := by
  rw [euclideanExteriorOneForm, (hf.hasFDerivAt.fun_smul hα.hasFDerivAt).fderiv]
  simp only [sub_apply, flip_apply, add_apply, smul_apply, smulRight_apply, smul_eq_mul,
    euclideanExteriorOneForm]
  ring
end leibniz

section cone
variable {ι κ : Type} [Fintype ι] [Fintype κ]
local notation "E" => PlanePhase ι × PlanePhase κ

theorem conePrimitive_radial_contraction (c d : ℝ) (p k : E) :
    euclideanExteriorOneForm (conePrimitive c d) p ((0 : PlanePhase ι), p.2) k =
      (2 * (1 + phaseSq p.1) ^ 2 / coneDenominator p) *
        (conePrimitive c d p k - affineFSPrimitive c p.1 k.1) := by
  let F : E →L[ℝ] PlanePhase ι := ContinuousLinearMap.fst ℝ _ _
  let S : E →L[ℝ] PlanePhase κ := ContinuousLinearMap.snd ℝ _ _
  let B : E →L[ℝ] E →L[ℝ] ℝ := phaseArea.bilinearComp F F
  let V : E →L[ℝ] E →L[ℝ] ℝ := phaseArea.bilinearComp S S
  let A : E → E →L[ℝ] ℝ := fun y => (2 * (1 + phaseSq y.1)) • B y + V y
  let D : E → ℝ := fun y => coneDenominator y
  let f : E → ℝ := fun y => (c * d / 2) * (D y)⁻¹
  let β : E → E →L[ℝ] ℝ := primitivePullback (affineFSPrimitive c) F
  let R : E := (0, p.2)
  have hD : ContDiff ℝ ∞ D :=
    ((contDiff_const.add (phaseSq_smooth.comp contDiff_fst)).pow 2).add
      (phaseSq_smooth.comp contDiff_snd)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const (c := c * d / 2)).mul (hD.inv (fun y => (coneDenominator_pos y).ne'))
  have hA : ContDiff ℝ ∞ A :=
    ((contDiff_const.mul (contDiff_const.add (phaseSq_smooth.comp contDiff_fst))).smul B.contDiff).add V.contDiff
  have hβ : ContDiff ℝ ∞ β := primitivePullback_smooth (affineFSPrimitive_smooth c) F.contDiff
  have he : conePrimitive c d = (1 - 2 * d) • β + fun y => f y • A y := by
    funext y
    apply ContinuousLinearMap.ext
    intro w
    simp only [conePrimitive_apply, Pi.add_apply, add_apply, Pi.smul_apply, smul_apply,
      smul_eq_mul, β, primitivePullback, F.fderiv, fderiv_fst, ContinuousLinearMap.comp_apply,
      A, B, V, ContinuousLinearMap.bilinearComp_apply, F, S, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply, f, D]
    ring
  have hβR : euclideanExteriorOneForm β p R k = 0 := by
    have hh := primitivePullback_exterior (affineFSPrimitive_smooth c) F.contDiff p
    rw [F.fderiv] at hh
    have hv := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L R k) hh
    change euclideanExteriorOneForm β p R k = _ at hv
    rw [hv]
    change euclideanExteriorOneForm (affineFSPrimitive c) p.1 0 k.1 = 0
    rw [map_zero, zero_apply]
  have hAR : A p R = 0 := by
    change 2 * (1 + phaseSq p.1) * phaseArea p.1 0 + phaseArea p.2 p.2 = 0
    simp only [map_zero, mul_zero, phaseArea_self, add_zero]
  have hDA (u w : E) : fderiv ℝ A p u w =
      4 * phaseDot p.1 u.1 * phaseArea p.1 w.1 +
        2 * (1 + phaseSq p.1) * phaseArea u.1 w.1 + phaseArea u.2 w.2 := by
    have hb := ((phaseSq_hasFDerivAt p.1).comp p F.hasFDerivAt).const_add 1
    have hh := ((hb.const_mul 2).fun_smul B.hasFDerivAt).add V.hasFDerivAt
    change HasFDerivAt A _ p at hh
    rw [hh.fderiv]
    simp only [add_apply, smul_apply, smulRight_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, B, V, ContinuousLinearMap.bilinearComp_apply, F, S, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply]
    ring
  have hdAR : euclideanExteriorOneForm A p R k = 2 * phaseArea p.2 k.2 := by
    change fderiv ℝ A p R k - fderiv ℝ A p k R = _
    rw [hDA, hDA]
    change _ = 2 * phaseArea p.2 k.2
    simp only [R, map_zero, zero_apply, mul_zero, zero_add, add_zero]
    rw [phaseArea_skew k.2 p.2]
    ring
  have hdf : fderiv ℝ f p R = -c * d * phaseSq p.2 / (coneDenominator p) ^ 2 := by
    have hb := ((phaseSq_hasFDerivAt p.1).comp p F.hasFDerivAt).const_add 1
    have hv := (phaseSq_hasFDerivAt p.2).comp p S.hasFDerivAt
    have hd := (hb.pow 2).add hv
    change HasFDerivAt D _ p at hd
    have hh := ((hasFDerivAt_inv' (𝕜 := ℝ) (coneDenominator_pos p).ne').comp p hd).const_mul (c * d / 2)
    change HasFDerivAt f _ p at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, smul_eq_mul,
      neg_apply, ContinuousLinearMap.mulLeftRight_apply, F, S, R, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply,
      map_zero, mul_zero, zero_add, D]
    simp only [phaseSq]
    field_simp
  have hcβ : DifferentiableAt ℝ ((1 - 2 * d) • β) p :=
    (hβ.differentiable (by simp) p).const_smul _
  have hfa : DifferentiableAt ℝ (fun y => f y • A y) p :=
    (hf.differentiable (by simp) p).smul (hA.differentiable (by simp) p)
  have hadd := euclideanExteriorOneForm_add (α := (1 - 2 * d) • β)
    (β := fun y => f y • A y) hcβ hfa
  rw [he, hadd, euclideanExteriorOneForm_smul _ (hβ.differentiable (by simp) p)]
  change ((1 - 2 * d) * euclideanExteriorOneForm β p R k +
    euclideanExteriorOneForm (fun y => f y • A y) p R k) = _
  rw [hβR, mul_zero, zero_add, exterior_fun_smul (hf.differentiable (by simp) p)
    (hA.differentiable (by simp) p), hAR, mul_zero, sub_zero, hdAR, hdf]
  rw [← he]
  simp only [f, D, conePrimitive_apply, affineFSPrimitive, smul_apply, smul_eq_mul]
  change (c * d / 2 * (coneDenominator p)⁻¹) * (2 * phaseArea p.2 k.2) +
    (-c * d * phaseSq p.2 / coneDenominator p ^ 2) *
      (2 * (1 + phaseSq p.1) * phaseArea p.1 k.1 + phaseArea p.2 k.2) = _
  field_simp [(coneDenominator_pos p).ne', (fs_den_pos p.1).ne']
  simp only [coneDenominator]
  ring

end cone
end SymplecticPacking.BranchSmall.VT
