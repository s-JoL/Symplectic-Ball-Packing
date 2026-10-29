import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.Forms.Basic

/-!
# Kähler potential calculus for the vector normal transfer

Holomorphic naturality of `ddcForm` and positivity of the affine Fubini--Study potential.
These lemmas use the derivative-based forms in `VectorTransfer.lean`.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

section naturality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem dcForm_comp_holomorphic {g : E → F} {Φ : F → ℝ}
    (hg : Differentiable ℂ g) (hΦ : Differentiable ℝ Φ) :
    SymplecticPacking.Forms.pull1 g (dcForm Φ) = dcForm (Φ ∘ g) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hgR : DifferentiableAt ℝ g x := (hg x).restrictScalars ℝ
  have hJ : fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := by
    rw [(hg x).fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  simp only [SymplecticPacking.Forms.pull1_apply, dcForm,
    smul_apply, ContinuousLinearMap.comp_apply, cxJ_apply, smul_eq_mul,
    fderiv_comp x (hΦ _) hgR, hJ]

theorem ddcForm_comp_holomorphic {g : E → F} {Φ : F → ℝ}
    (hg : Differentiable ℂ g) (hg2 : ContDiff ℝ ∞ g) (hΦ : ContDiff ℝ ∞ Φ)
    (x v w : E) :
    ddcForm (Φ ∘ g) x v w =
      ddcForm Φ (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hD : DifferentiableAt ℝ (dcForm Φ) (g x) := by
    have hd := hΦ.fderiv_right (m := ∞) (by simp)
    exact ((hd.clm_comp contDiff_const).const_smul (-(1 / (4 * Real.pi)))).differentiable
      (by simp) _
  have h := SymplecticPacking.Forms.pull2_d1_apply (x := x)
    (hg2.contDiffAt.of_le (by simp)) hD
  rw [dcForm_comp_holomorphic hg (hΦ.differentiable (by simp))] at h
  have h' := congrArg (fun L => L v w) h
  simpa only [SymplecticPacking.Forms.pull2_apply, ddcForm,
    euclideanExteriorOneForm, SymplecticPacking.Forms.d1] using h'

end naturality

section affine

variable {ι : Type*} [Fintype ι]

def fsPotential (z : ι → ℂ) : ℝ := Real.log (1 + phaseSq (complexCartesian z))

theorem fsPotential_contDiff : ContDiff ℝ ∞ (fsPotential (ι := ι)) :=
  (contDiff_const.add (phaseSq_smooth.comp (complexCartesian (ι := ι)).contDiff)).log fun z =>
    (fs_den_pos (complexCartesian z)).ne'

theorem fsPotential_dc (z v : ι → ℂ) :
    dcForm fsPotential z v =
      affineFSPrimitive (1 / Real.pi) (complexCartesian z) (complexCartesian v) := by
  have h1 : HasFDerivAt (fun z : ι → ℂ => phaseSq (complexCartesian z))
      (((2 : ℝ) • phaseDot (complexCartesian z)).comp complexCartesian.toContinuousLinearMap) z :=
    (phaseSq_hasFDerivAt (complexCartesian z)).comp z
      (complexCartesian (ι := ι)).toContinuousLinearMap.hasFDerivAt
  have h2 := (h1.const_add 1).log (fs_den_pos (complexCartesian z)).ne'
  change HasFDerivAt (fsPotential (ι := ι)) _ z at h2
  simp only [dcForm, smul_apply, ContinuousLinearMap.comp_apply,
    cxJ_apply, smul_eq_mul, h2.fderiv, complexCartesian_I, phaseDot_J_right,
    affineFSPrimitive, ContinuousLinearEquiv.coe_coe, complexCartesian_I, phaseDot_J_right]
  field_simp
  ring

theorem fsPotential_comp_dc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : E → (ι → ℂ)}
    (hg : Differentiable ℂ g) :
    dcForm (fsPotential ∘ g) =
      primitivePullback (affineFSPrimitive (1 / Real.pi)) (fun z => complexCartesian (g z)) := by
  rw [← dcForm_comp_holomorphic hg (fsPotential_contDiff.differentiable (by simp))]
  funext z
  apply ContinuousLinearMap.ext
  intro v
  rw [SymplecticPacking.Forms.pull1_apply, fsPotential_dc]
  have hd := (complexCartesian (ι := ι)).toContinuousLinearMap.hasFDerivAt.comp z
    (((hg z).restrictScalars ℝ).hasFDerivAt)
  change HasFDerivAt (fun z => complexCartesian (g z)) _ z at hd
  rw [primitivePullback, hd.fderiv]
  rfl

theorem fsPotential_ddc (z v w : ι → ℂ) :
    ddcForm fsPotential z v w =
      affineFSForm (1 / Real.pi) (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
  have hdc : dcForm (fsPotential (ι := ι)) =
      SymplecticPacking.Forms.pull1 complexCartesian (affineFSPrimitive (1 / Real.pi)) := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    rw [fsPotential_dc]
    change _ = affineFSPrimitive _ _ (fderiv ℝ (complexCartesian (ι := ι)) z v)
    rw [(complexCartesian (ι := ι)).hasFDerivAt.fderiv]
    rfl
  have h := SymplecticPacking.Forms.pull2_d1_apply (x := z)
    ((complexCartesian (ι := ι)).contDiff.contDiffAt.of_le (by decide : (2 : ℕ∞) ≤ ∞))
    ((affineFSPrimitive_smooth (1 / Real.pi)).differentiable (by simp) (complexCartesian z))
  rw [← hdc] at h
  have h' := congrArg (fun L => L v w) h
  change ddcForm fsPotential z v w = _
  change ddcForm fsPotential z v w = _ at h'
  rw [h']
  simp only [SymplecticPacking.Forms.pull2_apply,
    ContinuousLinearEquiv.fderiv, ContinuousLinearEquiv.coe_coe]
  exact affineFSPrimitive_exterior _ _ _ _

theorem fsPotential_ddc_pos (z v : ι → ℂ) (hv : v ≠ 0) :
    0 < ddcForm fsPotential z v (Complex.I • v) := by
  rw [fsPotential_ddc, complexCartesian_I]
  exact affineFSForm_positive (one_div_pos.mpr Real.pi_pos) _ _
    (fun h => hv (complexCartesian.injective (h.trans (map_zero _).symm)))

end affine

end SymplecticPacking.BranchSmall.VT
