import SymplecticPacking.HighDim.Handle.RawSurfaceMass

/-!
# Calibrated area redistribution on raw data

Area redistribution computed from the calibrated raw finite integral and the intrinsic unit handle density.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M]
namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)

def calibratedDefect (η Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] E →L[ℝ] ℝ :=
  D.calibratedMass Ω • η-Ω

def calibratedCorrection (η Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] ℝ :=
  D.primitiveOperator (D.calibratedDefect η Ω)

def calibratedPrimitive (Γ : M → E →L[ℝ] ℝ)
    (η Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] ℝ :=
  Γ+D.calibratedCorrection η Ω

variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem calibratedCorrection_spec (hG : D.Geometry)
    {η Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hη : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ η)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsη : ∀ x u v, η x u v = -η x v u) (hsΩ : ∀ x u v, Ω x u v = -Ω x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hzη : ∀ x, x ∉ K → η x = 0) (hzΩ : ∀ x, x ∉ L → Ω x = 0)
    (hcover : K ∪ L ⊆ ⋃ i, (D.boxes i).box.inner)
    (hunit : D.formMass η = D.massCalibration) (hcal : D.massCalibration≠0) :
    RawIsPrimitive D.inclusion (D.calibratedDefect η Ω) (D.calibratedCorrection η Ω) ∧
      (∀ x, x ∉ D.support → D.calibratedCorrection η Ω x=0) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hc : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun _ : M => D.calibratedMass Ω) := contMDiff_const
  have hdef : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (D.calibratedDefect η Ω) :=
    (hc.smul hη).sub hΩ
  apply D.primitiveOperator_data hG (hK.union hL) hcover hdef
  · intro x u v
    change D.calibratedMass Ω*η x u v-Ω x u v = -(D.calibratedMass Ω*η x v u-Ω x v u)
    rw [hsη x u v,hsΩ x u v]
    ring
  · intro x hx
    change D.calibratedMass Ω • η x-Ω x=0
    rw [hzη x (fun hk => hx (Or.inl hk)),hzΩ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change D.calibratedMass Ω*0-(0:ℝ)=0
    ring
  · change D.formMass (D.calibratedMass Ω • η-Ω)=0
    have hηI (i) : Integrable ((D.boxes i).coefficient (D.weightedForm (D.calibratedMass Ω • η) i)) := by
      rw [D.weightedForm_smul,(D.boxes i).coefficient_smul]
      exact (D.weightedCoefficient_integrable hG hη hK hzη i).const_mul _
    rw [D.formMass_sub hηI (D.weightedCoefficient_integrable hG hΩ hL hzΩ),
      D.formMass_smul,hunit]
    unfold calibratedMass
    rw [div_mul_cancel₀ _ hcal,sub_self]

theorem calibratedPrimitive_spec (hG : D.Geometry)
    {Γ : M → E →L[ℝ] ℝ} {Ξ η Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΓ : RawIsPrimitive D.inclusion Ξ Γ)
    (hη : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ η)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsη : ∀ x u v, η x u v = -η x v u) (hsΩ : ∀ x u v, Ω x u v = -Ω x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hzη : ∀ x, x ∉ K → η x = 0) (hzΩ : ∀ x, x ∉ L → Ω x = 0)
    (hcover : K ∪ L ⊆ ⋃ i, (D.boxes i).box.inner) (hunit : D.formMass η=D.massCalibration) (hcal : D.massCalibration≠0) :
    RawIsPrimitive D.inclusion (Ξ+D.calibratedDefect η Ω) (D.calibratedPrimitive Γ η Ω) :=
  hΓ.add (D.calibratedCorrection_spec hG hη hΩ hsη hsΩ hK hL hzη hzΩ hcover hunit hcal).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem calibratedCorrection_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (hG : D.Geometry)
    {η : M → E →L[ℝ] E →L[ℝ] ℝ} {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hη : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ η)
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hzη : ∀ x, x∉K → η x=0) (hzΩ : ∀ p x, x∉L → Ω p x=0) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => D.calibratedCorrection η (Ω q.1) q.2) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hH := D.calibratedMass_family_smooth hG hΩ hL hzΩ
  have hHprod : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => D.calibratedMass (Ω q.1)) := hH.contMDiff.comp contMDiff_fst
  have hηprod : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => η q.2) := hη.comp contMDiff_snd
  have hF : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => D.calibratedDefect η (Ω q.1) q.2) :=
    (hHprod.smul hηprod).sub hΩ
  change ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
    (fun q : P × M => D.primitiveOperator (D.calibratedDefect η (Ω q.1)) q.2)
  apply D.primitiveOperator_family_smooth (Ω := fun p => D.calibratedDefect η (Ω p)) hG hF (hK.union hL)
  ·
    intro p x hx
    change D.calibratedMass (Ω p) • η x-Ω p x=0
    rw [hzη x (fun h => hx (Or.inl h)),hzΩ p x (fun h => hx (Or.inr h))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change D.calibratedMass (Ω p)*0-(0:ℝ)=0
    ring

end RawSurfacePresentation
#check_explicit RawSurfacePresentation.calibratedCorrection
#check_explicit RawSurfacePresentation.calibratedPrimitive
end SymplecticPacking.HighDim.ToricPackingStages
