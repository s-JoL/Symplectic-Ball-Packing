import SymplecticPacking.HighDim.Handle.RawSurfaceFamily

/-!
# The explicit finite surface integral

The explicit finite integral used to calculate the removed area and handle mass.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M]
namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)

def formMass (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : ℝ := ∑ i, D.weightedMass Ω i

/-- The fixed raw root bump calibrates the finite integral against the intrinsic area. -/
def massCalibration : ℝ := D.formMass (D.boxes D.root).unitBump

def calibratedMass (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : ℝ := D.formMass Ω/D.massCalibration

theorem weightedForm_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (i : Fin (D.size+1)) :
    D.weightedForm (a • Ω) i = a • D.weightedForm Ω i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change D.partitionWeight i x*(a*Ω x u v) = a*(D.partitionWeight i x*Ω x u v)
  ring

theorem weightedForm_sub (Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ) (i : Fin (D.size+1)) :
    D.weightedForm (Ω-Ξ) i = D.weightedForm Ω i-D.weightedForm Ξ i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change D.partitionWeight i x*(Ω x u v-Ξ x u v) =
    D.partitionWeight i x*Ω x u v-D.partitionWeight i x*Ξ x u v
  ring

theorem weightedMass_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (i : Fin (D.size+1)) :
    D.weightedMass (a • Ω) i = a*D.weightedMass Ω i := by
  unfold weightedMass
  rw [D.weightedForm_smul,RawAmbientBox.mass_smul]

theorem formMass_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) :
    D.formMass (a • Ω) = a*D.formMass Ω := by
  unfold formMass
  simp_rw [D.weightedMass_smul]
  rw [Finset.mul_sum]

theorem calibratedMass_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) :
    D.calibratedMass (a • Ω) = a*D.calibratedMass Ω := by
  unfold calibratedMass
  rw [D.formMass_smul]
  ring

theorem formMass_sub {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ∀ i, Integrable ((D.boxes i).coefficient (D.weightedForm Ω i)))
    (hΞ : ∀ i, Integrable ((D.boxes i).coefficient (D.weightedForm Ξ i))) :
    D.formMass (Ω-Ξ) = D.formMass Ω-D.formMass Ξ := by
  unfold formMass weightedMass
  simp_rw [D.weightedForm_sub]
  have hs (i : Fin (D.size+1)) := (D.boxes i).mass_sub (hΩ i) (hΞ i)
  simp_rw [hs]
  rw [Finset.sum_sub_distrib]


theorem calibratedMass_sub {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ∀ i,Integrable ((D.boxes i).coefficient (D.weightedForm Ω i)))
    (hΞ : ∀ i,Integrable ((D.boxes i).coefficient (D.weightedForm Ξ i))) :
    D.calibratedMass (Ω-Ξ)=D.calibratedMass Ω-D.calibratedMass Ξ := by
  unfold calibratedMass
  rw [D.formMass_sub hΩ hΞ]
  ring

variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem weightedCoefficient_integrable (hG : D.Geometry)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    {K : Set M} (hK : IsCompact K) (hz : ∀ x, x ∉ K → Ω x = 0)
    (i : Fin (D.size+1)) : Integrable ((D.boxes i).coefficient (D.weightedForm Ω i)) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hρ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (D.partitionWeight i) :=
    RawBoxFamily.partitionWeight_smooth (fun j => (D.boxes j).box) hG.box_smooth i
  exact (D.boxes i).coefficient_integrable (hG.box_smooth i) (hG.box_inverse i)
    (hρ.smul hΩ) (hK.inter_right (isClosed_tsupport _))
    (fun x hx => (D.partitionWeight_support i hx.2).1)
    (fun x hx => D.weightedForm_zero (P := ℝ) (fun _ => hz) 0 i x hx)

theorem formMass_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (hG : D.Geometry)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hzΩ : ∀ p x, x ∉ K → Ω p x=0) :
    ContDiff ℝ ∞ (fun p => D.formMass (Ω p)) :=
  ContDiff.sum (fun i _ => D.weightedMass_family_smooth hG hΩ hK hzΩ i)

theorem calibratedMass_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (hG : D.Geometry)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hzΩ : ∀ p x, x ∉ K → Ω p x=0) :
    ContDiff ℝ ∞ (fun p => D.calibratedMass (Ω p)) :=
  (D.formMass_family_smooth hG hΩ hK hzΩ).div_const _

end RawSurfacePresentation
#check_explicit RawSurfacePresentation.formMass
#check_explicit RawSurfacePresentation.calibratedMass
end SymplecticPacking.HighDim.ToricPackingStages
