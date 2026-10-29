import SymplecticPacking.HighDim.Handle.RawCutoffNormalization

/-!
# Mass budget of the raw cutoff form

The common mass budget for scalar and spatially varying physical curvature.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {U : Set M} (D : RawSurfacePresentation E M U)

def rawCutoffForm (χ : M → ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] E →L[ℝ] ℝ :=
  fun x => χ x • Ω x

theorem rawCutoffRemoved_decomposition (χ : M → ℝ) (c : ℝ)
    (Λ : M → E →L[ℝ] E →L[ℝ] ℝ) (Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ) (p : P) :
    rawCutoffRemoved χ c Λ Ω p=rawCutoffForm χ (Ω p)-c • rawCutoffForm χ Λ := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change χ x*(Ω p x u v-c*Λ x u v)=χ x*Ω p x u v-c*(χ x*Λ x u v)
  ring

theorem rawCutoffForm_zero (χ : M → ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ)
    {x : M} (hx : χ x=0) : rawCutoffForm χ Ω x=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change χ x*Ω x u v=0
  rw [hx,zero_mul]

theorem calibrated_removed_mass (hG : D.Geometry)
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ χ) (c : ℝ)
    {Λ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΛ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Λ)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ} (p : P)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (Ω p))
    {K : Set M} (hK : IsCompact K) (hz : ∀ x,x∉K → χ x=0) :
    D.calibratedMass (rawCutoffRemoved χ c Λ Ω p)=
      D.calibratedMass (rawCutoffForm χ (Ω p))-c*D.calibratedMass (rawCutoffForm χ Λ) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hIΩ := D.weightedCoefficient_integrable hG (hχ.smul hΩ) hK
    (fun x hx => rawCutoffForm_zero χ (Ω p) (hz x hx))
  have hIΛ := D.weightedCoefficient_integrable hG (hχ.smul hΛ) hK
    (fun x hx => rawCutoffForm_zero χ Λ (hz x hx))
  have hcI (i) : Integrable ((D.boxes i).coefficient (D.weightedForm (c • rawCutoffForm χ Λ) i)) := by
    rw [D.weightedForm_smul,(D.boxes i).coefficient_smul]
    exact (hIΛ i).const_mul c
  rw [rawCutoffRemoved_decomposition,D.calibratedMass_sub (Ω := rawCutoffForm χ (Ω p)) (Ξ := c • rawCutoffForm χ Λ) hIΩ hcI,D.calibratedMass_smul]

theorem handleMass_loss_budget {H physicalCut referenceCut outer inner c reserve : ℝ}
    (hH : H=physicalCut-c*referenceCut) (hcut : inner≤physicalCut)
    (htail : outer-inner≤reserve/32) (hbg : c*referenceCut≤reserve/32) :
    outer-reserve/16≤H := by linarith

end SymplecticPacking.HighDim.ToricPackingStages
