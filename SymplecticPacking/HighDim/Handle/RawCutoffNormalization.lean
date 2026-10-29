import SymplecticPacking.HighDim.Handle.RawCalibratedCorrection
import SymplecticPacking.HighDim.Handle.RawManifoldBridge

/-!
# Cutoff redistribution of physical curvature

Cutoff redistribution for spatially varying physical curvature as well as scalar families.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]

def rawCutoffRemoved (χ : M → ℝ) (c : ℝ)
    (Λ : M → E →L[ℝ] E →L[ℝ] ℝ) (Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ)
    (p : P) (x : M) : E →L[ℝ] E →L[ℝ] ℝ := χ x • (Ω p x-c • Λ x)

variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem rawCutoffRemoved_smooth
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ χ) (c : ℝ)
    {Λ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΛ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Λ)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2)) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => rawCutoffRemoved χ c Λ Ω q.1 q.2) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hc : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (fun _ : P × M => c) := contMDiff_const
  exact (hχ.comp contMDiff_snd).smul (hΩ.sub (hc.smul (hΛ.comp contMDiff_snd)))

theorem rawCutoffRemoved_zero {χ : M → ℝ} (c : ℝ)
    (Λ : M → E →L[ℝ] E →L[ℝ] ℝ) (Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ)
    {x : M} (hx : χ x=0) (p : P) : rawCutoffRemoved χ c Λ Ω p x=0 := by
  unfold rawCutoffRemoved
  rw [hx]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact zero_mul _

theorem cutoff_background_positive {χ κ c : ℝ}
    (hχ0 : 0≤χ) (hχ1 : χ≤1) (hκ : 0<κ) (hc : 0<c) :
    0 < κ-χ*(κ-c) := by
  rcases le_total κ c with h|h
  · have hm := mul_nonneg hχ0 (sub_nonneg.mpr h)
    nlinarith
  · have hm := mul_nonneg (sub_nonneg.mpr hχ1) (sub_nonneg.mpr h)
    nlinarith

#check_explicit rawCutoffRemoved
end SymplecticPacking.HighDim.ToricPackingStages
