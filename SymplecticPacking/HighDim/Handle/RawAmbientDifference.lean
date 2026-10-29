import SymplecticPacking.HighDim.Handle.RawAmbientLinearity
import SymplecticPacking.HighDim.Handle.RawAmbientUnitMass

/-!
# The local zero-mass difference primitive

The explicit local zero-mass difference primitive.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

theorem formPrimitive_isPrimitive
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v, Ω x u v = -Ω x v u)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.carrier)
    (hz : ∀ x, x ∉ K → Ω x = 0) (hm : B.mass Ω = 0) :
    RawIsPrimitive B.inclusion Ω (B.formPrimitive Ω) := by
  obtain ⟨hs, hz, hp⟩ := B.formPrimitive_spec hB hsB hΩ hsk hK hKB hz hm
  exact ⟨hs, fun C hinc _ hsC z hzt => hp C hinc.symm hsC z hzt⟩

theorem difference_isPrimitive
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hΞ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ξ)
    (hsΩ : ∀ x u v, Ω x u v = -Ω x v u) (hsΞ : ∀ x u v, Ξ x u v = -Ξ x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K ⊆ B.box.carrier) (hLB : L ⊆ B.box.carrier)
    (hzΩ : ∀ x, x ∉ K → Ω x = 0) (hzΞ : ∀ x, x ∉ L → Ξ x = 0)
    (hm : B.mass Ω = B.mass Ξ) :
    RawIsPrimitive B.inclusion (Ω-Ξ) (B.formPrimitive (Ω-Ξ)) := by
  apply B.formPrimitive_isPrimitive hB hsB (hΩ.sub hΞ)
  · intro x u v
    change Ω x u v-Ξ x u v = -(Ω x v u-Ξ x v u)
    rw [hsΩ x u v, hsΞ x u v]
    ring
  · exact hK.union hL
  · exact union_subset hKB hLB
  · intro x hx
    change Ω x-Ξ x = 0
    rw [hzΩ x (fun hk => hx (Or.inl hk)), hzΞ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)-0 = 0
    ring
  · change B.mass (Ω-Ξ) = 0
    rw [B.mass_sub
      (B.coefficient_integrable hB hsB hΩ hK (fun x hx => (hKB hx).1) hzΩ)
      (B.coefficient_integrable hB hsB hΞ hL (fun x hx => (hLB hx).1) hzΞ), hm, sub_self]

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
