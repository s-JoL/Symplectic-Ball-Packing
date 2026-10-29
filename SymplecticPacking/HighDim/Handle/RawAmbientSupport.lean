import SymplecticPacking.HighDim.Handle.RawAmbientDifference

/-!
# Compact support of raw box primitives

Compact support of the displayed box primitives.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

theorem formPrimitive_zero
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.carrier)
    (hz : ∀ x, x ∉ K → Ω x = 0) (hm : B.mass Ω = 0)
    (x : M) (hx : x ∉ B.box.compactCarrier) : B.formPrimitive Ω x = 0 :=
  (B.primitive_spec hsB
    (B.coefficient_smooth hB hsB hΩ hK (fun x hx => (hKB hx).1) hz)
    (B.coefficient_face_zero hKB hz) hm).1 x hx

theorem difference_zero
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hΞ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ξ)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K ⊆ B.box.carrier) (hLB : L ⊆ B.box.carrier)
    (hzΩ : ∀ x, x ∉ K → Ω x = 0) (hzΞ : ∀ x, x ∉ L → Ξ x = 0)
    (hm : B.mass Ω = B.mass Ξ) (x : M) (hx : x ∉ B.box.compactCarrier) :
    B.formPrimitive (Ω-Ξ) x = 0 := by
  apply B.formPrimitive_zero hB hsB (hΩ.sub hΞ) (hK.union hL) (union_subset hKB hLB) _ _ x hx
  · intro x hx
    change Ω x-Ξ x = 0
    rw [hzΩ x (fun hk => hx (Or.inl hk)), hzΞ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)-0=0
    ring
  · change B.mass (Ω-Ξ) = 0
    rw [B.mass_sub
      (B.coefficient_integrable hB hsB hΩ hK (fun x hx => (hKB hx).1) hzΩ)
      (B.coefficient_integrable hB hsB hΞ hL (fun x hx => (hLB hx).1) hzΞ), hm, sub_self]

theorem difference_data
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hΞ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ξ)
    (hsΩ : ∀ x u v, Ω x u v = -Ω x v u) (hsΞ : ∀ x u v, Ξ x u v = -Ξ x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K ⊆ B.box.carrier) (hLB : L ⊆ B.box.carrier)
    (hzΩ : ∀ x, x ∉ K → Ω x = 0) (hzΞ : ∀ x, x ∉ L → Ξ x = 0)
    (hm : B.mass Ω = B.mass Ξ) :
    RawIsPrimitive B.inclusion (Ω-Ξ) (B.formPrimitive (Ω-Ξ)) ∧
      ∀ x, x ∉ B.box.compactCarrier → B.formPrimitive (Ω-Ξ) x = 0 :=
  ⟨B.difference_isPrimitive hB hsB hΩ hΞ hsΩ hsΞ hK hL hKB hLB hzΩ hzΞ hm,
    B.difference_zero hB hsB hΩ hΞ hK hL hKB hLB hzΩ hzΞ hm⟩

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
