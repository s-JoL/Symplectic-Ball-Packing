import SymplecticPacking.BranchLarge3.ExactSafety
import SymplecticPacking.BranchLarge3.ExactFibreCore

/-!
# A compact flow enclosure

A compact flow enclosure from finite scalar derivative bounds.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.ExactSafety
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] {n : ℕ}

/-- The known complete flow is supplied before its safety time is evaluated. The compact
enclosure is its image of the displayed closed strip; `Good` is only the conclusion. -/
theorem good_of_flow {Γ : ℝ → ManifoldOneForm E M} {K U : Set M} {δ : ℝ}
    {A : ℝ × M → N} {T : Set N} (hK : IsCompact K)
    (f : Fin n → ℝ × M → ℝ) (Ψ : ℝ × M → M)
    (hΨ : ContinuousOn Ψ (Icc (-1) 1 ×ˢ K))
    (hΨ0 : ∀ x∈K,Ψ (0,x)=x)
    (h0 : ∀ i,ContinuousOn (fun x => f i (0,x)) K)
    (hd : ∀ i,ContinuousOn (fun p : ℝ × M => deriv (fun s => f i (s,p.2)) p.1)
      (Icc (-1) 1 ×ˢ K))
    (hder : ∀ i,∀ x∈K,∀ s∈Icc (-1) 1,DifferentiableAt ℝ (fun r => f i (r,x)) s)
    (hpos : ∀ i,∀ x∈K,0<f i (0,x)) (hδ : 0<δ)
    (hreg : ∀ s∈Icc (-1) 1,∀ x∈K,(∀ i,0<f i (s,x)) →
      (s,Ψ (s,x))∈ExactCore.region Γ U A T)
    (hODE : ∀ s∈Icc (-1) 1,∀ x∈K,(∀ i,0<f i (s,x)) →
      HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun r => Ψ (r,x)) s
        (((1:ℝ →L[ℝ] ℝ).smulRight (ExactCore.mfield Γ (s,Ψ (s,x)))) : ℝ →L[ℝ] E)) :
    ExactCore.Good Γ K U δ A T (time f K δ) := by
  let τ := time f K δ
  have hτ : 0<τ := time_pos (clearance_pos hK h0 hpos) (speed_pos hK hd) hδ
  have hb := time_bounds f K δ
  have hsub : Icc (-τ) (2*τ) ×ˢ K ⊆ Icc (-1) 1 ×ˢ K := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    exact ⟨⟨by linarith [hb.2.1,hs.1],by linarith [hb.2.1,hs.2]⟩,hx⟩
  have hpositive {s : ℝ} (hs : s∈Icc (-τ) (2*τ)) {x : M} (hx : x∈K) :
      ∀ i,0<f i (s,x) := by
    intro i
    have hsabs : |s|≤2*time f K δ := by
      rw [abs_le]
      exact ⟨by linarith [hs.1],hs.2⟩
    have hh := guard_ge_half hK h0 hd hder hpos hδ i hx hsabs
    linarith [clearance_pos hK h0 hpos]
  let C := (fun p : ℝ × M => (p.1,Ψ p)) '' (Icc (-τ) (2*τ) ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image_of_continuousOn
    (continuousOn_fst.prodMk (hΨ.mono hsub))
  have hCR : C ⊆ ExactCore.region Γ U A T := by
    rintro _ ⟨⟨s,x⟩,hsx,rfl⟩
    exact hreg s (hsub hsx).1 x hsx.2 (hpositive hsx.1 hsx.2)
  refine ⟨⟨hτ.le,le_min (by linarith [hb.1]) (by linarith [hb.2.1])⟩,
    C,hC,hCR,τ/2,by positivity,by linarith [hb.2.1],?_⟩
  intro x hx
  refine ⟨fun s => Ψ (s,x),hΨ0 x hx,?_⟩
  intro s hs
  have hsI : s∈Icc (-τ) (2*τ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  exact ⟨⟨(s,x),⟨hsI,hx⟩,rfl⟩,
    hODE s (hsub (show (s,x)∈Icc (-τ) (2*τ) ×ˢ K from ⟨hsI,hx⟩)).1 x hx (hpositive hsI hx)⟩

end SymplecticPacking.BranchLarge3.ExactSafety
