import SymplecticPacking.HighDim.Handle.RawProductMoserSpec

/-!
# Product inclusion of a raw surface presentation

The inclusion `M × V → E × V` induced by a raw surface presentation.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M]
  {U : Set M}
namespace RawSurfacePresentation
variable (D : RawSurfacePresentation E M U)

def productInclusion (x : M × V) : E × V := (D.inclusion x.1,x.2)

def productMoserField (W : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : ℝ → V → M → E →L[ℝ] ℝ) (p : ℝ × (M × V)) : E × V := by
  classical
  exact (List.finRange (D.size+1)).foldr (fun i rest =>
    if p.2.1 ∈ (D.boxes i).box.chart.source then
      (D.boxes i).productMoserField W Γ p.1 p.2 else rest) 0

def cutProductMoserField (W : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : ℝ → V → M → E →L[ℝ] ℝ) (χ : ℝ × (M × V) → ℝ)
    (p : ℝ × (M × V)) : E × V := χ p • D.productMoserField W Γ p

section manifold
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

def productMoserFlow (W : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : ℝ → V → M → E →L[ℝ] ℝ) (χ : ℝ × (M × V) → ℝ)
    (t : ℝ) (x : M × V) : M × V :=
  ambientFieldFlow (K := Plane × V) D.productInclusion (D.cutProductMoserField W Γ χ) t x

end manifold
end RawSurfacePresentation
#check_explicit RawSurfacePresentation.productInclusion
#check_explicit RawSurfacePresentation.productMoserField
#check_explicit RawSurfacePresentation.cutProductMoserField
#check_explicit RawSurfacePresentation.productMoserFlow
end SymplecticPacking.HighDim.ToricPackingStages
