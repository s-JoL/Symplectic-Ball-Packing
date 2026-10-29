import SymplecticPacking.Explicit.PlaneMeasure
import SymplecticPacking.HighDim.Handle.ExplicitLineBump

/-!
# Chart mass for the normalized planar measure

Coordinate integrals with the uniquely rectangle-normalized planar measure.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def formulaChartMass (c : M) (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∫ y, extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y) ∂SymplecticPacking.Explicit.planeVolume

#check_explicit formulaChartMass
end SymplecticPacking.HighDim.ToricPackingStages
