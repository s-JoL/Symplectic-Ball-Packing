import SymplecticPacking.HighDim.Handle.ExplicitUnitBump
import SymplecticPacking.HighDim.Handle.ExplicitBoxPrimitive
import SymplecticPacking.HighDim.Handle.CanonicalChartMass

/-!
# Finite geometric data for an explicit interior primitive operator

Only coordinate boxes and a rooted finite overlap tree are supplied. Unit bumps are the
fixed formulas of `ExplicitUnitBump`; edge primitives are coordinate integrals; the global
primitive is a finite sum along the tree. No primitive is supplied as an input field.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [T2Space M]

/-- Raw finite geometry. Each non-root box has an earlier parent and an overlap box
compactly contained in both. All boxes lie in the specified open base region. -/
structure ExplicitSurfacePresentation (M : Type) [TopologicalSpace M] [ChartedSpace Plane M]
    (U : Set M) where
  size : ℕ
  boxes : Fin (size + 1) → SurfaceCoordinateBox M
  inside : ∀ i, (boxes i).compactCarrier ⊆ U
  parent : (i : Fin size) → Fin (i.val + 1)
  overlap : Fin size → SurfaceCoordinateBox M
  overlap_child : ∀ i, (overlap i).compactCarrier ⊆ (boxes i.succ).carrier
  overlap_parent : ∀ i, (overlap i).compactCarrier ⊆
    (boxes ⟨(parent i).val, by have := (parent i).isLt; have := i.isLt; omega⟩).carrier

namespace ExplicitSurfacePresentation

variable {U : Set M} (D : ExplicitSurfacePresentation M U)

end ExplicitSurfacePresentation

end SymplecticPacking.HighDim.ToricPackingStages
