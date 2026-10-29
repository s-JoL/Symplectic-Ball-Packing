import SymplecticPacking.HighDim.Polytope
import SymplecticPacking.HighDim.Handle.RawCalibratedCorrection
import OAI.Geometry.BallPacking.Annuli.AnnularChartNormalization

/-!
# Raw toric model data

Primitive input data for the native three-stage construction.
The ambient normed space is an explicit parameter. No semantic tensor or selected
manifold chart is a field of either record.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope

structure RawAnnularHandle (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] where
  width : ℝ
  source : Set HandleCylinder
  target : Set M
  forward : HandleCylinder → M
  inverse : M → HandleCylinder
  ambientCover : Plane → E
  coordinate : E →L[ℝ] Plane
  dual : M → E →L[ℝ] ℝ
  radial : ℝ → M → E →L[ℝ] ℝ
  clock : Circle → ℝ

structure RawToricModel (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (m q : ℕ) where
  polytope : Polytope m q
  base : Set M
  correctionCore : Set M
  presentation : ToricPackingStages.RawSurfacePresentation E M (interior base)
  physicalPrimitive : Moments m → M → E →L[ℝ] ℝ
  physicalForm : Moments m → M → E →L[ℝ] E →L[ℝ] ℝ
  referencePrimitive : M → E →L[ℝ] ℝ
  referenceForm : M → E →L[ℝ] E →L[ℝ] ℝ
  referenceAreaBound : ℝ
  densityFloor : ℝ
  handle : RawAnnularHandle E M
  cutoff : M → ℝ
  hb : ℝ
  hδ : ℝ

end SymplecticPacking.HighDim
