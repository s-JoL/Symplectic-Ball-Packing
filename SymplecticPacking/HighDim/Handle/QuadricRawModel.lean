import SymplecticPacking.HighDim.Handle.RawNormalization
import SymplecticPacking.HighDim.Handle.QuadricModelPresentation
import SymplecticPacking.HighDim.Handle.QuadricRawDensity
import SymplecticPacking.HighDim.Handle.QuadricBoundaryCutoff
import SymplecticPacking.BranchSmall.QuadricRawForms

/-!
# Raw toric models of the scalar quadric families

Raw toric inputs for scalar-curvature quadric families.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope

def quadricRawHandle (m : ℕ) : RawAnnularHandle (Affine (m+2)) (Surface m) where
  width := 1/8
  source := Ioo (-1/8) (1/8) ×ˢ univ
  target := {x | QuadricRawDensity.nativeSheet m x.val}
  forward z := transverseAnnulusInverse m (cylinderComplexMap z)
  inverse x := cylinderComplexInverse (transverseCoordinate m x.val)
  ambientCover := QuadricRawDual.transverseCover m
  coordinate := QuadricRawDual.transverseProjection m
  dual x := QuadricRawDual.actualDual m x.val
  radial b x := QuadricRawDensity.radial m b x.val
  clock := positiveCircleClock (1/4)

/-- The small and mixed families use this same finite affine construction. The supplied
scalar density is the coefficient of their physical FS primitive. -/
def quadricScalarRawModel (m n q ℓ : ℕ) (Δ : Polytope n q)
    (κ : Moments n → ℝ) (floor : ℝ) : RawToricModel (Affine (m+2)) (Surface m) n q where
  polytope := Δ
  base := projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)
  correctionCore := projectionDomain (parameters m) ((quadricFiniteSupportRadius m ℓ:ℝ))
  presentation := quadricModelRawPresentation m ℓ
  physicalPrimitive p x := SymplecticPacking.BranchSmall.RawQuadric.scaledPrimitive (1/Real.pi) κ p x.val
  physicalForm p x := SymplecticPacking.BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val
  referencePrimitive x := ambientFSPrimitive (1/Real.pi) x.val
  referenceForm x := SymplecticPacking.BranchSmall.RawQuadric.ambientFSForm (1/Real.pi) x.val
  referenceAreaBound := (2:ℝ)^(m+2)
  densityFloor := floor
  handle := quadricRawHandle m
  cutoff x := 1-quadricBoundaryCutoff
    (exhaustionRadius (parameters m) ℓ-2) (exhaustionRadius (parameters m) ℓ-1) x
  hb := 1/16
  hδ := 1/4

#check_explicit quadricRawHandle
#check_explicit quadricScalarRawModel
end SymplecticPacking.HighDim.ToricPackingStages
