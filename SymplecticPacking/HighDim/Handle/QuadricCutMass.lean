import SymplecticPacking.HighDim.Handle.RawSurfaceMass
import SymplecticPacking.HighDim.Handle.QuadricBackgroundScale
import SymplecticPacking.HighDim.Handle.QuadricBoundaryCutoff
import SymplecticPacking.HighDim.Handle.QuadricCollarBounds
import SymplecticPacking.BranchSmall.QuadricRawForms

/-!
# Cutoff forms and handle mass for the quadric

Raw Fubini--Study cutoff forms and the finite-integral handle mass.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

/-- Compact core area form, in ambient covectors, with the radial collar cutoff. -/
def quadricCutFSForm {m : ℕ} (a : Fin m → ℂ) (A B : ℝ) (x : locus a) :
    Affine m →L[ℝ] Affine m →L[ℝ] ℝ :=
  (1-quadricBoundaryCutoff A B x) •
    SymplecticPacking.BranchSmall.RawQuadric.ambientFSForm (1/Real.pi) x.val

def quadricRemovedFSForm {m q : ℕ} (a : Fin m → ℂ) (reserve height A B : ℝ)
    (p : Fin q → ℝ) : locus a → Affine m →L[ℝ] Affine m →L[ℝ] ℝ :=
  (equalNormalCoefficient q 2 p-quadricBackgroundCoefficient m reserve height) • quadricCutFSForm a A B

namespace RawSurfacePresentation
variable {m : ℕ} {a : Fin m → ℂ} {U : Set (locus a)}
  (D : RawSurfacePresentation (Affine m) (locus a) U)

def quadricRemovedHandleMass {q : ℕ} (reserve height A B : ℝ) (p : Fin q → ℝ) : ℝ :=
  D.calibratedMass (quadricRemovedFSForm a reserve height A B p)

end RawSurfacePresentation

section Smooth
variable {m q : ℕ} (a : Fin m → ℂ)
  [Fact (Injective a)] [Fact (∀ j,a j≠0)]

namespace RawSurfacePresentation
variable {a} {U : Set (locus a)} (D : RawSurfacePresentation (Affine m) (locus a) U)

end RawSurfacePresentation
end Smooth

#check_explicit quadricCutFSForm
#check_explicit quadricRemovedFSForm
#check_explicit RawSurfacePresentation.quadricRemovedHandleMass
end SymplecticPacking.HighDim.ToricPackingStages
