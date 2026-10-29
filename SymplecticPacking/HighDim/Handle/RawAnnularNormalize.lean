import SymplecticPacking.HighDim.Handle.RawToricModel
import SymplecticPacking.HighDim.Handle.QuadricRawAnnular

/-!
# The native annular normalization formula

The native annular normalization formula on raw handle data.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function
open ToricPackingStages
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
namespace RawAnnularHandle
variable {E M P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [NormedAddCommGroup P] [NormedSpace ℝ P]
  (H : RawAnnularHandle E M)

def normalizeCoverPoint (q : Plane) : M := H.forward (cylinderCover q)

def normalizeCoverCovector (δ : P → M → E →L[ℝ] ℝ) (p : P) (q : Plane) : Plane →L[ℝ] ℝ :=
  (δ p (H.normalizeCoverPoint q)).comp (fderiv ℝ H.ambientCover q)

def normalizeCoverA (δ : P → M → E →L[ℝ] ℝ) (q : P × Plane) : ℝ := H.normalizeCoverCovector δ q.1 q.2 (1,0)
def normalizeCoverB (δ : P → M → E →L[ℝ] ℝ) (q : P × Plane) : ℝ := H.normalizeCoverCovector δ q.1 q.2 (0,1)
def period (δ : P → M → E →L[ℝ] ℝ) : P → ℝ := annularMean 0 (H.normalizeCoverB δ)

def potential (δ : P → M → E →L[ℝ] ℝ) (p : P) (z : HandleCylinder) : ℝ :=
  annularCylinderScalar (normalizedAnnularPrimitive 0 (H.normalizeCoverA δ) (H.normalizeCoverB δ)
    (H.clock ∘ circleTurn)) p z

def cutWidth (b : ℝ) : ℝ := (b+H.width)/2

def coordinateGauge (b : ℝ) (δ : P → M → E →L[ℝ] ℝ) (p : P) (z : Plane) : ℝ :=
  let w := cylinderComplexInverse (Complex.equivRealProdCLM.symm z)
  intervalPlateau (H.cutWidth b) (H.cutWidth (H.cutWidth b)) w.1 * H.potential δ p w

def gaugeCovector (ι : M → E) (b : ℝ) (δ : P → M → E →L[ℝ] ℝ) (p : P) (x : M) : E →L[ℝ] ℝ := by
  classical
  exact if x∈H.target then
    (fderiv ℝ (H.coordinateGauge b δ p) (H.coordinate (ι x))).comp H.coordinate
  else 0

def normalize (ι : M → E) (b : ℝ) (Γ N : P → M → E →L[ℝ] ℝ) (p : P) (x : M) : E →L[ℝ] ℝ :=
  Γ p x-H.period (Γ-N) p • H.dual x-H.gaugeCovector ι b (Γ-N) p x

end RawAnnularHandle
end SymplecticPacking.HighDim
