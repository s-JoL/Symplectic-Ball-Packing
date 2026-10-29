import SymplecticPacking.HighDim.Handle.RawToricModel
import SymplecticPacking.HighDim.Handle.RawCutoffNormalization

/-!
# The native normalization formula

The native normalization is a formula on the raw model data.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
namespace RawToricModel
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] {m q : ℕ} (T : RawToricModel E M m q)

def backgroundCoefficient (reserve : ℝ) : ℝ :=
  min (reserve/(32*T.referenceAreaBound)) (T.densityFloor/2)

def handleDensity (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (T.handle.radial T.hb x).smulRight (T.handle.dual x)-
    (T.handle.dual x).smulRight (T.handle.radial T.hb x)

def removedForm (reserve : ℝ) (p : Moments m) : M → E →L[ℝ] E →L[ℝ] ℝ :=
  ToricPackingStages.rawCutoffRemoved T.cutoff (T.backgroundCoefficient reserve) T.referenceForm T.physicalForm p

def handleMass (reserve : ℝ) (p : Moments m) : ℝ :=
  T.presentation.calibratedMass (T.removedForm reserve p)

def correction (reserve : ℝ) (p : Moments m) : M → E →L[ℝ] ℝ :=
  T.presentation.calibratedCorrection T.handleDensity (T.removedForm reserve p)

def redistributedPrimitive (reserve : ℝ) (p : Moments m) : M → E →L[ℝ] ℝ :=
  T.physicalPrimitive p+T.correction reserve p

theorem backgroundCoefficient_pos {reserve : ℝ} (hr : 0<reserve)
    (hA : 0<T.referenceAreaBound) (hf : 0<T.densityFloor) :
    0<T.backgroundCoefficient reserve :=
  lt_min (div_pos hr (mul_pos (by norm_num) hA)) (half_pos hf)

open ToricPackingStages
open scoped ContDiff Manifold Topology
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

end RawToricModel
#check_explicit RawToricModel.handleMass
#check_explicit RawToricModel.redistributedPrimitive
end SymplecticPacking.HighDim
