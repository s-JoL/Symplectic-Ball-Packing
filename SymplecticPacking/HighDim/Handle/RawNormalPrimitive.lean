import SymplecticPacking.HighDim.Handle.RawNormalization
import SymplecticPacking.HighDim.Handle.RawAnnularNormalize

/-!
# The native normalized primitive

Native normalized primitive, evaluated only from raw model fields and finite integrals.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
namespace RawToricModel
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] {m q : ℕ} (T : RawToricModel E M m q)

def normalModel (reserve : ℝ) (p : Moments m) (x : M) : E →L[ℝ] ℝ :=
  T.backgroundCoefficient reserve • T.referencePrimitive x+
    (T.handleMass reserve p*intervalClock (-T.hb) T.hb (T.handle.inverse x).1) • T.handle.dual x

def normalPrimitive (reserve : ℝ) : Moments m → M → E →L[ℝ] ℝ :=
  T.handle.normalize T.presentation.inclusion T.hb (T.redistributedPrimitive reserve) (T.normalModel reserve)

end RawToricModel
#check_explicit RawToricModel.normalPrimitive
end SymplecticPacking.HighDim
