import SymplecticPacking.HighDim.Handle.RawProductFlow

/-!
# Full ambient covectors and their Moser field

Full ambient covectors, including arbitrary vertical and mixed components.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport.Hamiltonian
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

def fullCovector (α : M × V → (E × V) →L[ℝ] ℝ) (y : Plane × V) :
    (Plane × V) →L[ℝ] ℝ :=
  (α (B.box.chart.symm y.1,y.2)).comp
    ((B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V))

def fullForm (α : M × V → (E × V) →L[ℝ] ℝ) (y : Plane × V) :
    (Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ :=
  euclideanExteriorOneForm (B.fullCovector α) y

def fullTimePrimitive (α : ℝ → M × V → (E × V) →L[ℝ] ℝ) (t : ℝ) (y : Plane × V) :
    (Plane × V) →L[ℝ] ℝ := deriv (fun s => B.fullCovector (α s) y) t

def fullMoserField (α : ℝ → M × V → (E × V) →L[ℝ] ℝ) (t : ℝ) (x : M × V) : E × V :=
  let y := (B.box.chart x.1,x.2)
  ((B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V))
    (rawLinearMoser (B.fullForm (α t) y) (B.fullTimePrimitive α t y))

end RawAmbientBox
#check_explicit RawAmbientBox.fullCovector
#check_explicit RawAmbientBox.fullForm
#check_explicit RawAmbientBox.fullTimePrimitive
#check_explicit RawAmbientBox.fullMoserField
end SymplecticPacking.HighDim.ToricPackingStages
