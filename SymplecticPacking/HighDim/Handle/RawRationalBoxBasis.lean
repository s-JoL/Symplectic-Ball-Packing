import SymplecticPacking.HighDim.Handle.RawCoordinateBox

/-!
# Rational points of the plane

The embedding of `ℚ × ℚ` in the plane and the density of its range.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped Topology

def rationalPlane (q : ℚ × ℚ) : Plane := ((q.1:ℝ), (q.2:ℝ))

theorem rationalPlane_dense : DenseRange rationalPlane :=
  Rat.denseRange_cast.prodMap Rat.denseRange_cast

#check_explicit rationalPlane
end SymplecticPacking.HighDim.ToricPackingStages
