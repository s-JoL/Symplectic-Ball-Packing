import SymplecticPacking.BranchLarge3.ComparisonData
import OAI.Geometry.BallPacking.Models.CubicPhysicalLocality

/-!
# Lower bound for the six-dimensional physical area

The six-dimensional physical area has a global lower bound from the explicit comparison parameters.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3

 theorem cubicComparison_physicalArea_lower {N L D S : ℕ} {r : Fin N → ℝ} {a : ℚ}
    (H : CmpHyp r a) (hL : 0<L)
    (hD : (D:ℝ)=(L:ℝ)*(2-a)) (hS : (S:ℝ)=(L:ℝ)*(1-a))
    (p : Moments 2) (hp : p∈region sixModelBounds ![((cmpData r a).h₁:ℝ),(cmpData r a).h₂]) :
    (cmpData r a).ε≤physicalArea D S (1/((L:ℝ)*Real.pi)) L p := by
  rw [physicalArea_eq_sixModelDensity hL hD hS]
  have hδ := cmpDelta_lt H
  have hm2 : cmpMargin r a≤(2*(a:ℝ)-1)/6 := (min_le_left _ _).trans (min_le_right _ _)
  have hheight : ((cmpData r a).h₂:ℝ)=(2-(a:ℝ))/3-(cmpDelta r a:ℝ) := by
    simp [cmpData]
  have hsh : 1-(a:ℝ)≤((cmpData r a).h₂:ℝ) := by
    rw [hheight]
    linarith [H.a_gt]
  have hlo := sixModelDensity_lower (s := 1-(a:ℝ)) (b := (2-(a:ℝ))/3) hsh hp
  rw [hheight] at hlo
  change 9*(cmpDelta r a:ℝ)≤_
  linarith

end SymplecticPacking.HighDim.ToricPackingStages
