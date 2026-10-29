import SymplecticPacking.BranchSmall.Params
import OAI.Geometry.BallPacking.Models.EqualNormalModelConvergence
import SymplecticPacking.Explicit

/-!
# Background scale of the quadric normalization

A numerical background scale for the quadric normalisation.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

/-- The pointwise background coefficient uses the explicit degree area bound and an
explicit density floor. It does not evaluate a selected atlas integral or an existential gap. -/
def quadricBackgroundCoefficient (q : ℕ) (reserve height : ℝ) : ℝ :=
  min (reserve/(32*(2:ℝ)^q)) ((1-2*height)/2)

theorem quadricBackgroundCoefficient_pos {q : ℕ} {reserve height : ℝ}
    (hr : 0 < reserve) (hh : height < 1/2) :
    0 < quadricBackgroundCoefficient q reserve height := by
  apply lt_min
  · exact div_pos hr (by positivity)
  · linarith

theorem quadricBackgroundCoefficient_budget {q : ℕ} {reserve height A : ℝ}
    (hr : 0 < reserve) (hh : height < 1/2) (hA : A ≤ (2:ℝ)^q) :
    quadricBackgroundCoefficient q reserve height*A ≤ reserve/32 := by
  have hc := quadricBackgroundCoefficient_pos (q := q) hr hh
  calc
    quadricBackgroundCoefficient q reserve height*A ≤
        quadricBackgroundCoefficient q reserve height*(2:ℝ)^q := mul_le_mul_of_nonneg_left hA hc.le
    _ ≤ (reserve/(32*(2:ℝ)^q))*(2:ℝ)^q :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    _ = reserve/32 := by field_simp

/-- The small-ball model uses this scalar at its integer degree and explicit gap. -/
def smallQuadricBackgroundCoefficient {k : ℕ} (m : ℕ) (ρ : Fin k → ℝ) : ℝ :=
  quadricBackgroundCoefficient (m+2) (11*SymplecticPacking.BranchSmall.dgap (m+3) ρ/64)
    (SymplecticPacking.BranchSmall.hgt (m+3) ρ)

/-- Once the fixed cutoff area is evaluated by the raw finite integral, this is the
handle mass formula for an equal-normal quadric family. -/
def quadricHandleMassRaw (q : ℕ) (reserve height cutoffArea : ℝ) (p : Fin q → ℝ) : ℝ :=
  (equalNormalCoefficient q 2 p-quadricBackgroundCoefficient q reserve height)*cutoffArea

#check_explicit quadricBackgroundCoefficient
#check_explicit smallQuadricBackgroundCoefficient
#check_explicit quadricHandleMassRaw
end SymplecticPacking.HighDim.ToricPackingStages
