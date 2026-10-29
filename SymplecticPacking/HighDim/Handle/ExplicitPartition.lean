import SymplecticPacking.HighDim.Handle.SurfacePresentation

/-!
# A smooth plateau function on an interval

The plateau function `plateauLine A`, equal to one on `[-A/2, A/2]` and zero for `A ≤ |x|`.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

/-- A plateau function, one on the half interval and zero off the full interval. -/
def plateauLine (A x : ℝ) : ℝ :=
  Real.smoothTransition (2 * (x + A) / A) * Real.smoothTransition (2 * (A - x) / A)

theorem plateauLine_smooth (A : ℝ) : ContDiff ℝ ∞ (plateauLine A) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.add contDiff_const)).div_const A)).mul
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const A))

theorem plateauLine_nonneg (A x : ℝ) : 0 ≤ plateauLine A x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateauLine_zero {A : ℝ} (hA : 0 < A) (x : ℝ) (hx : A ≤ |x|) :
    plateauLine A x = 0 := by
  unfold plateauLine
  rcases le_or_gt x 0 with h | h
  · rw [abs_of_nonpos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (x := 2*(x+A)/A)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le), zero_mul]
  · rw [abs_of_pos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (x := 2*(A-x)/A)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le), mul_zero]

theorem plateauLine_one {A : ℝ} (hA : 0 < A) (x : ℝ) (hx : |x| ≤ A/2) :
    plateauLine A x = 1 := by
  have hb := abs_le.mp hx
  unfold plateauLine
  rw [Real.smoothTransition.one_of_one_le (x := 2*(x+A)/A)
    ((one_le_div hA).2 (by linarith)),
    Real.smoothTransition.one_of_one_le (x := 2*(A-x)/A)
    ((one_le_div hA).2 (by linarith)), mul_one]

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [T2Space M]

namespace ExplicitSurfacePresentation
variable {U : Set M} (D : ExplicitSurfacePresentation M U)

end ExplicitSurfacePresentation

end SymplecticPacking.HighDim.ToricPackingStages
