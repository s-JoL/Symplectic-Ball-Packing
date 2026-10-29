import SymplecticPacking.HighDim.Handle.ExplicitLineBump

/-!
# Explicit unit bumps on coordinate boxes

`planarUnitBump`, the product of two normalized one-dimensional bumps: a smooth, compactly
supported, nonnegative function on the plane with integral one.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

/-- Product of two fixed normalized one-dimensional flat bumps. -/
def planarUnitBump (A : ℝ) (hA : 0 < A) (z : Plane) : ℝ :=
  formulaLineBump A z.1 * formulaLineBump A z.2

theorem planarUnitBump_spec (A : ℝ) (hA : 0 < A) :
    ContDiff ℝ ∞ (planarUnitBump A hA) ∧
      (∀ z, 0 ≤ planarUnitBump A hA z) ∧ HasCompactSupport (planarUnitBump A hA) ∧
      (∀ x y, A ≤ |x| ∨ A ≤ |y| → planarUnitBump A hA (x, y) = 0) ∧
      (∫ z, planarUnitBump A hA z) = 1 := by
  let r := formulaLineBump A
  obtain ⟨hrs, hrnonneg, hrc, hr0, hrmass⟩ := formulaLineBump_spec hA
  have hs : ContDiff ℝ ∞ (planarUnitBump A hA) :=
    (hrs.comp contDiff_fst).mul (hrs.comp contDiff_snd)
  have hz (x y : ℝ) (hxy : A ≤ |x| ∨ A ≤ |y|) : planarUnitBump A hA (x, y) = 0 := by
    rcases hxy with hx | hy
    · exact mul_eq_zero_of_left (hr0 x hx) _
    · exact mul_eq_zero_of_right _ (hr0 y hy)
  have hc : HasCompactSupport (planarUnitBump A hA) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) A)
    intro z hn
    have hh : A < max |z.1| |z.2| := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, not_le] using hn
    exact hz z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨hs, fun z => mul_nonneg (hrnonneg _) (hrnonneg _), hc, hz, ?_⟩
  have hi := integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (planarUnitBump A hA) (hs.continuous.integrable_of_hasCompactSupport hc)
  rw [Measure.volume_eq_prod ℝ ℝ, hi]
  change (∫ x, ∫ y, r x * r y) = 1
  simp_rw [integral_const_mul]
  rw [show (∫ y, r y) = 1 from hrmass]
  simp only [mul_one]
  exact hrmass

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [T2Space M]

end SymplecticPacking.HighDim.ToricPackingStages
