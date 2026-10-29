import OAI.Geometry.BallPacking.SurfaceArea.SurfacePrimitiveOperator

/-!
# A normalized one-dimensional bump

A fixed one-dimensional flat bump, normalized by its positive integral.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory
open scoped ContDiff Topology

/-- Two explicit transition functions. -/
def lineBumpRaw (A x : ℝ) : ℝ :=
  Real.smoothTransition ((x + A) / A) * Real.smoothTransition ((A - x) / A)

theorem lineBumpRaw_smooth (A : ℝ) : ContDiff ℝ ∞ (lineBumpRaw A) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const A)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const A))

theorem lineBumpRaw_nonneg (A x : ℝ) : 0 ≤ lineBumpRaw A x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem lineBumpRaw_zero {A : ℝ} (hA : 0 < A) (x : ℝ) (hx : A ≤ |x|) :
    lineBumpRaw A x = 0 := by
  unfold lineBumpRaw
  rcases le_or_gt x 0 with h | h
  · rw [abs_of_nonpos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (x := (x+A)/A)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le), zero_mul]
  · rw [abs_of_pos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (x := (A-x)/A)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le), mul_zero]

theorem lineBumpRaw_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (lineBumpRaw A) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) A)
  intro x hx
  exact lineBumpRaw_zero hA x (le_of_lt (by simpa only [Metric.mem_closedBall,
    dist_zero_right, Real.norm_eq_abs, not_le] using hx))

theorem lineBumpRaw_mass_pos {A : ℝ} (hA : 0 < A) : 0 < ∫ x, lineBumpRaw A x := by
  apply (lineBumpRaw_smooth A).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (lineBumpRaw_compact hA) (lineBumpRaw_nonneg A) (x := 0)
  simp [lineBumpRaw, hA.ne', Real.smoothTransition.one]

/-- The normalized bump used in every coordinate primitive. -/
def formulaLineBump (A : ℝ) (x : ℝ) : ℝ := lineBumpRaw A x / ∫ y, lineBumpRaw A y

theorem formulaLineBump_spec {A : ℝ} (hA : 0 < A) :
    ContDiff ℝ ∞ (formulaLineBump A) ∧ (∀ x, 0 ≤ formulaLineBump A x) ∧
      HasCompactSupport (formulaLineBump A) ∧
      (∀ x, A ≤ |x| → formulaLineBump A x = 0) ∧
      (∫ x, formulaLineBump A x) = 1 := by
  have hz (x : ℝ) (hx : A ≤ |x|) : formulaLineBump A x = 0 := by
    rw [formulaLineBump, lineBumpRaw_zero hA x hx, zero_div]
  refine ⟨(lineBumpRaw_smooth A).div_const _,
    fun x => div_nonneg (lineBumpRaw_nonneg A x) (lineBumpRaw_mass_pos hA).le, ?_, hz, ?_⟩
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) A)
    intro x hx
    exact hz x (le_of_lt (by simpa only [Metric.mem_closedBall,
      dist_zero_right, Real.norm_eq_abs, not_le] using hx))
  · simp only [formulaLineBump, div_eq_mul_inv]
    rw [integral_mul_const, mul_inv_cancel₀ (lineBumpRaw_mass_pos hA).ne']

end SymplecticPacking.HighDim.ToricPackingStages
