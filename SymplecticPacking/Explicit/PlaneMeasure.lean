import SymplecticPacking.Explicit

/-!
# Planar Lebesgue measure

Intrinsic, unique planar Lebesgue measure for explicit coordinate integrals.
-/

noncomputable section
namespace SymplecticPacking.Explicit

open MeasureTheory Set

/-- Rectangle normalization determines planar Lebesgue measure uniquely. It refers
only to the two one-dimensional Lebesgue measures, never to a selected planar measure. -/
def PlaneRectangleSpec (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
    μ (s ×ˢ t) = (volume : Measure ℝ) s * (volume : Measure ℝ) t

theorem existsUnique_planeRectangleSpec : ∃! μ, PlaneRectangleSpec μ := by
  refine ⟨(volume : Measure (ℝ × ℝ)), ?_, ?_⟩
  · intro s t hs ht
    exact Measure.prod_prod s t
  · intro μ hμ
    exact (Measure.prod_eq hμ).symm

/-- The unique rectangle-normalized measure. Existence is used only in the proof of
the unique specification; the definition selects no arbitrary map representative. -/
def planeVolume : Measure (ℝ × ℝ) := the existsUnique_planeRectangleSpec

theorem planeVolume_spec : PlaneRectangleSpec planeVolume :=
  the_spec existsUnique_planeRectangleSpec

theorem planeVolume_eq_volume : planeVolume = (volume : Measure (ℝ × ℝ)) :=
  the_eq existsUnique_planeRectangleSpec (by
    intro s t hs ht
    exact Measure.prod_prod s t)

#check_explicit planeVolume

end SymplecticPacking.Explicit
