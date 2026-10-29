import SymplecticPacking.HighDim.Handle.RawCoordinateBox
import SymplecticPacking.HighDim.Handle.ExplicitBoxPrimitive
import SymplecticPacking.Explicit.PlaneMeasure

/-!
# Raw ambient coordinate boxes

Coordinate primitives returned as ambient covectors, independently of manifold chart encoding.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter MeasureTheory Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M]

/-- The coordinate is a fixed ambient linear projection. Smoothness of the inverse is a
separate proof property; no selected manifold chart enters this data. -/
structure RawAmbientBox (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] where
  box : RawCoordinateBox M
  inclusion : M → E
  coordinate : E →L[ℝ] Plane
  coordinate_eq : ∀ x, coordinate (inclusion x) = box.chart x

namespace RawAmbientBox
variable (B : RawAmbientBox E M)

def inverseAmbient (z : Plane) : E := B.inclusion (B.box.chart.symm z)

def frame (z : Plane) : Plane →L[ℝ] E := fderiv ℝ B.inverseAmbient z

theorem frame_rightInverse (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {z : Plane} (hz : z ∈ B.box.chart.target) :
    B.coordinate.comp (B.frame z) = ContinuousLinearMap.id ℝ Plane := by
  have hf : HasFDerivAt B.inverseAmbient (B.frame z) z :=
    ((hs z hz).contDiffAt (B.box.chart.open_target.mem_nhds hz)).differentiableAt (by simp)
      |>.hasFDerivAt
  have hcomp := B.coordinate.hasFDerivAt.comp z hf
  have he : (fun w => B.coordinate (B.inverseAmbient w)) =ᶠ[𝓝 z] id := by
    filter_upwards [B.box.chart.open_target.mem_nhds hz] with w hw
    exact (B.coordinate_eq _).trans (B.box.chart.right_inv hw)
  exact (hcomp.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id z)

/-- The displayed planar integral covector, composed with the fixed ambient projection. -/
def primitive (f : Plane → ℝ) (x : M) : E →L[ℝ] ℝ := by
  classical
  exact if x ∈ B.box.chart.source then
    (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f (B.box.chart x)).comp
      B.coordinate
  else 0

def coordinatePullback (α : M → E →L[ℝ] ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  (α (B.box.chart.symm z)).comp (B.frame z)

theorem primitive_pullback (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (f : Plane → ℝ) {z : Plane} (hz : z ∈ B.box.chart.target) :
    B.coordinatePullback (B.primitive f) z =
      formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f z := by
  unfold coordinatePullback primitive
  rw [if_pos (B.box.chart.map_target hz), B.box.chart.right_inv hz,
    ContinuousLinearMap.comp_assoc, B.frame_rightInverse hs hz]
  exact ContinuousLinearMap.comp_id _

theorem primitive_zero (f : Plane → ℝ)
    (hf : ∀ z, z ∉ Metric.closedBall B.box.point B.box.radius →
      formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f z = 0)
    {x : M} (hx : x ∉ B.box.compactCarrier) : B.primitive f x = 0 := by
  classical
  unfold primitive
  split_ifs with hs
  · have hn : B.box.chart x ∉ Metric.closedBall B.box.point B.box.radius :=
      fun hh => hx ⟨_, hh, B.box.chart.left_inv hs⟩
    rw [hf _ hn]
    exact ContinuousLinearMap.zero_comp _
  · rfl

theorem primitive_spec (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ x y, B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2| → f (x,y)=0)
    (hmass : (∫ z, f z ∂SymplecticPacking.Explicit.planeVolume) = 0) :
    (∀ x, x ∉ B.box.compactCarrier → B.primitive f x = 0) ∧
      ∀ z ∈ B.box.chart.target,
        euclideanExteriorOneForm (B.coordinatePullback (B.primitive f)) z = f z • planarArea := by
  have hp := formulaTranslatedCovectorOperator_spec (P := ℝ) B.box.radius_pos B.box.point
    (f := fun q : ℝ × Plane => f q.2) (hf.comp contDiff_snd)
    (fun _ x y hh => hzero x y hh)
    (fun _ => by simpa only [SymplecticPacking.Explicit.planeVolume_eq_volume] using hmass)
  refine ⟨?_, ?_⟩
  · intro x hx
    apply B.primitive_zero f _ hx
    intro z hz
    have hh : B.box.radius < max |z.1-B.box.point.1| |z.2-B.box.point.2| := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, Real.norm_eq_abs, not_le] using hz
    exact hp.2.1 0 z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  · intro z hz
    have he : B.coordinatePullback (B.primitive f) =ᶠ[𝓝 z]
        formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f := by
      filter_upwards [B.box.chart.open_target.mem_nhds hz] with w hw
      exact B.primitive_pullback hs f hw
    calc
      euclideanExteriorOneForm (B.coordinatePullback (B.primitive f)) z =
          euclideanExteriorOneForm
            (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f) z := by
        simp only [euclideanExteriorOneForm, he.fderiv_eq]
      _ = f z • planarArea := hp.2.2 0 z

theorem primitive_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
    (hB : B.box.Smooth) (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ x y, B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2| → f (x,y)=0)
    (hmass : (∫ z, f z ∂SymplecticPacking.Explicit.planeVolume) = 0) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ (B.primitive f) := by
  have hp := formulaTranslatedCovectorOperator_spec (P := ℝ) B.box.radius_pos B.box.point
    (f := fun q : ℝ × Plane => f q.2) (hf.comp contDiff_snd)
    (fun _ x y hh => hzero x y hh)
    (fun _ => by simpa only [SymplecticPacking.Explicit.planeVolume_eq_volume] using hmass)
  have hβ : ContDiff ℝ ∞
      (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f) :=
    covector_family_slice_smooth
      (β := fun q : ℝ × Plane =>
        formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f q.2) hp.1 0
  have hφ : ContDiff ℝ ∞ (fun z =>
      (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f z).comp B.coordinate) :=
    hβ.clm_comp contDiff_const
  have hz := (B.primitive_spec hs hf hzero hmass).1
  intro x
  by_cases hx : x ∈ B.box.chart.source
  · apply ContMDiffAt.congr_of_eventuallyEq
      (hφ.contMDiff.contMDiffAt.comp x ((hB.forward x hx).contMDiffAt
        (B.box.chart.open_source.mem_nhds hx)))
    filter_upwards [B.box.chart.open_source.mem_nhds hx] with y hy
    exact if_pos hy
  · have hxK : x ∉ B.box.compactCarrier := by
      rintro ⟨z, hz, hzx⟩
      rw [← hzx] at hx
      exact hx (B.box.chart.map_target (B.box.closed_subset hz))
    apply (contMDiffAt_const (c := (0 : E →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [B.box.compactCarrier_compact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact hz y hy

end RawAmbientBox
#check_explicit RawAmbientBox.primitive
end SymplecticPacking.HighDim.ToricPackingStages
