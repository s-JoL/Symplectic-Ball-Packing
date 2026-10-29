import SymplecticPacking.HighDim.Handle.RawAmbientMass
import OAI.Geometry.BallPacking.Normal.MovingPrimitiveNaturality

/-!
# Raw coordinate primitives in compatible charts

A coordinate integral gives a primitive in every compatible raw chart.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B C : RawAmbientBox E M)

theorem primitive_pullback_transition (hinc : B.inclusion = C.inclusion)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    (f : Plane → ℝ) {z : Plane}
    (hz : z ∈ (C.box.chart.symm.trans B.box.chart).source) :
    C.coordinatePullback (B.primitive f) z = primitivePullback
      (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point f)
      (B.transition C) z := by
  have hzB : C.box.chart.symm z ∈ B.box.chart.source := hz.2
  have hzC : z ∈ C.box.chart.target := hz.1
  unfold coordinatePullback primitive primitivePullback
  rw [if_pos hzB, ContinuousLinearMap.comp_assoc, (B.transition_deriv C hinc hsC hzC).fderiv]
  rfl

theorem primitive_curvature (hinc : B.inclusion = C.inclusion)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ∀ x u v, Ω x u v = -Ω x v u)
    (hf : ContDiff ℝ ∞ (B.coefficient Ω))
    (hzero : ∀ x y, B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2| →
      B.coefficient Ω (x,y) = 0)
    (hmass : B.mass Ω = 0) {K : Set M}
    (hKB : K ⊆ B.box.chart.source) (hzΩ : ∀ x, x ∉ K → Ω x = 0)
    {z : Plane} (hz : z ∈ C.box.chart.target) :
    euclideanExteriorOneForm (C.coordinatePullback (B.primitive (B.coefficient Ω))) z =
      C.coefficient Ω z • planarArea := by
  have hp := formulaTranslatedCovectorOperator_spec (P := ℝ) B.box.radius_pos B.box.point
    (f := fun q : ℝ × Plane => B.coefficient Ω q.2) (hf.comp contDiff_snd)
    (fun _ x y hh => hzero x y hh)
    (fun _ => by simpa only [mass, SymplecticPacking.Explicit.planeVolume_eq_volume] using hmass)
  let β := formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point (B.coefficient Ω)
  have hβ : ContDiff ℝ ∞ β := covector_family_slice_smooth
    (β := fun q : ℝ × Plane => β q.2) hp.1 0
  by_cases hxB : C.box.chart.symm z ∈ B.box.chart.source
  · have hzt : z ∈ (C.box.chart.symm.trans B.box.chart).source := ⟨hz,hxB⟩
    have he : C.coordinatePullback (B.primitive (B.coefficient Ω)) =ᶠ[𝓝 z]
        primitivePullback β (B.transition C) := by
      filter_upwards [(C.box.chart.symm.trans B.box.chart).open_source.mem_nhds hzt] with w hw
      exact B.primitive_pullback_transition C hinc hsC _ hw
    have hT : ContDiffAt ℝ ∞ (B.transition C) z := by
      rw [B.transition_eq C hinc]
      exact (B.coordinate.contDiff.comp_contDiffOn hsC).contDiffAt
        (C.box.chart.open_target.mem_nhds hz)
    rw [show euclideanExteriorOneForm (C.coordinatePullback (B.primitive (B.coefficient Ω))) z =
        euclideanExteriorOneForm (primitivePullback β (B.transition C)) z by
      simp only [euclideanExteriorOneForm, he.fderiv_eq]]
    rw [primitivePullback_exteriorAt hβ.contDiffAt hT]
    change (euclideanExteriorOneForm β (B.transition C z)).bilinearComp
      (fderiv ℝ (B.transition C) z) (fderiv ℝ (B.transition C) z) = _
    rw [hp.2.2 0 (B.transition C z), B.coefficient_change C hinc hsB hsC Ω hΩ hzt]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.bilinearComp_apply, smul_apply, smul_eq_mul,
      planarArea_map]
    ring
  · have hxK : C.box.chart.symm z ∉ B.box.compactCarrier := by
      rintro ⟨w, hw, hwe⟩
      rw [← hwe] at hxB
      exact hxB (B.box.chart.map_target (B.box.closed_subset hw))
    have hU := C.box.chart.symm.continuousOn.isOpen_inter_preimage
      C.box.chart.open_target B.box.compactCarrier_compact.isClosed.isOpen_compl
    have he : C.coordinatePullback (B.primitive (B.coefficient Ω)) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hU.mem_nhds ⟨hz,hxK⟩] with w hw
      unfold coordinatePullback
      rw [(B.primitive_spec hsB hf hzero hmass).1 _ hw.2]
      exact ContinuousLinearMap.zero_comp _
    have hΩz : Ω (C.box.chart.symm z) = 0 := hzΩ _ (fun hk => hxB (hKB hk))
    have hcz : C.coefficient Ω z = 0 := by
      simp only [coefficient, if_pos hz, hΩz, zero_apply]
    rw [hcz]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [euclideanExteriorOneForm, he.fderiv_eq, fderiv_zero, sub_apply,
      ContinuousLinearMap.flip_apply, Pi.zero_apply, zero_apply, sub_self, smul_apply, smul_eq_mul, zero_mul]

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
