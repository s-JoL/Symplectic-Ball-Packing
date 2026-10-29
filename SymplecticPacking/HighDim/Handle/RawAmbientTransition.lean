import SymplecticPacking.HighDim.Handle.RawAmbientForm

/-!
# Transitions between raw ambient coordinate frames

Chain rule for the displayed ambient coordinate frames.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B C : RawAmbientBox E M)

def transition : Plane → Plane := B.box.chart ∘ C.box.chart.symm

theorem transition_eq (hinc : B.inclusion = C.inclusion) :
    B.transition C = B.coordinate ∘ C.inverseAmbient := by
  funext z
  exact (B.coordinate_eq (C.box.chart.symm z)).symm.trans
    (congrArg B.coordinate (congrFun hinc (C.box.chart.symm z)))

theorem transition_deriv (hinc : B.inclusion = C.inclusion)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    {z : Plane} (hz : z ∈ C.box.chart.target) :
    HasFDerivAt (B.transition C) (B.coordinate.comp (C.frame z)) z := by
  rw [B.transition_eq C hinc]
  exact B.coordinate.hasFDerivAt.comp z
    (((hsC z hz).contDiffAt (C.box.chart.open_target.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt

theorem frame_change (hinc : B.inclusion = C.inclusion)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    {z : Plane} (hz : z ∈ (C.box.chart.symm.trans B.box.chart).source) :
    (B.frame (B.transition C z)).comp (fderiv ℝ (B.transition C) z) = C.frame z := by
  have hzt : B.transition C z ∈ B.box.chart.target := B.box.chart.map_source hz.2
  have hfdB : HasFDerivAt B.inverseAmbient (B.frame (B.transition C z)) (B.transition C z) :=
    (((hsB _ hzt).contDiffAt (B.box.chart.open_target.mem_nhds hzt)).differentiableAt
      (by simp)).hasFDerivAt
  have hfdT := B.transition_deriv C hinc hsC hz.1
  have hfdC : HasFDerivAt C.inverseAmbient (C.frame z) z :=
    (((hsC z hz.1).contDiffAt (C.box.chart.open_target.mem_nhds hz.1)).differentiableAt
      (by simp)).hasFDerivAt
  have he : (fun w => B.inverseAmbient (B.transition C w)) =ᶠ[𝓝 z] C.inverseAmbient := by
    filter_upwards [(C.box.chart.symm.trans B.box.chart).open_source.mem_nhds hz] with w hw
    change B.inclusion (B.box.chart.symm (B.box.chart (C.box.chart.symm w))) =
      C.inclusion (C.box.chart.symm w)
    have hws : C.box.chart.symm w ∈ B.box.chart.source := hw.2
    rw [B.box.chart.left_inv hws, hinc]
  rw [hfdT.fderiv]
  exact ((hfdB.comp z hfdT).congr_of_eventuallyEq he.symm).unique hfdC

theorem coefficient_change (hinc : B.inclusion = C.inclusion)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u)
    {z : Plane} (hz : z ∈ (C.box.chart.symm.trans B.box.chart).source) :
    C.coefficient Ω z = (fderiv ℝ (B.transition C) z).det *
      B.coefficient Ω (B.transition C z) := by
  have hzt : B.transition C z ∈ B.box.chart.target := B.box.chart.map_source hz.2
  have hfr := B.frame_change C hinc hsB hsC hz
  have hv (v : Plane) : C.frame z v =
      B.frame (B.transition C z) (fderiv ℝ (B.transition C) z v) :=
    (congrArg (fun g => g v) hfr).symm
  have hx : B.box.chart.symm (B.transition C z) = C.box.chart.symm z :=
    B.box.chart.left_inv hz.2
  let α := (Ω (C.box.chart.symm z)).bilinearComp
    (B.frame (B.transition C z)) (B.frame (B.transition C z))
  have hα : ∀ u v, α u v = -α v u := fun u v => hΩ _ _ _
  have hzC : z ∈ C.box.chart.target := hz.1
  rw [coefficient, if_pos hzC, coefficient, if_pos hzt, hx, hv (1,0), hv (0,1)]
  change α (fderiv ℝ (B.transition C) z (1,0)) (fderiv ℝ (B.transition C) z (0,1)) =
    (fderiv ℝ (B.transition C) z).det * α (1,0) (0,1)
  rw [planar_skew_coefficient α hα, ← planar_det, mul_comm]

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
