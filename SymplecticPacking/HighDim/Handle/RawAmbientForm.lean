import SymplecticPacking.HighDim.Handle.RawAmbientBox
import SymplecticPacking.HighDim.Handle.ExplicitUnitBump

/-!
# Ambient differential forms in raw coordinates

Ambient differential forms from the displayed raw coordinates.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

/-- A fixed coordinate two-form, returned as an ambient bilinear form. -/
def supportedForm (f : Plane → ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ := by
  classical
  exact if x ∈ B.box.chart.source then
    f (B.box.chart x) • planarArea.bilinearComp B.coordinate B.coordinate else 0

/-- The coefficient in a displayed chart; it vanishes off its target. -/
def coefficient (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (z : Plane) : ℝ := by
  classical
  exact if z ∈ B.box.chart.target then
    Ω (B.box.chart.symm z) (B.frame z (1,0)) (B.frame z (0,1)) else 0

def mass (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ∫ z, B.coefficient Ω z ∂SymplecticPacking.Explicit.planeVolume

theorem supportedForm_skew (f : Plane → ℝ) (x : M) (u v : E) :
    B.supportedForm f x u v = -B.supportedForm f x v u := by
  unfold supportedForm
  split_ifs <;> simp only [ContinuousLinearMap.bilinearComp_apply, smul_apply,
    smul_eq_mul, zero_apply, neg_zero]
  simp only [planarArea_apply]
  ring

theorem supportedForm_coefficient
    (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (f : Plane → ℝ) (hz : ∀ z, z ∉ B.box.chart.target → f z = 0) :
    B.coefficient (B.supportedForm f) = f := by
  funext z
  by_cases hzt : z ∈ B.box.chart.target
  · have he := B.frame_rightInverse hs hzt
    have hcoord (v : Plane) : B.coordinate (B.frame z v) = v := congrArg (fun g => g v) he
    simp only [coefficient, if_pos hzt, supportedForm, if_pos (B.box.chart.map_target hzt),
      B.box.chart.right_inv hzt, smul_apply, smul_eq_mul,
      ContinuousLinearMap.bilinearComp_apply, hcoord, planarArea_apply]
    ring
  · simp only [coefficient, if_neg hzt, hz z hzt]

theorem supportedForm_mass
    (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (f : Plane → ℝ) (hz : ∀ z, z ∉ B.box.chart.target → f z = 0) :
    B.mass (B.supportedForm f) = ∫ z, f z ∂SymplecticPacking.Explicit.planeVolume := by
  unfold mass
  rw [B.supportedForm_coefficient hs f hz]

theorem supportedForm_zero (f : Plane → ℝ) {C : Set Plane}
    (hz : ∀ z, z ∉ C → f z = 0) {x : M}
    (hx : x ∉ B.box.chart.symm '' C) : B.supportedForm f x = 0 := by
  unfold supportedForm
  split_ifs with hxs
  · rw [hz _ (fun hc => hx ⟨_, hc, B.box.chart.left_inv hxs⟩)]
    ext u v
    change (0:ℝ) * _ = 0
    ring
  · rfl

theorem supportedForm_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {C : Set Plane} (hC : IsCompact C) (hCt : C ⊆ B.box.chart.target)
    (hz : ∀ z, z ∉ C → f z = 0) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (B.supportedForm f) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hK : IsCompact (B.box.chart.symm '' C) :=
    hC.image_of_continuousOn (B.box.chart.continuousOn_symm.mono hCt)
  have hsu : tsupport (B.supportedForm f) ⊆ B.box.chart.symm '' C := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (B.supportedForm_zero f hz hn)
  have hraw : ContDiff ℝ ∞ (fun z =>
      f z • planarArea.bilinearComp B.coordinate B.coordinate) := hf.smul contDiff_const
  apply contMDiff_of_tsupport
  intro x hx
  obtain ⟨z, hzc, hzx⟩ := hsu hx
  have hxs : x ∈ B.box.chart.source := by
    rw [← hzx]
    exact B.box.chart.map_target (hCt hzc)
  apply ContMDiffAt.congr_of_eventuallyEq
    (hraw.contMDiff.contMDiffAt.comp x ((hB.forward x hxs).contMDiffAt
      (B.box.chart.open_source.mem_nhds hxs)))
  filter_upwards [B.box.chart.open_source.mem_nhds hxs] with y hy
  exact if_pos hy

def unitBumpCoefficient (z : Plane) : ℝ :=
  planarUnitBump (B.box.radius/2) (by linarith [B.box.radius_pos]) (z-B.box.point)

def unitBump : M → E →L[ℝ] E →L[ℝ] ℝ := B.supportedForm B.unitBumpCoefficient

theorem unitBumpCoefficient_zero {z : Plane}
    (hz : z ∉ Metric.closedBall B.box.point (B.box.radius/2)) : B.unitBumpCoefficient z = 0 := by
  have hh : B.box.radius/2 < max |z.1-B.box.point.1| |z.2-B.box.point.2| := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs, not_le] using hz
  exact (planarUnitBump_spec (B.box.radius/2) (by linarith [B.box.radius_pos])).2.2.2.1
    _ _ ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)

theorem unitBump_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ B.unitBump := by
  apply B.supportedForm_smooth hB (C := Metric.closedBall B.box.point (B.box.radius/2))
    ((planarUnitBump_spec (B.box.radius/2) (by linarith [B.box.radius_pos])).1.comp
      (contDiff_id.sub contDiff_const)) (isCompact_closedBall _ _)
  · exact (Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])).trans B.box.closed_subset
  · exact fun _ hz => B.unitBumpCoefficient_zero hz

theorem unitBump_mass (hs : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target) :
    B.mass B.unitBump = 1 := by
  have hz : ∀ z, z ∉ B.box.chart.target → B.unitBumpCoefficient z = 0 := by
    intro z hzt
    apply B.unitBumpCoefficient_zero
    exact fun hc => hzt (B.box.closed_subset
      ((Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])) hc))
  rw [unitBump, B.supportedForm_mass hs _ hz,
    SymplecticPacking.Explicit.planeVolume_eq_volume]
  change (∫ z, planarUnitBump (B.box.radius/2) _ (z-B.box.point)) = 1
  rw [integral_sub_right_eq_self]
  exact (planarUnitBump_spec (B.box.radius/2) (by linarith [B.box.radius_pos])).2.2.2.2

theorem unitBump_zero {x : M}
    (hx : x ∉ B.box.chart.symm '' Metric.closedBall B.box.point (B.box.radius/2)) :
    B.unitBump x = 0 :=
  B.supportedForm_zero _ (fun _ hn => B.unitBumpCoefficient_zero hn) hx

end RawAmbientBox
#check_explicit RawAmbientBox.supportedForm
#check_explicit RawAmbientBox.coefficient
#check_explicit RawAmbientBox.mass
#check_explicit RawAmbientBox.unitBump
end SymplecticPacking.HighDim.ToricPackingStages
