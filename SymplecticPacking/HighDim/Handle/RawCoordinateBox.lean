import SymplecticPacking.HighDim.Handle.ExplicitPartition

/-!
# Raw coordinate boxes and their weights

Fixed coordinate-box formulas with charts supplied as data.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

/-- Unlike `SurfaceCoordinateBox`, the chart is supplied explicitly, independently of the
ambient manifold's selected `chartAt`. Compatibility is a separate proof property. -/
structure RawCoordinateBox (M : Type) [TopologicalSpace M] where
  chart : OpenPartialHomeomorph M Plane
  point : Plane
  radius : ℝ
  radius_pos : 0 < radius
  closed_subset : Metric.closedBall point radius ⊆ chart.target

namespace RawCoordinateBox
variable {M : Type} [TopologicalSpace M] [T2Space M]

structure Smooth [ChartedSpace Plane M] (B : RawCoordinateBox M) : Prop where
  forward : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ B.chart B.chart.source
  inverse : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ B.chart.symm B.chart.target

def carrier (B : RawCoordinateBox M) : Set M :=
  B.chart.source ∩ B.chart ⁻¹' Metric.ball B.point B.radius

def compactCarrier (B : RawCoordinateBox M) : Set M :=
  B.chart.symm '' Metric.closedBall B.point B.radius

theorem compactCarrier_compact (B : RawCoordinateBox M) : IsCompact B.compactCarrier :=
  (isCompact_closedBall _ _).image_of_continuousOn (B.chart.continuousOn_symm.mono B.closed_subset)

theorem carrier_subset_compactCarrier (B : RawCoordinateBox M) : B.carrier ⊆ B.compactCarrier := by
  intro x hx
  exact ⟨B.chart x, Metric.ball_subset_closedBall hx.2, B.chart.left_inv hx.1⟩

/-- Inner closed coordinate box on which the weight is exactly one. -/
def inner (B : RawCoordinateBox M) : Set M :=
  B.chart.symm '' Metric.closedBall B.point (B.radius/4)

def innerOpen (B : RawCoordinateBox M) : Set M :=
  B.chart.source ∩ B.chart ⁻¹' Metric.ball B.point (B.radius/4)

theorem innerOpen_open (B : RawCoordinateBox M) : IsOpen B.innerOpen :=
  B.chart.continuousOn.isOpen_inter_preimage B.chart.open_source Metric.isOpen_ball

theorem innerOpen_subset_inner (B : RawCoordinateBox M) : B.innerOpen ⊆ B.inner := by
  intro x hx
  exact ⟨B.chart x, Metric.ball_subset_closedBall hx.2, B.chart.left_inv hx.1⟩

/-- The coordinate plateau extended by zero; its support lies strictly inside the box. -/
def weight (B : RawCoordinateBox M) (x : M) : ℝ := by
  classical
  exact if x ∈ B.chart.source then
    plateauLine (B.radius/2) ((B.chart x).1 - B.point.1) *
    plateauLine (B.radius/2) ((B.chart x).2 - B.point.2)
  else 0

theorem weight_nonneg (B : RawCoordinateBox M) (x : M) : 0 ≤ weight B x := by
  unfold weight
  split_ifs
  · exact mul_nonneg (plateauLine_nonneg _ _) (plateauLine_nonneg _ _)
  · exact le_rfl

theorem weight_zero (B : RawCoordinateBox M) (x : M)
    (hx : x ∉ B.chart.symm ''
      Metric.closedBall B.point (B.radius/2)) : weight B x = 0 := by
  classical
  unfold weight
  split_ifs with hs
  · have hn : B.chart x ∉ Metric.closedBall B.point (B.radius/2) :=
      fun hy => hx ⟨_, hy, B.chart.left_inv hs⟩
    have hh : B.radius/2 < max |(B.chart x).1-B.point.1|
        |(B.chart x).2-B.point.2| := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, Real.norm_eq_abs, not_le] using hn
    rcases lt_max_iff.mp hh with h | h
    · rw [plateauLine_zero (by linarith [B.radius_pos]) _ h.le, zero_mul]
    · rw [plateauLine_zero (by linarith [B.radius_pos]) _ h.le, mul_zero]
  · rfl

theorem weight_support (B : RawCoordinateBox M) : tsupport (weight B) ⊆ B.carrier := by
  let C := Metric.closedBall B.point (B.radius/2)
  have hC : C ⊆ B.chart.target :=
    (Metric.closedBall_subset_closedBall (by linarith [B.radius_pos])).trans B.closed_subset
  have hK : IsCompact (B.chart.symm '' C) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (B.chart.continuousOn_symm.mono hC)
  have hz : tsupport (weight B) ⊆ B.chart.symm '' C :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (weight_zero B x hn)) hK.isClosed
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := hz hx
  refine ⟨B.chart.map_target (hC hy), ?_⟩
  change B.chart (B.chart.symm y) ∈ Metric.ball B.point B.radius
  rw [B.chart.right_inv (hC hy)]
  exact (Metric.closedBall_subset_ball (by linarith [B.radius_pos])) hy

theorem weight_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ, Plane) ∞ M]
    (B : RawCoordinateBox M) (hB : B.Smooth) :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ (weight B) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := (weight_support B hx).1
  have hraw : ContDiff ℝ ∞ (fun y : Plane =>
      plateauLine (B.radius/2) (y.1-B.point.1) * plateauLine (B.radius/2) (y.2-B.point.2)) :=
    ((plateauLine_smooth _).comp (contDiff_fst.sub contDiff_const)).mul
      ((plateauLine_smooth _).comp (contDiff_snd.sub contDiff_const))
  apply ContMDiffAt.congr_of_eventuallyEq
    (hraw.contMDiff.contMDiffAt.comp x ((hB.forward x hxs).contMDiffAt (B.chart.open_source.mem_nhds hxs)))
  filter_upwards [B.chart.open_source.mem_nhds hxs] with y hy
  exact if_pos hy

theorem weight_one (B : RawCoordinateBox M) (x : M) (hx : x ∈ inner B) :
    weight B x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyt : y ∈ B.chart.target :=
    B.closed_subset ((Metric.closedBall_subset_closedBall (by linarith [B.radius_pos])) hy)
  unfold weight
  rw [if_pos (B.chart.map_target hyt),
    B.chart.right_inv hyt]
  have hh : max |y.1-B.point.1| |y.2-B.point.2| ≤ B.radius/4 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs] using hy
  rw [plateauLine_one (by linarith [B.radius_pos]) _
    (by linarith [le_max_left |y.1-B.point.1| |y.2-B.point.2|]),
    plateauLine_one (by linarith [B.radius_pos]) _
    (by linarith [le_max_right |y.1-B.point.1| |y.2-B.point.2|]), mul_one]

end RawCoordinateBox
end SymplecticPacking.HighDim.ToricPackingStages
