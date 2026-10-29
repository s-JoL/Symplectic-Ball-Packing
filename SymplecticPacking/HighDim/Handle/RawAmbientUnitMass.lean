import SymplecticPacking.HighDim.Handle.RawAmbientMass

/-!
# Unit mass of fixed bumps in raw charts

Fixed unit bumps retain unit mass in every positively oriented raw chart.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B C : RawAmbientBox E M)

def unitSupport : Set M :=
  B.box.chart.symm '' Metric.closedBall B.box.point (B.box.radius/2)

theorem unitSupport_compact : IsCompact B.unitSupport :=
  (isCompact_closedBall _ _).image_of_continuousOn
    (B.box.chart.continuousOn_symm.mono
      ((Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])).trans B.box.closed_subset))

theorem unitSupport_subset : B.unitSupport ⊆ B.box.carrier := by
  rintro x ⟨z, hz, rfl⟩
  have hzt : z ∈ B.box.chart.target := B.box.closed_subset
    ((Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])) hz)
  refine ⟨B.box.chart.map_target hzt, ?_⟩
  change B.box.chart (B.box.chart.symm z) ∈ Metric.ball B.box.point B.box.radius
  rw [B.box.chart.right_inv hzt]
  exact Metric.closedBall_subset_ball (by linarith [B.box.radius_pos]) hz

theorem unitBump_mass_in (hinc : C.inclusion = B.inclusion)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    (hBC : B.unitSupport ⊆ C.box.chart.source)
    (hpos : ∀ z ∈ B.box.chart '' B.unitSupport, 0 < (fderiv ℝ (C.transition B) z).det) :
    C.mass B.unitBump = 1 := by
  have he := C.mass_change B hinc hsC hsB
    (Ω := B.unitBump) (B.supportedForm_skew B.unitBumpCoefficient)
    B.unitSupport_compact hBC (fun x hx => (B.unitSupport_subset hx).1)
    (fun x hx => B.unitBump_zero hx) hpos
  exact he.symm.trans (B.unitBump_mass hsB)

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
