import SymplecticPacking.HighDim.Handle.QuadricFiniteOverlap
import SymplecticPacking.HighDim.Handle.QuadricRawOrientation
import SymplecticPacking.HighDim.Handle.RawSurfaceTree

/-!
# Geometry of the quadric root-chart presentation

Ambient and smooth compatibility bridges for the finite root-chart certificates.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold
namespace QuadricRootChart
variable {m : ℕ} {a : Fin m → ℂ}

/-- Offset boxes use the same fixed ambient coordinate as their root chart. -/
def ambientBox (C : QuadricRootChart a) (B : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) : RawAmbientBox (Affine m) (locus a) where
  box := B
  inclusion := Subtype.val
  coordinate := quadricCoordinateProjection C.tag
  coordinate_eq := by
    intro x
    rw [hB,C.chart_apply]
    cases C.tag <;> rfl

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem box_smooth (C : QuadricRootChart a) (B : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) : B.Smooth := by
  rw [show B.Smooth ↔
    ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ B.chart B.chart.source ∧
    ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ B.chart.symm B.chart.target from ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.1,h.2⟩⟩]
  rw [hB]
  rcases C with ⟨c,tag,hc⟩
  cases tag with
  | none => exact ⟨(ordinaryRealExplicitChart_smooth c hc).contMDiffOn,
      ordinaryRealExplicitChart_inverse_smooth c hc⟩
  | some i => exact ⟨(branchRealExplicitChart_smooth c i hc).contMDiffOn,
      branchRealExplicitChart_inverse_smooth c i hc⟩

theorem ambientBox_inverse_smooth (C : QuadricRootChart a) (B : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) :
    ContDiffOn ℝ ∞ (C.ambientBox B hB).inverseAmbient B.chart.target := by
  change ContDiffOn ℝ ∞ (fun z => (B.chart.symm z).val) B.chart.target
  rw [hB]
  rcases C with ⟨c,tag,hc⟩
  cases tag with
  | none =>
    exact ((ordinaryLocalLift_smooth c hc).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hz => hz.2)
  | some i =>
    exact ((branchLocalLift_smooth c i hc).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hz => hz.2)

theorem transition_positive (C E : QuadricRootChart a) {z : Plane}
    (hz : z ∈ (C.chart.symm.trans E.chart).source) :
    0 < (fderiv ℝ (E.chart ∘ C.chart.symm) z).det := by
  let c := rawQuadricChart C.centre C.tag C.regular
  let e := rawQuadricChart E.centre E.tag E.regular
  have hzc : Complex.equivRealProdCLM.symm z ∈ (c.symm.trans e).source := by
    rcases C with ⟨c,tc,hc⟩
    rcases E with ⟨e,te,he⟩
    cases tc <;> cases te <;> exact ⟨hz.1.2,hz.2.1⟩
  have heq : E.chart ∘ C.chart.symm =
      Complex.equivRealProdCLM ∘ (c.symm.trans e) ∘ Complex.equivRealProdCLM.symm := by
    rcases C with ⟨c,tc,hc⟩
    rcases E with ⟨e,te,he⟩
    cases tc <;> cases te <;> rfl
  rw [heq]
  exact rawQuadricChart_transition_positive C.centre E.centre C.tag E.tag C.regular E.regular hzc

end QuadricRootChart
#check_explicit QuadricRootChart.ambientBox
end SymplecticPacking.HighDim.ToricPackingStages
