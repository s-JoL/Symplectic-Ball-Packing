import SymplecticPacking.HighDim.Handle.RawManifoldNaturality
import SymplecticPacking.HighDim.Handle.RawAmbientUnitMass
import OAI.Geometry.BallPacking.SurfaceArea.QuadricEndResidueMass

/-!
# Intrinsic mass of the raw root bump

The raw root bump has intrinsic surface mass one.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem unitBump_partition_mass {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion=ι)
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hpos : ∀ c y, y ∈ B.box.chart.target →
      B.box.chart.symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source →
      0 < (fderiv ℝ ((extChartAt 𝓘(ℝ,Plane) c) ∘ B.box.chart.symm) y).det)
    {I : Type} [Fintype I] {K : Set M}
    (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier)) (hUK : B.unitSupport ⊆ K) :
    partitionFormMass Boxes ρ (semanticTwoForm ι B.unitBump)=1 := by
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞ :=
    { toPartialEquiv := B.box.chart.symm.toPartialEquiv
      open_source := B.box.chart.open_target
      open_target := B.box.chart.open_source
      contMDiffOn_toFun := hB.inverse
      contMDiffOn_invFun := hB.forward }
  have hePos : PositivePartialChart e := hpos
  have heT : B.unitSupport ⊆ e.target := fun x hx => (B.unitSupport_subset hx).1
  have hsm := semanticTwoForm_smooth hι (B.unitBump_smooth hB)
  have hsk : ∀ x u v, semanticTwoForm ι B.unitBump x u v = -semanticTwoForm ι B.unitBump x v u :=
    fun x u v => B.supportedForm_skew B.unitBumpCoefficient x _ _
  have hzero (x : M) (hx : x ∉ B.unitSupport) : semanticTwoForm ι B.unitBump x=0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change B.unitBump x _ _=0
    rw [B.unitBump_zero hx]
    rfl
  have hinner : Metric.closedBall B.box.point (B.box.radius/2) ⊆ B.box.chart.target :=
    (Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])).trans B.box.closed_subset
  have himage : e.symm '' B.unitSupport=Metric.closedBall B.box.point (B.box.radius/2) := by
    ext z
    constructor
    · rintro ⟨x,⟨w,hw,rfl⟩,rfl⟩
      change B.box.chart (B.box.chart.symm w) ∈ Metric.closedBall B.box.point (B.box.radius/2)
      rwa [B.box.chart.right_inv (hinner hw)]
    · intro hz
      exact ⟨B.box.chart.symm z,⟨z,hz,rfl⟩,B.box.chart.right_inv (hinner hz)⟩
  have hfzt : ∀ z, z ∉ B.box.chart.target → B.unitBumpCoefficient z=0 := by
    intro z hzt
    exact B.unitBumpCoefficient_zero (fun hz => hzt (hinner hz))
  have hcoef := B.supportedForm_coefficient hsB B.unitBumpCoefficient hfzt
  have heCoef (z : Plane) (hz : z ∈ Metric.closedBall B.box.point (B.box.radius/2)) :
      partialChartCoefficient e (semanticTwoForm ι B.unitBump) z=B.unitBumpCoefficient z := by
    have hpb := semanticTwoForm_pullback B hι hinc hB B.unitBump (hinner hz)
    have hv := congrArg (fun A : Plane →L[ℝ] Plane →L[ℝ] ℝ => A (1,0) (0,1)) hpb
    have hh : partialChartCoefficient e (semanticTwoForm ι B.unitBump) z=B.coefficient B.unitBump z := by
      simpa only [mfld_simps,e, partialChartCoefficient,euclideanPullbackTwoForm,manifoldPullbackTwoForm,
        manifoldMapDifferential,ContinuousLinearMap.bilinearComp_apply,
        coefficient,if_pos (hinner hz)] using hv
    exact hh.trans (congrFun hcoef z)
  calc
    partitionFormMass Boxes ρ (semanticTwoForm ι B.unitBump) =
        ∫ z in e.symm '' B.unitSupport,partialChartCoefficient e (semanticTwoForm ι B.unitBump) z :=
      partitionFormMass_eq_partialChart_integral e hePos B.unitSupport_compact heT Boxes
        (partitionOnSubset ρ hUK) hρ hsm hsk hzero
    _ = ∫ z in Metric.closedBall B.box.point (B.box.radius/2),B.unitBumpCoefficient z := by
      rw [himage]
      exact setIntegral_congr_fun (Metric.isClosed_closedBall.measurableSet) heCoef
    _ = ∫ z,B.unitBumpCoefficient z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => B.unitBumpCoefficient_zero hz)
    _ = 1 := by
      change (∫ z,planarUnitBump (B.box.radius/2) _ (z-B.box.point))=1
      rw [integral_sub_right_eq_self]
      exact (planarUnitBump_spec (B.box.radius/2) (by linarith [B.box.radius_pos])).2.2.2.2

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
