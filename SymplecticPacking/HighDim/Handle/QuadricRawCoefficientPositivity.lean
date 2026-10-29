import SymplecticPacking.HighDim.Handle.QuadricRawCanonicalOrientation
import SymplecticPacking.HighDim.Handle.RawManifoldNaturality
import OAI.Geometry.BallPacking.Surfaces.QuadricOrientation

/-!
# Positivity of the native quadric chart coefficients

Positive native chart coefficients from the canonical complex orientation.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem quadricRaw_coefficient_positive (B : RawAmbientBox (Affine m) (locus a))
    (centre : locus a) (tag : Option (Fin m)) (hc : centre.val∈regularCoordinate tag)
    (hchart : B.box.chart=rawQuadricRealChart centre tag hc)
    (hinc : B.inclusion=Subtype.val) (hB : B.box.Smooth)
    {Ω : locus a → Affine m →L[ℝ] Affine m →L[ℝ] ℝ}
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (z : Plane) (hz : z∈B.box.chart.target)
    (hpos : 0<chartTwoForm (semanticTwoForm Subtype.val Ω) (B.box.chart.symm z)
      (extChartAt 𝓘(ℝ,Plane) (B.box.chart.symm z) (B.box.chart.symm z)) (1,0) (0,1)) :
    0<Ω (B.box.chart.symm z) (B.frame z (1,0)) (B.frame z (0,1)) := by
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane (locus a) ∞ :=
    { toPartialEquiv := B.box.chart.symm.toPartialEquiv
      open_source := B.box.chart.open_target
      open_target := B.box.chart.open_source
      contMDiffOn_toFun := hB.inverse
      contMDiffOn_invFun := hB.forward }
  have hp : PositivePartialChart e := by
    intro c y hy hcy
    change y∈B.box.chart.target at hy
    change B.box.chart.symm y∈(extChartAt 𝓘(ℝ,Plane) c).source at hcy
    change 0<(fderiv ℝ ((extChartAt 𝓘(ℝ,Plane) c) ∘ B.box.chart.symm) y).det
    rw [hchart] at hy hcy ⊢
    exact rawQuadricChart_canonical_transition_positive centre tag hc c hy hcy
  let x := B.box.chart.symm z
  have hcanon : x∈(extChartAt 𝓘(ℝ,Plane) x).source := mem_extChartAt_source x
  have hpb := semanticTwoForm_pullback B (real_inclusion_contMDiff a) hinc hB Ω hz
  have hcoef : partialChartCoefficient e (semanticTwoForm Subtype.val Ω) z=
      Ω x (B.frame z (1,0)) (B.frame z (0,1)) := by
    simpa only [mfld_simps,e,x,partialChartCoefficient,euclideanPullbackTwoForm,manifoldPullbackTwoForm,
      manifoldMapDifferential,ContinuousLinearMap.bilinearComp_apply] using
      congrArg (fun A : Plane →L[ℝ] Plane →L[ℝ] ℝ => A (1,0) (0,1)) hpb
  have hs (x : locus a) (u v : Plane) : semanticTwoForm Subtype.val Ω x u v = -semanticTwoForm Subtype.val Ω x v u :=
    hsk x _ _
  have hch := partialChartCoefficient_change e hs hz hcanon
  rw [hcoef] at hch
  rw [hch]
  exact mul_pos (hp x z hz hcanon) hpos

end SymplecticPacking.HighDim.ToricPackingStages
