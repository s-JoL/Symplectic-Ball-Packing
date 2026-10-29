import SymplecticPacking.HighDim.Handle.RawManifoldExterior
import SymplecticPacking.HighDim.Handle.RawSurfaceMass
import SymplecticPacking.HighDim.Handle.RawUnitBumpIntrinsic
import OAI.Geometry.BallPacking.SurfaceArea.SurfaceInteriorBoxes

/-!
# Intrinsic calibration of the raw surface integral

Calibration of the formula integral by the root bump, using compact Stokes.
No coordinate representation occurring in this proof is used by the raw algorithm.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem semanticTwoForm_smul (ι : M → E) (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) :
    semanticTwoForm ι (a • Ω)=a • semanticTwoForm ι Ω := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem semanticTwoForm_sub (ι : M → E) (Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ) :
    semanticTwoForm ι (Ω-Ξ)=semanticTwoForm ι Ω-semanticTwoForm ι Ξ := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem semanticTwoForm_zero_at (ι : M → E) {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    {x : M} (h : Ω x=0) : semanticTwoForm ι Ω x=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω x _ _=0
  rw [h]
  rfl

theorem semanticOneForm_zero_at (ι : M → E) {α : M → E →L[ℝ] ℝ}
    {x : M} (h : α x=0) : semanticOneForm ι α x=0 := by
  apply ContinuousLinearMap.ext
  intro u
  change α x _=0
  rw [h]
  rfl

namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)
variable (hG : D.Geometry)
variable (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
variable (hall : ∀ x : M, ∃ C : RawAmbientBox E M,
  C.inclusion=D.inclusion ∧ C.box.Smooth ∧
  ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target ∧ x ∈ C.box.chart.source)
variable (hor : PositivePlaneTransitions M)
include hG hι hall hor

theorem zero_mass_intrinsic {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hcover : K ⊆ ⋃ i, (D.boxes i).box.inner) (hDL : D.support ⊆ L)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v, Ω x u v = -Ω x v u)
    (hz : ∀ x, x ∉ K → Ω x=0) (hm : D.formMass Ω=0) :
    partitionFormMass Boxes ρ (semanticTwoForm D.inclusion Ω)=0 := by
  have hp := D.primitiveOperator_data hG hK hcover hΩ hsk hz hm
  rw [← hp.1.semantic_exterior hι hsk hall]
  exact partitionFormMass_compact_stokes hor hL Boxes ρ hρ
    (semanticOneForm_smooth hι hp.1.smooth)
    (fun x hx => semanticOneForm_zero_at _ (hp.2 x (fun h => hx (hDL h))))

theorem massCalibration_ne_zero {L : Set M} (hL : IsCompact L)
    (hcover : (D.boxes D.root).unitSupport ⊆ ⋃ i, (D.boxes i).box.inner)
    (hDL : D.support ⊆ L)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    (hunit : partitionFormMass Boxes ρ
      (semanticTwoForm D.inclusion (D.boxes D.root).unitBump)=1) :
    D.massCalibration ≠ 0 := by
  intro hm
  have hz := D.zero_mass_intrinsic hG hι hall hor
    (D.boxes D.root).unitSupport_compact hL hcover hDL Boxes ρ hρ
    ((D.boxes D.root).unitBump_smooth (hG.box_smooth D.root))
    (fun x u v => (D.boxes D.root).supportedForm_skew _ x u v)
    (fun x hx => (D.boxes D.root).unitBump_zero hx) hm
  rw [hunit] at hz
  exact one_ne_zero hz

theorem calibratedMass_eq_partition {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hcover : K ⊆ ⋃ i, (D.boxes i).box.inner) (hKL : K ⊆ L) (hDL : D.support ⊆ L)
    (hunitK : (D.boxes D.root).unitSupport ⊆ K)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    (hunit : partitionFormMass Boxes ρ
      (semanticTwoForm D.inclusion (D.boxes D.root).unitBump)=1)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v, Ω x u v = -Ω x v u)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    D.calibratedMass Ω=partitionFormMass Boxes ρ (semanticTwoForm D.inclusion Ω) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  let η := (D.boxes D.root).unitBump
  let a := D.formMass Ω
  let b := D.massCalibration
  have hη : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ η :=
    (D.boxes D.root).unitBump_smooth (hG.box_smooth D.root)
  have hzη (x : M) (hx : x ∉ K) : η x=0 :=
    (D.boxes D.root).unitBump_zero (fun h => hx (hunitK h))
  have hA : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (a • η) :=
    (show ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun _ : M => a) from contMDiff_const).smul hη
  have hB : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (b • Ω) :=
    (show ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun _ : M => b) from contMDiff_const).smul hΩ
  have hzA (x : M) (hx : x ∉ K) : (a • η) x=0 := by
    change a • η x=0
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change a*η x u v=0
    rw [hzη x hx]
    exact mul_zero _
  have hzB (x : M) (hx : x ∉ K) : (b • Ω) x=0 := by
    change b • Ω x=0
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change b*Ω x u v=0
    rw [hz x hx]
    exact mul_zero _
  have hm : D.formMass (a • η-b • Ω)=0 := by
    rw [D.formMass_sub (D.weightedCoefficient_integrable hG hA hK hzA)
      (D.weightedCoefficient_integrable hG hB hK hzB),D.formMass_smul,D.formMass_smul]
    change a*b-b*a=0
    ring
  have hskD (x : M) (u v : E) :
      (a • η-b • Ω) x u v = -(a • η-b • Ω) x v u := by
    change a*η x u v-b*Ω x u v = -(a*η x v u-b*Ω x v u)
    have hηsk := (D.boxes D.root).supportedForm_skew (D.boxes D.root).unitBumpCoefficient x u v
    change η x u v = -η x v u at hηsk
    rw [hηsk,hsk]
    ring
  have hzD (x : M) (hx : x ∉ K) : (a • η-b • Ω) x=0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (a • η) x u v-(b • Ω) x u v=0
    rw [hzA x hx,hzB x hx]
    exact sub_self _
  have hmI := D.zero_mass_intrinsic hG hι hall hor hK hL hcover hDL Boxes ρ hρ
    (hA.sub hB) hskD hzD hm
  change partitionFormMass Boxes ρ (semanticTwoForm D.inclusion (a • η-b • Ω))=0 at hmI
  change partitionFormMass Boxes ρ (semanticTwoForm D.inclusion η)=1 at hunit
  rw [semanticTwoForm_sub,partitionFormMass_sub hL Boxes ρ hρ
    (semanticTwoForm_smooth hι hA) (semanticTwoForm_smooth hι hB)
    (fun x hx => semanticTwoForm_zero_at _ (hzA x (fun h => hx (hKL h))))
    (fun x hx => semanticTwoForm_zero_at _ (hzB x (fun h => hx (hKL h)))),
    semanticTwoForm_smul,semanticTwoForm_smul,partitionFormMass_smul,partitionFormMass_smul,hunit] at hmI
  have hb : b≠0 := D.massCalibration_ne_zero hG hι hall hor hL
    (hunitK.trans hcover) hDL Boxes ρ hρ hunit
  unfold calibratedMass
  apply (div_eq_iff hb).mpr
  change a=partitionFormMass Boxes ρ (semanticTwoForm D.inclusion Ω)*b
  linarith

end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
