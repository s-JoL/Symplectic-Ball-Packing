import SymplecticPacking.HighDim.Handle.QuadricRawDual
import SymplecticPacking.HighDim.Handle.RawSurfaceIntrinsicMass
import OAI.Geometry.BallPacking.Hamiltonian.AnnularDensityMass

/-!
# The native quadric handle density

The handle density in native ambient covectors.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.QuadricRawDensity
open Set Function Filter Manifold
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open QuadricRawDual
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (m : ℕ)

def nativeSheet (z : Affine (m+2)) : Prop :=
  transverseCoordinate m z ∈ transverseAnnulusDomain m ∧
    (∀ j : Fin (m+2),j≠0 → 0<(z.2 j).im) ∧
    Real.log ‖transverseCoordinate m z‖ ∈
      Ioo (-(BranchSmall.explicitCylinderWidth m/2)) (BranchSmall.explicitCylinderWidth m/2)

def radialCoordinate (b : ℝ) (z : Plane) : ℝ :=
  intervalClock (-b) b (Real.log ‖Complex.equivRealProdCLM.symm z‖)

def radial (b : ℝ) (z : Affine (m+2)) : Affine (m+2) →L[ℝ] ℝ := by
  classical
  exact if nativeSheet m z then
    (fderiv ℝ (radialCoordinate b) (transverseProjection m z)).comp (transverseProjection m)
  else 0

theorem nativeSheet_iff (x : Surface m) :
    nativeSheet m x.val ↔ x ∈ (BranchSmall.quadricHandleData m).chart.target := by
  change _ ↔ x ∈ (transverseCylinder m).target ∩ (transverseCylinder m).symm ⁻¹'
    (Ioo (-(BranchSmall.explicitCylinderWidth m/2)) (BranchSmall.explicitCylinderWidth m/2) ×ˢ univ)
  rw [mem_inter_iff,transverseCylinder_target]
  simp only [nativeSheet,mem_preimage,mem_prod,mem_univ,and_true,
    transverseCylinder_symm_apply,cylinderComplexInverse]
  tauto

theorem radialCoordinate_contDiffAt (b : ℝ) {z : Plane}
    (hz : Complex.equivRealProdCLM.symm z≠0) : ContDiffAt ℝ ∞ (radialCoordinate b) z := by
  exact (intervalClock_smooth (-b) b).contDiffAt.comp z
    (((contDiffAt_norm ℝ hz).log (norm_ne_zero_iff.mpr hz)).comp z
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

theorem radialCoordinate_eq (b : ℝ) (x : Surface m) :
    radialCoordinate b (transverseProjection m x.val) =
      intervalClock (-b) b ((BranchSmall.quadricHandleData m).chart.symm x).1 := by
  have h := congrArg Prod.fst (transverseProjection_symm m x)
  change Real.log ‖Complex.equivRealProdCLM.symm (transverseProjection m x.val)‖ =
    ((BranchSmall.quadricHandleData m).chart.symm x).1 at h
  exact congrArg (intervalClock (-b) b) h

theorem radial_pullback_inside (b : ℝ) (x : Surface m)
    (hx : x ∈ (BranchSmall.quadricHandleData m).chart.target) :
    (BranchSmall.quadricHandleData m).radial b x =
      (radial m b x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) := by
  let H := BranchSmall.quadricHandleData m
  let f : HandleCylinder → ℝ := fun z => intervalClock (-b) b z.1
  have hf : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ f :=
    (intervalClock_smooth (-b) b).contMDiff.comp cylinder_fst_smooth
  have hi := (real_inclusion_contMDiff (parameters m)).contMDiffAt (x := x)
  have hP := (transverseProjection m).contDiff.contMDiff.contMDiffAt.comp x hi
  have hs := radialCoordinate_contDiffAt b
    (show Complex.equivRealProdCLM.symm (transverseProjection m x.val)≠0 from
      transverseCoordinate_ne_zero m x.property)
  have hD := mfderiv_comp x (hs.contMDiffAt.mdifferentiableAt (by simp))
    (hP.mdifferentiableAt (by simp))
  have hD2 := mfderiv_comp x (transverseProjection m).hasFDerivAt.differentiableAt.mdifferentiableAt
    (hi.mdifferentiableAt (by simp))
  have hlocal : f ∘ H.chart.symm = radialCoordinate b ∘
      ((transverseProjection m) ∘ (Subtype.val : Surface m → Affine (m+2))) := by
    funext y
    exact (radialCoordinate_eq m b y).symm
  have hg := H.chart.symm.contMDiffOn.contMDiffAt (H.chart.open_target.mem_nhds hx)
  have hc := mfderiv_comp x (hf.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (f ∘ H.chart.symm) x = _ at hc
  rw [hlocal,hD,hD2] at hc
  unfold AnnularHandleData.radial handlePushforwardOneForm
  rw [extendManifoldOneForm_inside hx]
  unfold manifoldPullbackOneForm manifoldMapDifferential cylinderRadialForm manifoldScalarDifferential
  rw [radial,if_pos ((nativeSheet_iff m x).mpr hx)]
  simp only [mfderiv_eq_fderiv,(transverseProjection m).fderiv] at hc
  exact hc.symm

theorem radial_zero {b : ℝ} (hb : 0<b) (x : Surface m)
    (hx : x ∉ (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band b) :
    radial m b x.val=0 := by
  by_cases hsheet : nativeSheet m x.val
  · have ht := (nativeSheet_iff m x).mp hsheet
    let z := transverseProjection m x.val
    let r : Plane → ℝ := fun u => Real.log ‖Complex.equivRealProdCLM.symm u‖
    have hrx : r z=((BranchSmall.quadricHandleData m).chart.symm x).1 := by
      exact congrArg Prod.fst (transverseProjection_symm m x)
    have hn : r z ∉ Icc (-b) b := by
      rw [hrx]
      exact (BranchSmall.quadricHandleData m).off_band_inverse b ht hx
    have hnz : Complex.equivRealProdCLM.symm z≠0 := transverseCoordinate_ne_zero m x.property
    have hr : ContinuousAt r z := ((contDiffAt_norm ℝ (n := ∞) hnz).log (norm_ne_zero_iff.mpr hnz)).continuousAt.comp
      Complex.equivRealProdCLM.symm.continuous.continuousAt
    have hd : fderiv ℝ (radialCoordinate b) z=0 := by
      simp only [mem_Icc,not_and_or,not_le] at hn
      rcases hn with hn|hn
      · have hloc : radialCoordinate b =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
          filter_upwards [hr (isOpen_Iio.mem_nhds hn)] with u hu
          exact intervalClock_zero (by linarith : -b<b) hu.le
        rw [hloc.fderiv_eq,fderiv_const_apply]
      · have hloc : radialCoordinate b =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
          filter_upwards [hr (isOpen_Ioi.mem_nhds hn)] with u hu
          exact intervalClock_one (by linarith : -b<b) hu.le
        rw [hloc.fderiv_eq,fderiv_const_apply]
    dsimp only [z] at hd
    simp only [radial,if_pos hsheet,hd,ContinuousLinearMap.zero_comp]
  · exact if_neg hsheet

theorem radial_pullback {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) (x : Surface m) :
    (BranchSmall.quadricHandleData m).radial b x =
      (radial m b x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) := by
  by_cases hx : x ∈ (BranchSmall.quadricHandleData m).chart.target
  · exact radial_pullback_inside m b x hx
  · have hband : x ∉ (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band b :=
      fun h => hx ((BranchSmall.quadricHandleData m).image_band_subset_target hbw h)
    rw [(BranchSmall.quadricHandleData m).radial_zero hb hband,radial_zero m hb x hband,
      ContinuousLinearMap.zero_comp]

theorem radial_contMDiff {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => radial m b x.val) := by
  intro x
  by_cases hx : x ∈ (BranchSmall.quadricHandleData m).chart.target
  · have hP := (transverseProjection m).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m))
    have hgrad : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
        (fun y : Surface m => (fderiv ℝ (radialCoordinate b)
          (transverseProjection m y.val)).comp (transverseProjection m)) x :=
      (((radialCoordinate_contDiffAt b (show Complex.equivRealProdCLM.symm
          (transverseProjection m x.val)≠0 from transverseCoordinate_ne_zero m x.property)).fderiv_right
          (m := ∞) (by simp)).contMDiffAt.comp x hP.contMDiffAt).clm_comp contMDiffAt_const
    apply hgrad.congr_of_eventuallyEq
    filter_upwards [(BranchSmall.quadricHandleData m).chart.open_target.mem_nhds hx] with y hy
    exact if_pos ((nativeSheet_iff m y).mpr hy)
  · have hband : x ∉ (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band b :=
      fun h => hx ((BranchSmall.quadricHandleData m).image_band_subset_target hbw h)
    apply (contMDiffAt_const (c := (0 : Affine (m+2) →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [((BranchSmall.quadricHandleData m).image_band_compact hbw).isClosed.isOpen_compl.mem_nhds hband]
      with y hy
    exact radial_zero m hb y hy

def density (b : ℝ) (z : Affine (m+2)) : Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ :=
  (radial m b z).smulRight (actualDual m z)-(actualDual m z).smulRight (radial m b z)

theorem density_contMDiff {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => density m b x.val) := by
  have hbil : ContDiff ℝ ∞ (fun q : (Affine (m+2) →L[ℝ] ℝ) × (Affine (m+2) →L[ℝ] ℝ) =>
      q.1.smulRight q.2) := contDiff_fst.smulRight contDiff_snd
  exact (hbil.contMDiff.comp ((radial_contMDiff m hb hbw).prodMk_space (actualDual_contMDiff m))).sub
    (hbil.contMDiff.comp ((actualDual_contMDiff m).prodMk_space (radial_contMDiff m hb hbw)))

theorem density_skew (b : ℝ) (x : Surface m) (u v : Affine (m+2)) :
    density m b x.val u v = -density m b x.val v u := by
  change radial m b x.val u*actualDual m x.val v-actualDual m x.val u*radial m b x.val v =
    -(radial m b x.val v*actualDual m x.val u-actualDual m x.val v*radial m b x.val u)
  ring

theorem density_semantic {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    semanticTwoForm (Subtype.val : Surface m → Affine (m+2)) (fun x => density m b x.val) =
      (BranchSmall.quadricHandleData m).density b := by
  funext x
  have hr := radial_pullback m hb hbw x
  have hd := correctedDual_pullback m x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change density m b x.val
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x u)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x v) =
    manifoldWedge ((BranchSmall.quadricHandleData m).radial b) (BranchSmall.quadricHandleData m).dual x u v
  rw [manifoldWedge_apply]
  change _ = ((BranchSmall.quadricHandleData m).radial b x u)*BranchSmall.QHandle.dual m x v-
    BranchSmall.QHandle.dual m x u*((BranchSmall.quadricHandleData m).radial b x v)
  rw [hr,hd]
  rfl

theorem density_zero {b : ℝ} (hb : 0<b) (x : Surface m)
    (hx : x ∉ (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band b) :
    density m b x.val=0 := by
  unfold density
  rw [radial_zero m hb x hx]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change (0:ℝ)*_-_*0=0
  ring

theorem density_partition_mass {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width)
    {L : Set (Surface m)}
    (hcoreL : (BranchSmall.quadricHandleData m).chart '' (BranchSmall.quadricHandleData m).core b ⊆ L)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox (Surface m))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (Surface m) L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier)) :
    partitionFormMass Boxes ρ
      (semanticTwoForm (Subtype.val : Surface m → Affine (m+2)) (fun x => density m b x.val))=1 := by
  rw [density_semantic m hb hbw]
  exact (BranchSmall.quadricHandleData m).density_mass hb hbw
    (BranchSmall.quadricHandleData_positive m) Boxes (partitionOnSubset ρ hcoreL) hρ

#check_explicit radial
#check_explicit density
end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawDensity
