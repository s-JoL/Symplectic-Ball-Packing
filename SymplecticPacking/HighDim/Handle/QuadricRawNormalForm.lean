import SymplecticPacking.HighDim.Handle.QuadricRawAnnularNormalize
import SymplecticPacking.BranchSmall.QuadricRawForms

/-!
# Annular normal form of the quadric handle

A native FS background plus the handle clock gives the annular normal form.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
open Set Function Filter Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (m : ℕ) {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def normalModel (b c : ℝ) (H : P → ℝ) (p : P) (x : Surface m) : Affine (m+2) →L[ℝ] ℝ :=
  c • ambientFSPrimitive (1/Real.pi) x.val+
    (H p*QuadricRawDensity.radialCoordinate b (QuadricRawDual.transverseProjection m x.val)) •
      QuadricRawDual.actualDual m x.val

theorem radialScalar_contMDiff (b : ℝ) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞
      (fun x : Surface m => QuadricRawDensity.radialCoordinate b (QuadricRawDual.transverseProjection m x.val)) := by
  intro x
  have hf : ContDiffAt ℝ ∞ (QuadricRawDensity.radialCoordinate b)
      (QuadricRawDual.transverseProjection m x.val) := QuadricRawDensity.radialCoordinate_contDiffAt b
    (show Complex.equivRealProdCLM.symm (QuadricRawDual.transverseProjection m x.val)≠0 from
      transverseCoordinate_ne_zero m x.property)
  have hfc : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (QuadricRawDensity.radialCoordinate b)
      (QuadricRawDual.transverseProjection m x.val) := hf.contMDiffAt
  have hP : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞
      ((QuadricRawDual.transverseProjection m) ∘ (Subtype.val : Surface m → Affine (m+2))) x :=
    (QuadricRawDual.transverseProjection m).contDiff.contMDiff.contMDiffAt.comp x
      ((real_inclusion_contMDiff (parameters m)).contMDiffAt (x := x))
  have h := hfc.comp x hP
  exact h

theorem normalModel_contMDiff (b c : ℝ) {H : P → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => normalModel m b c H q.1 q.2) := by
  have hF : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => ambientFSPrimitive (1/Real.pi) q.2.val) :=
    (ambientFSPrimitive_smooth (1/Real.pi)).contMDiff.comp
      ((real_inclusion_contMDiff (parameters m)).comp contMDiff_snd)
  have hs : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × Surface m => H q.1*
        QuadricRawDensity.radialCoordinate b (QuadricRawDual.transverseProjection m q.2.val)) :=
    (hH.contMDiff.comp (contMDiff_fst : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,P) ∞
      (Prod.fst : P × Surface m → P))).mul ((radialScalar_contMDiff m b).comp contMDiff_snd)
  have hc : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun _ : P × Surface m => c) := contMDiff_const
  exact (hc.smul hF).add
    (hs.smul ((QuadricRawDual.actualDual_contMDiff m).comp contMDiff_snd))

theorem normalModel_pullback (b c : ℝ) (H : P → ℝ) (p : P) (x : Surface m)
    (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    semanticOneForm Subtype.val (normalModel m b c H p) x=
      c • curveFSPrimitive (parameters m) (1/Real.pi) x+
        H p • (BranchSmall.quadricHandleData m).clockPrimitive b x := by
  rw [(BranchSmall.quadricHandleData m).clockPrimitive_eq b hx,
    BranchSmall.RawQuadric.curveFSPrimitive_eq_raw]
  have hβ := QuadricRawDual.correctedDual_pullback m x
  change (BranchSmall.quadricHandleData m).dual x=
    (QuadricRawDual.actualDual m x.val).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) at hβ
  rw [hβ]
  apply ContinuousLinearMap.ext
  intro v
  let w : Affine (m+2) := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2))
    (Subtype.val : Surface m → Affine (m+2)) x v
  change c*ambientFSPrimitive (1/Real.pi) x.val w+
    (H p*QuadricRawDensity.radialCoordinate b (QuadricRawDual.transverseProjection m x.val))*
      QuadricRawDual.actualDual m x.val w =
    c*ambientFSPrimitive (1/Real.pi) x.val w+
      H p*(intervalClock (-b) b ((BranchSmall.quadricHandleData m).chart.symm x).1*
        QuadricRawDual.actualDual m x.val w)
  rw [QuadricRawDensity.radialCoordinate_eq m b x]
  ring

theorem normalModel_exterior (b c : ℝ) (H : P → ℝ) (p : P) (x : Surface m)
    (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    manifoldExteriorOneForm (semanticOneForm Subtype.val (normalModel m b c H p)) x=
      c • curveFSForm (parameters m) (1/Real.pi) x+
        H p • (BranchSmall.quadricHandleData m).density b x := by
  have he : semanticOneForm Subtype.val (normalModel m b c H p) =ᶠ[𝓝 x]
      c • curveFSPrimitive (parameters m) (1/Real.pi)+
        H p • (BranchSmall.quadricHandleData m).clockPrimitive b := by
    filter_upwards [(BranchSmall.quadricHandleData m).chart.open_target.mem_nhds hx] with y hy
    exact normalModel_pullback m b c H p y hy
  rw [manifoldExteriorOneForm_congr_of_eventuallyEq he]
  have hf := (curveFSPrimitive_smooth (parameters m) (1/Real.pi)).spatial_smooth (0:ℝ) x
    (mem_extChartAt_target x)
  have hc := (BranchSmall.quadricHandleData m).clockPrimitive_smooth b hx
  have hcf : ContDiffAt ℝ ∞ (chartOneForm (c • curveFSPrimitive (parameters m) (1/Real.pi)) x)
      (extChartAt 𝓘(ℝ,Plane) x x) := by
    rw [show chartOneForm (c • curveFSPrimitive (parameters m) (1/Real.pi)) x=
      fun z => c • chartOneForm (curveFSPrimitive (parameters m) (1/Real.pi)) x z from
        funext (chartOneForm_smul c _ x)]
    exact (contDiffAt_const (c := c)).smul hf
  have hh : ContDiffAt ℝ ∞ (chartOneForm (H p • (BranchSmall.quadricHandleData m).clockPrimitive b) x)
      (extChartAt 𝓘(ℝ,Plane) x x) := by
    rw [show chartOneForm (H p • (BranchSmall.quadricHandleData m).clockPrimitive b) x=
      fun z => H p • chartOneForm ((BranchSmall.quadricHandleData m).clockPrimitive b) x z from
        funext (chartOneForm_smul (H p) _ x)]
    exact (contDiffAt_const (c := H p)).smul hc
  rw [manifoldExteriorOneForm_add_at hcf hh,manifoldExteriorOneForm_smul_at c hf,
    manifoldExteriorOneForm_smul_at (H p) hc,curveFSPrimitive_exterior,
    (BranchSmall.quadricHandleData m).clockPrimitive_exterior b hx]

#check_explicit normalModel
end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
