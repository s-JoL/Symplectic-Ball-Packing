import SymplecticPacking.HighDim.Handle.QuadricRawNormalization
import SymplecticPacking.HighDim.Handle.QuadricRawGlobalCover

/-!
# Correctness of the quadric primitive correction

Correctness of the calibrated primitive correction, with no target-primitive assumptions.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
variable (m ℓ : ℕ) {n : ℕ} (c : ℝ)
  {Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ}
  {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
  (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Ω q.1 q.2))
  (hsk : ∀ p x u v,Ω p x u v = -Ω p x v u)

include hsk in
theorem quadricNormalizationRemoved_skew (p : Moments n) (x : Surface m) (u v : Affine (m+2)) :
    quadricNormalizationRemoved m ℓ c Ω p x u v = -quadricNormalizationRemoved m ℓ c Ω p x v u := by
  have hΛ := BranchSmall.RawQuadric.ambientFSForm_skew (1/Real.pi) x.val u v
  change quadricNormalizationCutoff m ℓ x*(Ω p x u v-c*quadricReferenceForm m x u v) =
    -(quadricNormalizationCutoff m ℓ x*(Ω p x v u-c*quadricReferenceForm m x v u))
  change quadricReferenceForm m x u v = -quadricReferenceForm m x v u at hΛ
  rw [hsk p x u v,hΛ]
  ring

include hΩ hsk in
theorem quadricRedistributedPrimitive_isPrimitive (p : Moments n)
    (hΓ : RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p)) :
    RawIsPrimitive (Subtype.val : Surface m → Affine (m+2))
      (Ω p+(quadricModelRawPresentation m ℓ).calibratedDefect
        (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
        (quadricNormalizationRemoved m ℓ c Ω p)) (quadricRedistributedPrimitive m ℓ c Γ Ω p) := by
  have hΓD : RawIsPrimitive (quadricModelRawPresentation m ℓ).inclusion (Ω p) (Γ p) := by
    rw [quadricModelRawPresentation_inclusion]
    exact hΓ
  have hr := (quadricModelRawPresentation m ℓ).calibratedPrimitive_spec
    (quadricModelRawPresentation_geometry m ℓ) hΓD
    (QuadricRawDensity.density_contMDiff m (by norm_num) (quadricNormalization_width m))
    ((quadricNormalizationRemoved_smooth m ℓ c hΩ).comp (contMDiff_const.prodMk contMDiff_id))
    (QuadricRawDensity.density_skew m (1/16)) (quadricNormalizationRemoved_skew m ℓ c hsk p)
    (projectionDomain_compact _ _) (projectionDomain_compact _ _)
    (quadricRawDensity_zero_off_core m ℓ (by norm_num) (quadricNormalization_width m))
    (quadricNormalizationRemoved_zero m ℓ c p)
    (by rw [union_self]; exact quadricModelRawPresentation_cover m ℓ)
    (quadricRawDensity_formMass m ℓ (by norm_num) (quadricNormalization_width m))
    (quadricModelRawPresentation_calibration_ne_zero m ℓ)
  rw [quadricModelRawPresentation_inclusion] at hr
  exact hr

include hsk in
theorem quadricRedistributedForm_skew (p : Moments n) (x : Surface m) (u v : Affine (m+2)) :
    (Ω p+(quadricModelRawPresentation m ℓ).calibratedDefect
      (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
      (quadricNormalizationRemoved m ℓ c Ω p)) x u v =
    -(Ω p+(quadricModelRawPresentation m ℓ).calibratedDefect
      (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
      (quadricNormalizationRemoved m ℓ c Ω p)) x v u := by
  change Ω p x u v+(quadricNormalizationMass m ℓ c Ω p*QuadricRawDensity.density m (1/16) x.val u v-
    quadricNormalizationRemoved m ℓ c Ω p x u v) =
    -(Ω p x v u+(quadricNormalizationMass m ℓ c Ω p*QuadricRawDensity.density m (1/16) x.val v u-
      quadricNormalizationRemoved m ℓ c Ω p x v u))
  rw [hsk p x u v,QuadricRawDensity.density_skew m (1/16) x u v,
    quadricNormalizationRemoved_skew m ℓ c hsk p x u v]
  ring

include hΩ hsk in
theorem quadricRedistributedPrimitive_exterior (p : Moments n)
    (hΓ : RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p)) :
    manifoldExteriorOneForm (semanticOneForm Subtype.val (quadricRedistributedPrimitive m ℓ c Γ Ω p))=
      semanticTwoForm Subtype.val (Ω p+(quadricModelRawPresentation m ℓ).calibratedDefect
        (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
        (quadricNormalizationRemoved m ℓ c Ω p)) :=
  (quadricRedistributedPrimitive_isPrimitive m ℓ c hΩ hsk p hΓ).semantic_exterior
    (real_inclusion_contMDiff _) (quadricRedistributedForm_skew m ℓ c hsk p) (quadric_raw_global_cover _)

include hΩ hsk in
theorem quadricRedistributedPrimitive_annular_exterior (p : Moments n)
    (hΓ : RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p))
    (x : Surface m) (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    manifoldExteriorOneForm (semanticOneForm Subtype.val (quadricRedistributedPrimitive m ℓ c Γ Ω p)) x=
      manifoldExteriorOneForm (semanticOneForm Subtype.val (QuadricRawAnnular.normalModel m (1/16) c
        (quadricNormalizationMass m ℓ c Ω) p)) x := by
  rw [quadricRedistributedPrimitive_exterior m ℓ c hΩ hsk p hΓ,
    QuadricRawAnnular.normalModel_exterior m (1/16) c _ p x hx,
    ←quadricReferenceForm_semantic,
    ←QuadricRawDensity.density_semantic m (by norm_num) (quadricNormalization_width m)]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω p x _ _+(quadricNormalizationMass m ℓ c Ω p*QuadricRawDensity.density m (1/16) x.val _ _-
    quadricNormalizationCutoff m ℓ x*(Ω p x _ _-c*quadricReferenceForm m x _ _)) =
      c*quadricReferenceForm m x _ _+
        quadricNormalizationMass m ℓ c Ω p*QuadricRawDensity.density m (1/16) x.val _ _
  rw [quadricNormalizationCutoff_handle m ℓ x hx]
  ring

include hΩ hsk in
theorem quadricRedistributedPrimitive_off_support (p : Moments n) (x : Surface m)
    (hx : x∉(quadricModelRawPresentation m ℓ).support) :
    quadricRedistributedPrimitive m ℓ c Γ Ω p x=Γ p x := by
  have hr := (quadricModelRawPresentation m ℓ).calibratedCorrection_spec
    (quadricModelRawPresentation_geometry m ℓ)
    (QuadricRawDensity.density_contMDiff m (by norm_num) (quadricNormalization_width m))
    ((quadricNormalizationRemoved_smooth m ℓ c hΩ).comp (contMDiff_const.prodMk contMDiff_id))
    (QuadricRawDensity.density_skew m (1/16)) (quadricNormalizationRemoved_skew m ℓ c hsk p)
    (projectionDomain_compact _ _) (projectionDomain_compact _ _)
    (quadricRawDensity_zero_off_core m ℓ (by norm_num) (quadricNormalization_width m))
    (quadricNormalizationRemoved_zero m ℓ c p)
    (by rw [union_self]; exact quadricModelRawPresentation_cover m ℓ)
    (quadricRawDensity_formMass m ℓ (by norm_num) (quadricNormalization_width m))
    (quadricModelRawPresentation_calibration_ne_zero m ℓ)
  change Γ p x+_ = Γ p x
  have hz := hr.2 x hx
  change (quadricModelRawPresentation m ℓ).calibratedCorrection
    (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
    (quadricNormalizationRemoved m ℓ c Ω p) x=0 at hz
  rw [hz,add_zero]

end SymplecticPacking.HighDim.ToricPackingStages
