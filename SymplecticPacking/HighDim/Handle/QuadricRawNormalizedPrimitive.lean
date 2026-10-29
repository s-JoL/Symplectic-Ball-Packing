import SymplecticPacking.HighDim.Handle.QuadricRawNormalizationSpec

/-!
# Smoothness and curvature of the normalized quadric primitive

The native normalized primitive is smooth, preserves the redistributed curvature, and is exactly standard on the working handle.
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
  (hΓ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Γ q.1 q.2))
  (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Ω q.1 q.2))
  (hsk : ∀ p x u v,Ω p x u v = -Ω p x v u)
  (hdΓ : ∀ p,RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p))

include hΓ hΩ hsk hdΓ

theorem quadricNormalizedPrimitive_smooth :
    ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : Moments n × Surface m => quadricNormalizedPrimitive m ℓ c Γ Ω q.1 q.2) := by
  have hG := quadricRedistributedPrimitive_smooth m ℓ c hΩ hΓ
  have hGS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hG
  have hN := QuadricRawAnnular.normalModel_contMDiff m (1/16) c (quadricNormalizationMass_smooth m ℓ c hΩ)
  have hNS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hN
  exact QuadricRawAnnular.normalize_contMDiff m (quadricNormalization_width m) hGS hNS
    (fun p x hx => quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx) hG

theorem quadricNormalizedPrimitive_exterior (p : Moments n) :
    manifoldExteriorOneForm (semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p))=
      semanticTwoForm Subtype.val (Ω p+(quadricModelRawPresentation m ℓ).calibratedDefect
        (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val)
        (quadricNormalizationRemoved m ℓ c Ω p)) := by
  have hG := quadricRedistributedPrimitive_smooth m ℓ c hΩ hΓ
  have hGS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hG
  have hN := QuadricRawAnnular.normalModel_contMDiff m (1/16) c (quadricNormalizationMass_smooth m ℓ c hΩ)
  have hNS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hN
  have hs := QuadricRawAnnular.normalize_spec m (quadricNormalization_width m) hGS hNS
    (fun p x hx => quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx)
  funext x
  exact (hs.1 p x).trans (congrArg (fun A => A x)
    (quadricRedistributedPrimitive_exterior m ℓ c hΩ hsk p (hdΓ p)))

theorem quadricNormalizedPrimitive_on_handle (p : Moments n) (x : Surface m)
    (hx : x∈annularNormalizeRegion (BranchSmall.quadricHandleData m) (1/16)) :
    semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p) x=
      c • curveFSPrimitive (parameters m) (1/Real.pi) x+
        (intervalClock (-(1/16)) (1/16) ((BranchSmall.quadricHandleData m).chart.symm x).1*
          quadricNormalizationMass m ℓ c Ω p) • (BranchSmall.quadricHandleData m).dual x := by
  have hG := quadricRedistributedPrimitive_smooth m ℓ c hΩ hΓ
  have hGS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hG
  have hN := QuadricRawAnnular.normalModel_contMDiff m (1/16) c (quadricNormalizationMass_smooth m ℓ c hΩ)
  have hNS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hN
  have hs := QuadricRawAnnular.normalize_spec m (quadricNormalization_width m) hGS hNS
    (fun p x hx => quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx)
  rw [show semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p) x=
      semanticOneForm Subtype.val (QuadricRawAnnular.normalModel m (1/16) c
        (quadricNormalizationMass m ℓ c Ω) p) x from hs.2 p x hx,
    QuadricRawAnnular.normalModel_pullback m (1/16) c _ p x hx.1,
    (BranchSmall.quadricHandleData m).clockPrimitive_eq (1/16) hx.1,smul_smul,mul_comm]

theorem quadricNormalizedPrimitive_annular_exterior (p : Moments n) (x : Surface m)
    (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    manifoldExteriorOneForm (semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p)) x=
      c • curveFSForm (parameters m) (1/Real.pi) x+
        quadricNormalizationMass m ℓ c Ω p • (BranchSmall.quadricHandleData m).density (1/16) x := by
  have hn := congrArg (fun f => f x) (quadricNormalizedPrimitive_exterior m ℓ c hΓ hΩ hsk hdΓ p)
  have hg := congrArg (fun f => f x) (quadricRedistributedPrimitive_exterior m ℓ c hΩ hsk p (hdΓ p))
  exact hn.trans (hg.symm.trans ((quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx).trans
    (QuadricRawAnnular.normalModel_exterior m (1/16) c _ p x hx)))

end SymplecticPacking.HighDim.ToricPackingStages
