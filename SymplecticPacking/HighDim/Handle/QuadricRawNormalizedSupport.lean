import SymplecticPacking.HighDim.Handle.QuadricRawNormalizedPrimitive

/-!
# Support of the quadric normalization

The normalization changes the primitive only in a compact subset of the affine interior.
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
variable (m ℓ : ℕ)

/-- A support set in the proof of relative normalization; it is not read by the native formulas. -/
def quadricNormalizedSupport : Set (Surface m) :=
  (quadricModelRawPresentation m ℓ).support ∪ tsupport (BranchSmall.quadricHandleData m).dual ∪
    (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band
      (annularCutWidth (BranchSmall.quadricHandleData m)
        (annularCutWidth (BranchSmall.quadricHandleData m) (1/16)))

 theorem quadricNormalization_outer_width :
    annularCutWidth (BranchSmall.quadricHandleData m)
      (annularCutWidth (BranchSmall.quadricHandleData m) (1/16)) <(BranchSmall.quadricHandleData m).width := by
  dsimp [annularCutWidth]
  linarith [quadricNormalization_width m]

 theorem quadricNormalizedSupport_compact : IsCompact (quadricNormalizedSupport m ℓ) :=
  ((quadricModelRawPresentation m ℓ).support_compact.union
    (BranchSmall.quadricHandleData m).dual_compact).union
    ((BranchSmall.quadricHandleData m).image_band_compact (quadricNormalization_outer_width m))

 theorem quadricNormalizedSupport_inside : quadricNormalizedSupport m ℓ⊆
    interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)) := by
  intro x hx
  rcases hx with (hD|hβ)|hband
  · exact (quadricModelRawPresentation m ℓ).support_inside hD
  · exact BranchSmall.quadricHandleData_in_exhaustion m ℓ (Or.inr hβ)
  · exact BranchSmall.quadricHandleData_in_exhaustion m ℓ (Or.inl (subset_closure
      ((BranchSmall.quadricHandleData m).image_band_subset_target (quadricNormalization_outer_width m) hband)))

variable {n : ℕ} (c : ℝ)
  {Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ}
  {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
  (hΓ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Γ q.1 q.2))
  (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Ω q.1 q.2))
  (hsk : ∀ p x u v,Ω p x u v = -Ω p x v u)
  (hdΓ : ∀ p,RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p))

include hΓ hΩ hsk hdΓ in
 theorem quadricNormalizedPrimitive_off_support (p : Moments n) (x : Surface m)
    (hx : x∉quadricNormalizedSupport m ℓ) :
    semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p) x=
      semanticOneForm Subtype.val (Γ p) x := by
  have hG := quadricRedistributedPrimitive_smooth m ℓ c hΩ hΓ
  have hGS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hG
  have hN := QuadricRawAnnular.normalModel_contMDiff m (1/16) c (quadricNormalizationMass_smooth m ℓ c hΩ)
  have hNS := semanticOneForm_family_smooth (real_inclusion_contMDiff _) hN
  have hNat (p : Moments n) (x : Surface m) (_ : x∈(BranchSmall.quadricHandleData m).chart.target) :
      ContDiffAt ℝ ∞ (fun q : Moments n × Plane => chartOneForm
        (semanticOneForm Subtype.val (QuadricRawAnnular.normalModel m (1/16) c
          (quadricNormalizationMass m ℓ c Ω) q.1)) x q.2) (p,extChartAt 𝓘(ℝ,Plane) x x) :=
    (hNS x).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target x)).mem_nhds
      ⟨mem_univ _,mem_extChartAt_target x⟩)
  have hs := annularNormalizeOf_spec (BranchSmall.quadricHandleData m) (quadricNormalization_width m)
    hGS hNat (fun p x hx => quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx)
  unfold quadricNormalizedPrimitive
  rw [QuadricRawAnnular.normalize_pullback m (quadricNormalization_width m) hGS hNS
    (fun p x hx => quadricRedistributedPrimitive_annular_exterior m ℓ c hΩ hsk p (hdΓ p) x hx),
    hs.2.1 p x (fun h => h.elim (fun hh => hx (Or.inl (Or.inr hh))) (fun hh => hx (Or.inr hh)))]
  change (quadricRedistributedPrimitive m ℓ c Γ Ω p x).comp _=(Γ p x).comp _
  rw [quadricRedistributedPrimitive_off_support m ℓ c hΩ hsk p x (fun h => hx (Or.inl (Or.inl h)))]

end SymplecticPacking.HighDim.ToricPackingStages
