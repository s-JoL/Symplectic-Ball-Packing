import SymplecticPacking.HighDim.Handle.QuadricRawNormalization
import SymplecticPacking.HighDim.Handle.QuadricCutAreaBounds
import SymplecticPacking.HighDim.Handle.RawCutoffMass

/-!
# Mass bounds for the quadric collar cutoff

Finite mass bounds for the collar cutoff, valid for scalar and varying physical densities.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _
variable (m ℓ : ℕ)

def quadricNormalizationCutMass (Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) : ℝ :=
  (quadricModelRawPresentation m ℓ).calibratedMass (rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω)

 theorem quadricNormalizationCutoff_nonneg (x : Surface m) : 0≤quadricNormalizationCutoff m ℓ x :=
  sub_nonneg.mpr (quadricBoundaryCutoff_le_one _ _ x)

 theorem quadricNormalizationCutoff_le_one (x : Surface m) : quadricNormalizationCutoff m ℓ x≤1 := by
  have h := quadricBoundaryCutoff_nonneg
    (exhaustionRadius (parameters m) ℓ-2) (exhaustionRadius (parameters m) ℓ-1) x
  change 1-quadricBoundaryCutoff _ _ x≤1
  linarith

 theorem quadricNormalizationCutoff_inner (x : Surface m)
    (hx : x∈projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ-2)) :
    quadricNormalizationCutoff m ℓ x=1 := by
  have hR := quadricFiniteSupportRadius_exhaustion m ℓ
  have hfour := quadricFiniteSupportRadius_four m ℓ
  unfold quadricNormalizationCutoff
  rw [quadricBoundaryCutoff_zero (by linarith) (by linarith) x hx,sub_zero]

 theorem semanticTwoForm_cut (Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) :
    semanticTwoForm Subtype.val (rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω)=
      fun x => quadricNormalizationCutoff m ℓ x • semanticTwoForm Subtype.val Ω x := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

 theorem quadricNormalizationCutMass_partition
    {Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox (Surface m))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (Surface m)
      (projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)))
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier)) :
    quadricNormalizationCutMass m ℓ Ω=partitionFormMass Boxes ρ
      (fun x => quadricNormalizationCutoff m ℓ x • semanticTwoForm Subtype.val Ω x) := by
  let : MulActionWithZero ℝ (Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
  have hcut : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞
      (rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω) :=
    (quadricNormalizationCutoff_smooth m ℓ).smul hΩ
  have hscut (x : Surface m) (u v : Affine (m+2)) :
      rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω x u v =
        -rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω x v u := by
    change quadricNormalizationCutoff m ℓ x*Ω x u v= -(quadricNormalizationCutoff m ℓ x*Ω x v u)
    rw [hsk,mul_neg]
  have hz (x : Surface m) (hx : x∉projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)) :
      rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω x=0 :=
    rawCutoffForm_zero _ Ω (quadricNormalizationCutoff_zero m ℓ x hx)
  have hm := quadricModelRawPresentation_mass_eq m ℓ hcut hscut hz
  have hK := projectionDomain_compact (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)
  have hi := compactSurfaceFormIntegral_eq hK (positivePlaneTransitions _) Boxes ρ hρ
    (semanticTwoForm_smooth (real_inclusion_contMDiff _) hcut) (fun x u v => hscut x _ _)
  have hind : (projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)).indicator
      (semanticTwoForm Subtype.val (rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω))=
      semanticTwoForm Subtype.val (rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω) := by
    funext x
    by_cases hx : x∈projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,semanticTwoForm_zero_at (Subtype.val : Surface m → Affine (m+2))
        (Ω := rawCutoffForm (quadricNormalizationCutoff m ℓ) Ω) (hz x hx)]
  rw [restrictedPartitionFormMass_eq_indicator _ _ hK.measurableSet,hind,semanticTwoForm_cut] at hi
  exact hm.trans hi

 theorem quadricNormalization_referenceCut_le :
    quadricNormalizationCutMass m ℓ (quadricReferenceForm m)≤(2:ℝ)^(m+2) := by
  classical
  let hK := projectionDomain_compact (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)
  let Boxes := fun B : compactSurfaceBoxes hK => B.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  rw [quadricNormalizationCutMass_partition m ℓ (quadricReferenceForm_smooth m)
    (fun x u v => BranchSmall.RawQuadric.ambientFSForm_skew (1/Real.pi) x.val u v) Boxes ρ hρ,
    quadricReferenceForm_semantic]
  have hu := cutoff_integral_le_outer hK (positivePlaneTransitions _) Subset.rfl Boxes ρ hρ
    (curveFSForm_smooth (parameters m) (1/Real.pi)) (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun c y hy => (curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy).le)
    (quadricNormalizationCutoff_smooth m ℓ) (quadricNormalizationCutoff_le_one m ℓ)
    (quadricNormalizationCutoff_zero m ℓ)
  apply hu.trans
  have hd := compact_area_le_degree (parameters m) (one_div_pos.mpr Real.pi_pos) hK
  convert hd using 1 <;> field_simp

 theorem quadricNormalization_physicalCut_ge_inner
    {Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (κ : Surface m → ℝ) (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ)
    (he : ∀ x,semanticTwoForm Subtype.val Ω x=κ x • curveFSForm (parameters m) (1/Real.pi) x)
    (hκ0 : ∀ x∈projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ),0≤κ x) :
    compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ-2))
      (semanticTwoForm Subtype.val Ω) ≤ quadricNormalizationCutMass m ℓ Ω := by
  classical
  let hK := projectionDomain_compact (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)
  let Boxes := fun B : compactSurfaceBoxes hK => B.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  have hR := quadricFiniteSupportRadius_exhaustion m ℓ
  have hsub : projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ-2)⊆
      projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ) := by
    intro x hx
    change ‖x.val.1‖≤_ at hx ⊢
    linarith
  rw [quadricNormalizationCutMass_partition m ℓ hΩ hsk Boxes ρ hρ,funext he]
  have heq : (fun x : Surface m => quadricNormalizationCutoff m ℓ x •
      (κ x • curveFSForm (parameters m) (1/Real.pi) x))=
      fun x => (quadricNormalizationCutoff m ℓ x*κ x) • curveFSForm (parameters m) (1/Real.pi) x := by
    funext x
    exact smul_smul (quadricNormalizationCutoff m ℓ x) (κ x)
      (curveFSForm (parameters m) (1/Real.pi) x)
  rw [heq]
  exact cutoff_weighted_mass_ge_inner (projectionDomain_compact _ _) (positivePlaneTransitions _) hsub Boxes ρ hρ
    (curveFSForm_smooth (parameters m) (1/Real.pi)) (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun c y hy => (curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy).le)
    (quadricNormalizationCutoff_smooth m ℓ) hκ (quadricNormalizationCutoff_nonneg m ℓ)
    (quadricNormalizationCutoff_inner m ℓ) (quadricNormalizationCutoff_zero m ℓ) hκ0

 theorem quadricNormalizationMass_formula {n : ℕ} (c : ℝ)
    {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ} (p : Moments n)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (Ω p)) :
    quadricNormalizationMass m ℓ c Ω p=quadricNormalizationCutMass m ℓ (Ω p)-
      c*quadricNormalizationCutMass m ℓ (quadricReferenceForm m) :=
  calibrated_removed_mass (quadricModelRawPresentation m ℓ)
    (quadricModelRawPresentation_geometry m ℓ) (quadricNormalizationCutoff_smooth m ℓ) c
    (quadricReferenceForm_smooth m) p hΩ (projectionDomain_compact _ _)
    (quadricNormalizationCutoff_zero m ℓ)

 theorem quadricNormalizationMass_loss {n : ℕ} {c reserve outer : ℝ}
    (hc : 0≤c) (hcb : c≤reserve/(32*(2:ℝ)^(m+2)))
    {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ} (p : Moments n)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (Ω p))
    (hsk : ∀ x u v,Ω p x u v = -Ω p x v u)
    (κ : Surface m → ℝ) (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ)
    (he : ∀ x,semanticTwoForm Subtype.val (Ω p) x=κ x • curveFSForm (parameters m) (1/Real.pi) x)
    (hκ0 : ∀ x∈projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ),0≤κ x)
    (htail : outer-compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ-2))
      (semanticTwoForm Subtype.val (Ω p))≤reserve/32) :
    outer-reserve/16≤quadricNormalizationMass m ℓ c Ω p := by
  have hbg : c*quadricNormalizationCutMass m ℓ (quadricReferenceForm m)≤reserve/32 := by
    calc
      _≤c*(2:ℝ)^(m+2) := mul_le_mul_of_nonneg_left (quadricNormalization_referenceCut_le m ℓ) hc
      _≤(reserve/(32*(2:ℝ)^(m+2)))*(2:ℝ)^(m+2) := mul_le_mul_of_nonneg_right hcb (by positivity)
      _=reserve/32 := by field_simp
  exact handleMass_loss_budget (quadricNormalizationMass_formula m ℓ c p hΩ)
    (quadricNormalization_physicalCut_ge_inner m ℓ hΩ hsk κ hκ he hκ0) htail hbg

end SymplecticPacking.HighDim.ToricPackingStages
