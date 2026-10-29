import SymplecticPacking.HighDim.Handle.QuadricRawNormalizedPrimitive

/-!
# Positivity of the normalized quadric primitive

Positivity is a pointwise convex combination plus the nonnegative handle density.
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

include hΓ hΩ hsk hdΓ in
theorem quadricNormalizedPrimitive_positive (hc : 0<c) (p : Moments n)
    (hH : 0≤quadricNormalizationMass m ℓ c Ω p) (b : Surface m) (y : Plane)
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) b).target)
    (hphysical : 0<chartTwoForm (semanticTwoForm Subtype.val (Ω p)) b y (1,0) (0,1)) :
    0<chartTwoForm (manifoldExteriorOneForm
      (semanticOneForm Subtype.val (quadricNormalizedPrimitive m ℓ c Γ Ω p))) b y (1,0) (0,1) := by
  rw [quadricNormalizedPrimitive_exterior m ℓ c hΓ hΩ hsk hdΓ p]
  let x := (extChartAt 𝓘(ℝ,Plane) b).symm y
  let u : Affine (m+2) := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2))
    (Subtype.val : Surface m → Affine (m+2)) x ((chartDifferential (E := Plane) b x).inverse (1,0))
  let v : Affine (m+2) := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2))
    (Subtype.val : Surface m → Affine (m+2)) x ((chartDifferential (E := Plane) b x).inverse (0,1))
  have hΛ := curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) b hy
  rw [←quadricReferenceForm_semantic m] at hΛ
  have hη := (BranchSmall.quadricHandleData m).density_nonnegative (by norm_num : (0:ℝ)<1/16)
    (quadricNormalization_width m) (BranchSmall.quadricHandleData_positive m) b hy
  rw [←QuadricRawDensity.density_semantic m (by norm_num) (quadricNormalization_width m)] at hη
  change 0<Ω p x u v at hphysical
  change 0<quadricReferenceForm m x u v at hΛ
  change 0≤QuadricRawDensity.density m (1/16) x.val u v at hη
  have hχ0 : 0≤quadricNormalizationCutoff m ℓ x :=
    sub_nonneg.mpr (quadricBoundaryCutoff_le_one _ _ x)
  have hχ1 : quadricNormalizationCutoff m ℓ x≤1 := by
    have := quadricBoundaryCutoff_nonneg
      (exhaustionRadius (parameters m) ℓ-2) (exhaustionRadius (parameters m) ℓ-1) x
    change 1-quadricBoundaryCutoff _ _ x≤1
    linarith
  have hp := cutoff_background_positive hχ0 hχ1 hphysical (mul_pos hc hΛ)
  have hn := mul_nonneg hH hη
  change 0<Ω p x u v+(quadricNormalizationMass m ℓ c Ω p*QuadricRawDensity.density m (1/16) x.val u v-
    quadricNormalizationCutoff m ℓ x*(Ω p x u v-c*quadricReferenceForm m x u v))
  linarith

end SymplecticPacking.HighDim.ToricPackingStages
