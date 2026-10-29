import SymplecticPacking.HighDim.Handle.RawAmbientExterior
import SymplecticPacking.HighDim.Handle.QuadricNormalizationMassBounds
import SymplecticPacking.HighDim.Handle.QuadricCollarBounds

/-!
# Primitive and collar budget of the scalar quadric families

Scalar-family primitive and collar budget, covering the small and mixed quadric models.
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
local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _
variable (m ℓ : ℕ) {n : ℕ} (κ : Moments n → ℝ)

 theorem quadricScalar_isPrimitive (p : Moments n) :
    RawIsPrimitive (Subtype.val : Surface m → Affine (m+2))
      (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val)
      (fun x : Surface m => BranchSmall.RawQuadric.scaledPrimitive (1/Real.pi) κ p x.val) := by
  have hΓ : ContDiff ℝ ∞ (BranchSmall.RawQuadric.scaledPrimitive (m := m+2) (1/Real.pi) κ p) :=
    (contDiff_const (c := κ p)).smul (ambientFSPrimitive_smooth (1/Real.pi))
  have hd := ambient_primitive_restriction (real_inclusion_contMDiff (parameters m)) hΓ
  have he : (fun x : Surface m => euclideanExteriorOneForm
      (BranchSmall.RawQuadric.scaledPrimitive (1/Real.pi) κ p) x.val)=
      fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val := by
    funext x
    exact BranchSmall.RawQuadric.scaledPrimitive_exterior (1/Real.pi) κ p x.val
  rwa [he] at hd

 theorem quadricScalar_semantic (p : Moments n) :
    semanticTwoForm Subtype.val
      (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val)=
      κ p • curveFSForm (parameters m) (1/Real.pi) := by
  funext x
  exact (BranchSmall.RawQuadric.scaledForm_eq_raw (parameters m) (1/Real.pi) κ p x).symm

 theorem quadricScalar_collar_bound {d : ℝ} (hd : 0<d) (hd1 : d≤1)
    (hℓ : 64*((2:ℝ)^(m+2)*(m+2+2))/d≤ℓ)
    (p : Moments n) (hκ0 : 0≤κ p) (hκ1 : κ p≤1) :
    compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (semanticTwoForm Subtype.val (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val))-
    compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ-2))
      (semanticTwoForm Subtype.val (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val))
      ≤(11*d/64)/32 := by
  rw [quadricScalar_semantic m κ p,compactSurfaceFormIntegral_smul,compactSurfaceFormIntegral_smul]
  have hout := compact_area_le_degree (parameters m) (one_div_pos.mpr Real.pi_pos)
    (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
  have hout' : compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (curveFSForm (parameters m) (1/Real.pi))≤(2:ℝ)^(m+2) := by
    convert hout using 1 <;> field_simp
  have hℓ' : 64*((2:ℝ)^(m+2)*((m+2:ℕ)+2))/d≤ℓ := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hℓ
  have hin := quadric_collar_inner_defect (parameters m) (by omega : 2 ≤ m + 2) hd hd1 hℓ'
  rw [quadric_exhaustion_inner_radius (parameters m)
    (quadric_collar_level_two (by omega : 2 ≤ m + 2) hd hd1 hℓ')] at hin
  have hdiff : compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (curveFSForm (parameters m) (1/Real.pi))-
      compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ-2))
      (curveFSForm (parameters m) (1/Real.pi))≤d/65536 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hκ0
  have hup := mul_le_mul_of_nonneg_right hκ1 (show 0≤d/65536 by positivity)
  nlinarith

 theorem quadricScalar_handleMass_loss {d c : ℝ} (hd : 0<d) (hd1 : d≤1)
    (hℓ : 64*((2:ℝ)^(m+2)*(m+2+2))/d≤ℓ)
    (hc : 0≤c) (hcb : c≤(11*d/64)/(32*(2:ℝ)^(m+2)))
    (hκ : ContDiff ℝ ∞ κ) (p : Moments n) (hκ0 : 0≤κ p) (hκ1 : κ p≤1) :
    compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (semanticTwoForm Subtype.val (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val))-
      (11*d/64)/16≤quadricNormalizationMass m ℓ c
        (fun p (x : Surface m) => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val) p := by
  have hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val) :=
    (BranchSmall.RawQuadric.scaledForm_restriction_contMDiff (parameters m) (1/Real.pi) hκ).comp
      (contMDiff_const.prodMk contMDiff_id)
  exact quadricNormalizationMass_loss m ℓ hc hcb p hΩ
    (fun x u v => BranchSmall.RawQuadric.scaledForm_skew (1/Real.pi) κ p x.val u v)
    (fun _ => κ p) contMDiff_const
    (fun x => congrArg (fun F => F x) (quadricScalar_semantic m κ p)) (fun _ _ => hκ0)
    (quadricScalar_collar_bound m ℓ κ hd hd1 hℓ p hκ0 hκ1)

 theorem quadricScalar_outer_reserve {d : ℝ} (hd : 0<d) (hd1 : d≤1)
    (hℓ : 64*((2:ℝ)^(m+2)*(m+2+2))/d≤ℓ)
    (p : Moments n) (hκ0 : 0≤κ p) (hκ1 : κ p≤1) (hmin : 2*d≤κ p*(2:ℝ)^(m+2)) :
    (11*d/64)/16≤compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (semanticTwoForm Subtype.val (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val)) := by
  rw [quadricScalar_semantic m κ p,compactSurfaceFormIntegral_smul]
  have hℓ' : 64*((2:ℝ)^(m+2)*((m+2:ℕ)+2))/d≤ℓ := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hℓ
  have hin := quadric_collar_inner_defect (parameters m) (by omega : 2 ≤ m + 2) hd hd1 hℓ'
  have hsub : projectionDomain (parameters m) (exhaustionRadius (parameters m) (ℓ-2))⊆
      projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) := by
    intro x hx
    change ‖x.val.1‖≤exhaustionRadius (parameters m) (ℓ-2) at hx
    change ‖x.val.1‖≤exhaustionRadius (parameters m) ℓ
    have hn : ((ℓ-2:ℕ):ℝ)≤ℓ := by exact_mod_cast Nat.sub_le ℓ 2
    dsimp [exhaustionRadius] at hx ⊢
    linarith
  have hmono := compactSurfaceFormIntegral_mono
    (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) (ℓ-2)))
    (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ)) hsub
    (positivePlaneTransitions _) (curveFSForm_smooth (parameters m) (1/Real.pi))
    (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun b y hy => (curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) b hy).le)
  have htail : (2:ℝ)^(m+2)-compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
      (curveFSForm (parameters m) (1/Real.pi))≤d/65536 := by linarith
  have hmul := mul_le_mul_of_nonneg_left htail hκ0
  have hup := mul_le_mul_of_nonneg_right hκ1 (show 0≤d/65536 by positivity)
  nlinarith

end SymplecticPacking.HighDim.ToricPackingStages
