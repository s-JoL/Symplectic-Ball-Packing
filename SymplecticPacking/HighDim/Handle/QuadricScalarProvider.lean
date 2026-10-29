import SymplecticPacking.HighDim.Handle.QuadricNormalizationSpec
import SymplecticPacking.HighDim.Handle.QuadricScalarNormalization

/-!
# Normalized providers for the scalar quadric families

A complete normalized provider for each scalar quadric family.
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

variable (m n q ℓ : ℕ) (Δ : Polytope n q) (κ : Moments n → ℝ) (floor d : ℝ)
local notation "T" => quadricScalarRawModel m n q ℓ Δ κ floor
local notation "rsv" => 11*d/64

def quadricScalarOuterArea (p : Moments n) : ℝ :=
  compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ))
    (semanticTwoForm Subtype.val (fun x : Surface m => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val))

theorem quadricScalar_provider (hκ : ContDiff ℝ ∞ κ) (hf : 0<floor) (hd : 0<d) (hd1 : d≤1)
    (hℓ : 64*((2:ℝ)^(m+2)*(m+2+2))/d≤ℓ)
    (hκpos : ∀ p∈Δ.set,0<κ p) (hκone : ∀ p∈Δ.set,κ p≤1)
    (hmin : ∀ p∈Δ.set,2*d≤κ p*(2:ℝ)^(m+2)) :
    RawNormalizationSpec T rsv (quadricScalarOuterArea m n ℓ κ) := by
  have hr : 0<rsv := by positivity
  let c := (T).backgroundCoefficient rsv
  have hc : 0<c := (T).backgroundCoefficient_pos hr (by change 0<(2:ℝ)^(m+2); positivity) hf
  have hcb : c≤rsv/(32*(2:ℝ)^(m+2)) := min_le_left _ _
  rw [quadricScalarRawModel_eq_modelOf]
  apply quadricRawModelOf_normalizationSpec m n q ℓ Δ _ _ floor rsv (quadricScalarOuterArea m n ℓ κ)
    (BranchSmall.RawQuadric.scaledPrimitive_restriction_contMDiff (parameters m) (1/Real.pi) hκ)
    (BranchSmall.RawQuadric.scaledForm_restriction_contMDiff (parameters m) (1/Real.pi) hκ)
    (fun p x u v => BranchSmall.RawQuadric.scaledForm_skew (1/Real.pi) κ p x.val u v)
    (quadricScalar_isPrimitive m κ) hf hr
  · intro p hp b y hy _
    rw [quadricScalar_semantic m κ p,chartTwoForm_smul]
    exact mul_pos (hκpos p hp) (curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) b hy)
  · intro p hp
    exact quadricScalar_handleMass_loss m ℓ κ hd hd1 hℓ hc.le hcb hκ p (hκpos p hp).le (hκone p hp)
  · intro p hp
    exact quadricScalar_outer_reserve m ℓ κ hd hd1 hℓ p (hκpos p hp).le (hκone p hp) (hmin p hp)

end SymplecticPacking.HighDim.ToricPackingStages
