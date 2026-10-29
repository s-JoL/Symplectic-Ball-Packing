import SymplecticPacking.HighDim.Handle.RawNormalPrimitive
import SymplecticPacking.HighDim.Handle.QuadricRawModelSpec
import SymplecticPacking.HighDim.Handle.QuadricRawNormalizedSupport
import SymplecticPacking.HighDim.Handle.QuadricRawNormalizedPositive

/-!
# The native normalized primitive of the quadric models

The generic raw normalizer specializes exactly to the proved quadric construction.
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

 theorem quadricRawHandle_normalize {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (m : ℕ) (b : ℝ) (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ) :
    (quadricRawHandle m).normalize Subtype.val b Γ N=QuadricRawAnnular.normalize m b Γ N := rfl

 def quadricRawModelOf (m n q ℓ : ℕ) (Δ : Polytope n q)
    (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
    (floor : ℝ) : RawToricModel (Affine (m+2)) (Surface m) n q :=
  { quadricScalarRawModel m n q ℓ Δ (fun _ => 0) floor with
    physicalPrimitive := Γ
    physicalForm := Ω }

 theorem quadricScalarRawModel_eq_modelOf (m n q ℓ : ℕ) (Δ : Polytope n q)
    (κ : Moments n → ℝ) (floor : ℝ) :
    quadricScalarRawModel m n q ℓ Δ κ floor=quadricRawModelOf m n q ℓ Δ
      (fun p (x : Surface m) => BranchSmall.RawQuadric.scaledPrimitive (1/Real.pi) κ p x.val)
      (fun p (x : Surface m) => BranchSmall.RawQuadric.scaledForm (1/Real.pi) κ p x.val) floor := rfl

 theorem quadricRawModelOf_normalModel (m n q ℓ : ℕ) (Δ : Polytope n q)
    (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
    (floor reserve : ℝ) :
    (quadricRawModelOf m n q ℓ Δ Γ Ω floor).normalModel reserve=
      QuadricRawAnnular.normalModel m (1/16)
        ((quadricRawModelOf m n q ℓ Δ Γ Ω floor).backgroundCoefficient reserve)
        (quadricNormalizationMass m ℓ ((quadricRawModelOf m n q ℓ Δ Γ Ω floor).backgroundCoefficient reserve) Ω) := by
  funext p x
  have hi := congrArg (fun f : Surface m → HandleCylinder => (f x).1) (quadricRawHandle_inverse m)
  have hr := QuadricRawDensity.radialCoordinate_eq m (1/16) x
  change _ = _ at hi
  change _ = _ at hr
  unfold RawToricModel.normalModel QuadricRawAnnular.normalModel
  change _+(_*intervalClock (-(1/16)) (1/16) ((quadricRawHandle m).inverse x).1) • _ =
    _+(_*QuadricRawDensity.radialCoordinate (1/16) (QuadricRawDual.transverseProjection m x.val)) • _
  rw [hr,hi]
  rfl

 theorem quadricRawModelOf_normalPrimitive (m n q ℓ : ℕ) (Δ : Polytope n q)
    (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
    (floor reserve : ℝ) :
    (quadricRawModelOf m n q ℓ Δ Γ Ω floor).normalPrimitive reserve=
      quadricNormalizedPrimitive m ℓ
        ((quadricRawModelOf m n q ℓ Δ Γ Ω floor).backgroundCoefficient reserve) Γ Ω := by
  unfold RawToricModel.normalPrimitive
  rw [quadricRawModelOf_normalModel]
  have hi : (quadricRawModelOf m n q ℓ Δ Γ Ω floor).presentation.inclusion=Subtype.val :=
    quadricModelRawPresentation_inclusion m ℓ
  rw [hi]
  change (quadricRawHandle m).normalize Subtype.val (1/16)
    (quadricRedistributedPrimitive m ℓ _ Γ Ω) (QuadricRawAnnular.normalModel m (1/16) _ _)=_
  exact quadricRawHandle_normalize m (1/16) _ _

end SymplecticPacking.HighDim.ToricPackingStages
