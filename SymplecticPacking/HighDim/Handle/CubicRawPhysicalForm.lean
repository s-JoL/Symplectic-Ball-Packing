import SymplecticPacking.HighDim.Handle.RawAmbientExterior
import SymplecticPacking.BranchLarge3.CubicRawForms

/-!
# The six-dimensional physical curvature form

The six-dimensional physical curvature is the Euclidean derivative of its native primitive.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.CubicRawPhysical
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawCubic.physicalExtension

def form (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (p : Moments 2) (z : Affine 2) : Affine 2 →L[ℝ] Affine 2 →L[ℝ] ℝ :=
  ambientFamilyExterior (RawCubic.physicalExtension A B D S c L P ℓ) p z

theorem form_skew (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (p : Moments 2) (z u v : Affine 2) :
    form A B D S c L P ℓ p z u v = -form A B D S c L P ℓ p z v u := by
  change fderiv ℝ (RawCubic.physicalExtension A B D S c L P ℓ p) z u v-
      fderiv ℝ (RawCubic.physicalExtension A B D S c L P ℓ p) z v u =
    -(fderiv ℝ (RawCubic.physicalExtension A B D S c L P ℓ p) z v u-
      fderiv ℝ (RawCubic.physicalExtension A B D S c L P ℓ p) z u v)
  ring

theorem form_restriction_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (hm : 0<PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P≤A) :
    ContMDiff ((𝓘(ℝ,Moments 2)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine 2 →L[ℝ] Affine 2 →L[ℝ] ℝ) ∞
      (fun q : Moments 2 × BaseCurve => form A B D S c L P ℓ q.1 q.2.val) :=
  ambientFamilyExterior_restriction_smooth (real_inclusion_contMDiff (parameters 0))
    (RawCubic.physicalExtension_contDiff hA hAB D S c L P ℓ hm hmA)

theorem primitive_isPrimitive {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (hm : 0<PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P≤A) (p : Moments 2) :
    RawIsPrimitive (Subtype.val : BaseCurve → Affine 2)
      (fun x => form A B D S c L P ℓ p x.val)
      (fun x => RawCubic.physicalExtension A B D S c L P ℓ p x.val) := by
  change RawIsPrimitive (Subtype.val : BaseCurve → Affine 2)
    (fun x => euclideanExteriorOneForm (RawCubic.physicalExtension A B D S c L P ℓ p) x.val)
    (fun x => RawCubic.physicalExtension A B D S c L P ℓ p x.val)
  apply ambient_primitive_restriction (Γ := RawCubic.physicalExtension A B D S c L P ℓ p)
    (real_inclusion_contMDiff (parameters 0))
  exact (RawCubic.physicalExtension_contDiff hA hAB D S c L P ℓ hm hmA).comp
    (contDiff_const.prodMk contDiff_id)

theorem form_semantic {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (hm : 0<PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P≤A) (p : Moments 2) :
    manifoldExteriorOneForm (primitiveExt A B D S c L P ℓ p)=
      semanticTwoForm (Subtype.val : BaseCurve → Affine 2) (fun x => form A B D S c L P ℓ p x.val) := by
  have he : primitiveExt A B D S c L P ℓ p=semanticOneForm (Subtype.val : BaseCurve → Affine 2)
      (fun x => RawCubic.physicalExtension A B D S c L P ℓ p x.val) :=
    funext (RawCubic.physicalExtension_eq A B D S c L P ℓ p)
  rw [he]
  change manifoldExteriorOneForm (semanticOneForm (Subtype.val : BaseCurve → Affine 2)
    (fun x => RawCubic.physicalExtension A B D S c L P ℓ p x.val)) =
      semanticTwoForm Subtype.val (fun x => euclideanExteriorOneForm
        (RawCubic.physicalExtension A B D S c L P ℓ p) x.val)
  apply semantic_ambient_exterior (Γ := RawCubic.physicalExtension A B D S c L P ℓ p)
    (real_inclusion_contMDiff (parameters 0))
  exact (RawCubic.physicalExtension_contDiff hA hAB D S c L P ℓ hm hmA).comp
    (contDiff_const.prodMk contDiff_id)

#check_explicit form
end SymplecticPacking.HighDim.ToricPackingStages.CubicRawPhysical
