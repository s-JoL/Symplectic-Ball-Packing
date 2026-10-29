import SymplecticPacking.HighDim.Handle.CubicRawModel
import SymplecticPacking.BranchLarge3.CubicCollarBounds

/-!
# Collar mass bound for the cubic native curvature

The cubic native curvature obeys the proved two-level physical mass bound.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawCubic.physicalExtension quadricTreeAt quadricTreeOrder quadricTreePrefix

variable {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ) (c L : ℝ)
  {P : Set (Moments 2)} (hP : IsCompact P)
  (hm : 0<PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P≤A)
  (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B)) (ℓ : ℕ)

include hA hAB hP hm hmA hPS
theorem cubicRawPhysical_on_base (p : Moments 2) (hp : p∈P) (x : BaseCurve) (hx : x∈cubicExhaustion ℓ) :
    semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val) x=
      manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c L p) x := by
  rw [←CubicRawPhysical.form_semantic hA hAB D S c L P ℓ hm hmA p]
  exact physicalPrimitive_extension_curvature (primitiveExt_spec hA hAB D S c L hP hPS ℓ).2 hp (hPS hp) hx

theorem cubicRawPhysical_mass_eq (p : Moments 2) (hp : p∈P) (k : ℕ) (hk : k≤ℓ) :
    compactSurfaceFormIntegral (cubicExhaustion_compact k)
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))=
      compactSurfaceFormIntegral (cubicExhaustion_compact k)
        (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c L p)) := by
  apply compactSurfaceFormIntegral_congr
  intro x hx
  apply cubicRawPhysical_on_base hA hAB D S c L hP hm hmA hPS ℓ p hp x
  change ‖x.val.1‖≤exhaustionRadius (parameters 0) k at hx
  change ‖x.val.1‖≤exhaustionRadius (parameters 0) ℓ
  have hn : (k:ℝ)≤ℓ := by exact_mod_cast hk
  dsimp [exhaustionRadius] at hx ⊢
  linarith

theorem cubicRawPhysical_positive_on_base (hc : 0<c) (hB : 3*B<D) (hS : 3*S<D)
    (p : Moments 2) (hp : p∈P) (x : BaseCurve) (hx : x∈cubicExhaustion ℓ) :
    0<chartTwoForm (semanticTwoForm Subtype.val
      (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
  dsimp only [chartTwoForm]
  rw [(extChartAt 𝓘(ℝ,Plane) x).left_inv (mem_extChartAt_source x),
    cubicRawPhysical_on_base hA hAB D S c L hP hm hmA hPS ℓ p hp x hx]
  have ht := radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) x
    (mem_extChartAt_target x)
  dsimp only [chartTwoForm] at ht
  rw [(extChartAt 𝓘(ℝ,Plane) x).left_inv (mem_extChartAt_source x)] at ht
  exact ht

end SymplecticPacking.HighDim.ToricPackingStages
