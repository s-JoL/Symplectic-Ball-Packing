import SymplecticPacking.HighDim.Handle.CubicRawPhysicalForm
import SymplecticPacking.HighDim.Handle.QuadricNativeFloor
import SymplecticPacking.HighDim.Handle.QuadricRawModel

/-!
# The six-dimensional raw toric model

The six-dimensional model uses its native physical curvature and finite coefficient floor.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawCubic.physicalExtension quadricTreeAt quadricTreeOrder quadricTreePrefix

variable {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ) (c L : ℝ) (q ℓ : ℕ)
  (Δ : Polytope 2 q) (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
  (hm : 0<PrimExt.margin A B L Δ.set) (hmA : PrimExt.margin A B L Δ.set≤A)

def cubicRawModel : RawToricModel (Affine 2) BaseCurve 2 q :=
  { quadricScalarRawModel 0 2 q ℓ Δ (fun _ => 0) 0 with
    physicalPrimitive p x := RawCubic.physicalExtension A B D S c L Δ.set ℓ p x.val
    physicalForm p x := CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val
    densityFloor := quadricNativeFloor ℓ Δ
      (fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val)
      (CubicRawPhysical.form_restriction_smooth hA hAB D S c L Δ.set ℓ hm hmA) hΔc hΔn }

include hA hAB hΔc hm hmA in
theorem cubicRawPhysical_positive (hc : 0<c) (hB : 3*B<D) (hS : 3*S<D)
    (hPS : MapsTo (physicalParameter L) Δ.set (Radial.lowerTrapezoid A B))
    (p : Moments 2) (hp : p∈Δ.set) (x : BaseCurve) (hx : x∈cubicExhaustion ℓ) :
    0<chartTwoForm (semanticTwoForm Subtype.val
      (fun x : BaseCurve => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
  rw [← CubicRawPhysical.form_semantic hA hAB D S c L Δ.set ℓ hm hmA p]
  dsimp only [chartTwoForm]
  rw [(extChartAt 𝓘(ℝ,Plane) x).left_inv (mem_extChartAt_source x)]
  rw [physicalPrimitive_extension_curvature
    (primitiveExt_spec hA hAB D S c L hΔc hPS ℓ).2 hp (hPS hp) hx]
  have ht := radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) x
    (mem_extChartAt_target x)
  dsimp only [chartTwoForm] at ht
  rw [(extChartAt 𝓘(ℝ,Plane) x).left_inv (mem_extChartAt_source x)] at ht
  exact ht

include hA hAB hΔc hΔn hm hmA in
theorem cubicRawModel_floor_pos (hc : 0<c) (hB : 3*B<D) (hS : 3*S<D)
    (hPS : MapsTo (physicalParameter L) Δ.set (Radial.lowerTrapezoid A B)) :
    0<(cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA).densityFloor := by
  change 0<quadricNativeFloor ℓ Δ
    (fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val)
    (CubicRawPhysical.form_restriction_smooth hA hAB D S c L Δ.set ℓ hm hmA) hΔc hΔn
  apply quadricNativeFloor_pos ℓ Δ
    (fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val)
    (CubicRawPhysical.form_restriction_smooth hA hAB D S c L Δ.set ℓ hm hmA) hΔc hΔn
  · exact fun p x u v => CubicRawPhysical.form_skew A B D S c L Δ.set ℓ p x.val u v
  · intro p hp x hx
    exact cubicRawPhysical_positive hA hAB D S c L q ℓ Δ hΔc hm hmA hc hB hS hPS p hp x hx

#check_explicit cubicRawModel
end SymplecticPacking.HighDim.ToricPackingStages
