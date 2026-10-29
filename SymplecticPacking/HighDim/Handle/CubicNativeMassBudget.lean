import SymplecticPacking.HighDim.Handle.CubicRawCollar
import SymplecticPacking.HighDim.Handle.QuadricNativeMassBudget
import SymplecticPacking.HighDim.Handle.QuadricCollarBounds

/-!
# Mass budget of the six-dimensional native model

The six-dimensional native mass uses the physical collar theorem, including the two reserved levels.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport
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

variable {A B D S L : ℕ} (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B)
  (hB : 3*B<D) (hS : 3*S<D) (hL : 0<L)
  {c h₁ h₂ d₁ d₂ reserve : ℝ} (hc : 0<c) (hhd₁ : h₁<d₁) (hhd₂ : h₂<d₂)
  (hAd : (A:ℝ)=(L:ℝ)*d₁) (hBd : (B:ℝ)=(L:ℝ)*d₂) (hr : 0<reserve)
  {P : Set (Moments 2)} (hP : IsCompact P)
  (hm : 0<PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P≤A)
  (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B))
  {ℓ : ℕ} (hℓ : cubicCollarLevel A B D S L c h₁ h₂ (reserve/32)≤ℓ)
  (p : Moments 2) (hp : p∈P) (hp6 : p∈region sixModelBounds ![h₁,h₂])

include hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd hr hP hm hmA hPS hℓ hp hp6

theorem cubicRawPhysical_collar_bound :
    compactSurfaceFormIntegral (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))-
    compactSurfaceFormIntegral (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ-2))
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))<reserve/32 := by
  have htwo : 2≤ℓ := by unfold cubicCollarLevel at hℓ; omega
  rw [←quadric_exhaustion_inner_radius (parameters 0) htwo]
  change compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))-
    compactSurfaceFormIntegral (cubicExhaustion_compact (ℓ-2))
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))<reserve/32
  rw [cubicRawPhysical_mass_eq hA hAB D S c L hP hm hmA hPS ℓ p hp ℓ le_rfl,
    cubicRawPhysical_mass_eq hA hAB D S c L hP hm hmA hPS ℓ p hp (ℓ-2) (Nat.sub_le _ _)]
  exact (cubicCollarMass_lt hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd
    (div_pos hr (by norm_num)) hℓ hp6).2

theorem cubicRawPhysical_handleMass_loss {background : ℝ} (hbg : 0≤background)
    (hbgb : background≤reserve/(32*(2:ℝ)^2)) :
    compactSurfaceFormIntegral (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))-
      reserve/16≤quadricNormalizationMass 0 ℓ background
        (fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L P ℓ p x.val) p := by
  have hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine 2 →L[ℝ] Affine 2 →L[ℝ] ℝ) ∞
      (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val) :=
    (CubicRawPhysical.form_restriction_smooth hA hAB D S c L P ℓ hm hmA).comp
      (contMDiff_const.prodMk contMDiff_id)
  apply quadricNormalizationMass_loss_of_tail 0 ℓ hbg hbgb p hΩ
    (fun x u v => CubicRawPhysical.form_skew A B D S c L P ℓ p x.val u v)
  · intro x hx
    have hi : x∈cubicExhaustion ℓ := by
      change ‖x.val.1‖≤(quadricFiniteSupportRadius 0 ℓ:ℝ) at hx
      change ‖x.val.1‖≤exhaustionRadius (parameters 0) ℓ
      linarith [quadricFiniteSupportRadius_exhaustion 0 ℓ]
    exact cubicRawPhysical_positive_on_base hA hAB D S c L hP hm hmA hPS ℓ hc hB hS p hp x hi
  · exact (cubicRawPhysical_collar_bound hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd hr
      hP hm hmA hPS hℓ p hp hp6).le

end SymplecticPacking.HighDim.ToricPackingStages
