import SymplecticPacking.HighDim.Handle.QuadricNormalizationSpec
import SymplecticPacking.HighDim.Handle.CubicNativeMassBudget
import SymplecticPacking.HighDim.Handle.CubicRawMargin

/-!
# Native normalization provider for the cubic model

The cubic model supplies the complete native normalization provider.
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

/-- The common level includes the collar modulus and two whole inner levels. -/
def cubicRawLevel (oldLevel A B D S L : ℕ) (c h₁ h₂ reserve : ℝ) : ℕ :=
  max oldLevel (cubicCollarLevel A B D S L c h₁ h₂ (reserve/32))

def cubicRawOuterArea (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ) (p : Moments 2) : ℝ :=
  compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
    (semanticTwoForm Subtype.val (fun x : BaseCurve => CubicRawPhysical.form A B D S c L P ℓ p x.val))

variable {A B D S L q : ℕ} (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B)
  (hB : 3*B<D) (hS : 3*S<D) (hL : 0<L)
  {c h₁ h₂ d₁ d₂ d : ℝ} (hc : 0<c) (hhd₁ : h₁<d₁) (hhd₂ : h₂<d₂)
  (hAd : (A:ℝ)=(L:ℝ)*d₁) (hBd : (B:ℝ)=(L:ℝ)*d₂) (hd : 0<d)
  (Δ : Polytope 2 q) (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
  (hm : 0<PrimExt.margin A B L Δ.set) (hmA : PrimExt.margin A B L Δ.set≤A)
  (hPS : MapsTo (physicalParameter L) Δ.set (Radial.lowerTrapezoid A B))
  (hregion : Δ.set=region sixModelBounds ![h₁,h₂])
  (ℓ : ℕ) (hℓ : cubicCollarLevel A B D S L c h₁ h₂ ((11*d/64)/32)≤ℓ)
  (harea : ∀ p∈Δ.set,2*d≤physicalArea D S c L p)

include hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd hd hΔc hΔn hm hmA hPS hregion hℓ harea

theorem cubicRawModel_spec :
    RawNormalizationSpec (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA) (11*d/64)
      (cubicRawOuterArea A B D S c L Δ.set ℓ) := by
  let Γ := fun p (x : BaseCurve) => RawCubic.physicalExtension A B D S c L Δ.set ℓ p x.val
  let Ω := fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val
  let floor := (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA).densityFloor
  have hr : 0<11*d/64 := by positivity
  have hf : 0<floor := cubicRawModel_floor_pos hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA hc hB hS hPS
  have hmodel : cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA=
      quadricRawModelOf 0 2 q ℓ Δ Γ Ω floor := rfl
  rw [hmodel]
  let T := quadricRawModelOf 0 2 q ℓ Δ Γ Ω floor
  let bg := T.backgroundCoefficient (11*d/64)
  have hbg : 0<bg := T.backgroundCoefficient_pos hr (by change 0<(2:ℝ)^2; positivity) hf
  have hbgb : bg≤(11*d/64)/(32*(2:ℝ)^2) := min_le_left _ _
  apply quadricRawModelOf_normalizationSpec 0 2 q ℓ Δ Γ Ω floor (11*d/64)
    (cubicRawOuterArea A B D S c L Δ.set ℓ)
    (RawCubic.physicalExtension_contDiff hA hAB D S c L Δ.set ℓ hm hmA |>.contMDiff.comp
      (contMDiff_fst.prodMk_space ((real_inclusion_contMDiff (parameters 0)).comp contMDiff_snd)))
    (CubicRawPhysical.form_restriction_smooth hA hAB D S c L Δ.set ℓ hm hmA)
    (fun p x u v => CubicRawPhysical.form_skew A B D S c L Δ.set ℓ p x.val u v)
    (fun p => CubicRawPhysical.primitive_isPrimitive hA hAB D S c L Δ.set ℓ hm hmA p) hf hr
  · intro p hp b y hy hx
    dsimp only [chartTwoForm]
    rw [cubicRawPhysical_on_base hA hAB D S c L hΔc hm hmA hPS ℓ p hp _ hx]
    exact radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy
  · intro p hp
    exact cubicRawPhysical_handleMass_loss hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd hr
      hΔc hm hmA hPS hℓ p hp (hregion ▸ hp) hbg.le hbgb
  · intro p hp
    have hlev : cubicAreaModulusFormula A B D S L c h₁ h₂ ((11*d/64)/32)≤ℓ := by
      unfold cubicCollarLevel at hℓ
      omega
    have hmod := cubicAreaModulusFormula_spec hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd
      (div_pos hr (by norm_num)) ℓ hlev p (hregion ▸ hp)
    have heq := cubicRawPhysical_mass_eq hA hAB D S c L hΔc hm hmA hPS ℓ p hp ℓ le_rfl
    change cubicRawOuterArea A B D S c L Δ.set ℓ p=_ at heq
    rw [←heq] at hmod
    have hlo := (abs_lt.mp hmod).1
    linarith [harea p hp]

#check_explicit cubicRawLevel
end SymplecticPacking.HighDim.ToricPackingStages
