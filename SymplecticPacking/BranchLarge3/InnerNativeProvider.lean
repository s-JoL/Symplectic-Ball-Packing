import SymplecticPacking.BranchLarge3.InnerNativeData
import SymplecticPacking.HighDim.Handle.CubicRawAgreement
import SymplecticPacking.HighDim.Handle.CubicComparisonArea

/-!
# Hypotheses of the six-dimensional inner packing

Every hypothesis of the native six-dimensional packing comes from the 
comparison parameters, weighted physical form, and explicit exhaustion modulus.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.NativeInner
open Set Function MeasureTheory Manifold
open HighDim HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology Pointwise
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawCubic.physicalExtension quadricTreeAt quadricTreeOrder quadricTreePrefix

variable {N : ℕ}

def semanticModel (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) :=
  let W := weights Q r a
  cubicRawSemanticModel W.A W.B W.D W.S (coefficient Q r a) W.L 2 (level Q r a) (polytope r a)

structure ProviderSpec (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : Prop where
  model : (semanticModel Q r a).Spec
  agreement : RawModelAgreement (rawModel Q r a) (semanticModel Q r a)
  normalization : RawNormalizationSpec (rawModel Q r a) (datum Q r a).reserve
    ((semanticModel Q r a).baseArea model)
  atlas : RawFlowAtlasSpec (rawModel Q r a) (quadricFlowAtlas 0 (level Q r a))
  cover : (rawModel Q r a).presentation.inclusion ∘ (rawModel Q r a).handle.cover=
    (rawModel Q r a).handle.ambientCover
  comparison : (datum Q r a).Spec (polytope r a) (input Q r a).P (11*(input Q r a).d/16)
  profile : ∀ p∈(polytope r a).set,(input Q r a).P p ≤
    (semanticModel Q r a).baseArea model p-∑ i,max (r i-∑ j,p j) 0
  caps : ∀ i p,(∀ j,0 ≤ p j) → ∑ j,p j ≤ r i → p∈((polytope r a).dilate (cmpData r a).τ).set
  physical_near : (semanticModel Q r a).form=ᶠ[𝓝ˢ (semanticModel Q r a).region]
    globalHorizontalCoupling phaseArea
      (physicalPrimitive (A:=(weights Q r a).A) (B:=(weights Q r a).B)
        (weights Q r a).D (weights Q r a).S (coefficient Q r a) (weights Q r a).L ∘ planeMoments)

 theorem providerSpec (Q : ℕ) {r : Fin N → ℝ} {a : ℚ} (H : CmpHyp r a) : ProviderSpec Q r a := by
  let W := weights Q r a
  let c := coefficient Q r a
  let Δ := polytope r a
  let A := area Q r a
  let e := tolerance Q r a
  let I := input Q r a
  let ℓ := level Q r a
  have : Nonempty (Fin N) := ⟨⟨0,H.ne⟩⟩
  obtain ⟨hrh,hhe,hes,hsd,hdh,hhd,hd₂,hh₁,hh₂,hτ,hτ1,hε,hcaps,hconc,hmean,houter⟩ := cmpData_spec H
  have he0 : (0:ℚ) < (cmpData r a).e := by
    have hh : (0:ℝ) < (cmpData r a).e := lt_trans hh₁ (Rat.cast_lt.mpr hhe)
    exact_mod_cast hh
  have hes' : (cmpData r a).e < 1-a := by exact_mod_cast hes
  have hsd' : 1-a < (cmpData r a).d₂ := by
    have hh := (hsd.trans (Rat.cast_lt.mpr hdh)).trans (Rat.cast_lt.mpr hhd)
    exact_mod_cast hh
  have hd₂' : (cmpData r a).d₂ < (2-a)/3 := by exact_mod_cast hd₂
  have haq : (1:ℚ)/2 < a := Rat.cast_lt.mp
    (show (((1:ℚ)/2:ℚ):ℝ) < (a:ℝ) by norm_num;exact H.a_gt)
  have ha1q : a < (1:ℚ) := Rat.cast_lt.mp (show (a:ℝ) < ((1:ℚ):ℝ) by simpa using H.a_lt)
  obtain ⟨hQ,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heA,heB,heD,heS⟩ := BranchLarge3.weights_spec Q
    (a:=a) haq ha1q he0 hes' hsd' hd₂'
  change 0 < W.L at hL
  change 0 < W.A at hA
  change 0 < W.S at hS0
  change W.A ≤ W.B at hAB
  change W.S ≤ W.B at hSB
  change 3*W.B < W.D at hB
  change 3*W.S < W.D at hS
  change (W.A:ℝ)=(W.L:ℝ)*(cmpData r a).e at heA
  change (W.B:ℝ)=(W.L:ℝ)*(cmpData r a).d₂ at heB
  change (W.D:ℝ)=(W.L:ℝ)*(2-(a:ℝ)) at heD
  change (W.S:ℝ)=(W.L:ℝ)*(1-(a:ℝ)) at heS
  have hLr : 0 < (W.L:ℝ) := Nat.cast_pos.mpr hL
  have hc : 0 < c := one_div_pos.mpr (mul_pos hLr Real.pi_pos)
  have hhe' : ((cmpData r a).h₁:ℝ) < (cmpData r a).e := Rat.cast_lt.mpr hhe
  have hhd' : ((cmpData r a).h₂:ℝ) < (cmpData r a).d₂ := Rat.cast_lt.mpr hhd
  have hPS : MapsTo (physicalParameter W.L) Δ.set (Radial.lowerTrapezoid W.A W.B) :=
    physicalParameter_maps_six_region hL hhe' hhd' heA heB
  have hΔc : IsCompact Δ.set := sixModelRegion_isCompact _ _
  have hΔn : Δ.set.Nonempty := by
    refine ⟨0,⟨fun _ => le_rfl,?_⟩⟩
    intro ν
    fin_cases ν
    · simpa [Δ,polytope] using hh₁.le
    · simpa [Δ,polytope] using hh₂.le
  have hΔ : Δ.Spec := by
    refine ⟨sixModelBounds_nonneg,?_,hΔc,?_⟩
    · intro ν;fin_cases ν;exact hh₁;exact hh₂
    · intro j;refine ⟨1,?_⟩;fin_cases j  <;> norm_num [polytope,Δ,sixModelBounds]
  have harea : physicalArea W.D W.S (1/((W.L:ℝ)*Real.pi)) W.L=
      sixModelDensity (1-(a:ℝ)) ((2-(a:ℝ))/3) := physicalArea_eq_sixModelDensity hL heD heS
  have hAF : ∀ p∈Δ.set,A p= -PolyFn.eval (areaPoly Q r a) p := fun p _ => area_eq_poly Q r a hc.le p
  have hmean' : 0 < ∫ p in Δ.set,A p-∑ i,max (r i-∑ j,p j) 0 := by
    change 0 < ∫ p in Δ.set,physicalArea W.D W.S (1/((W.L:ℝ)*Real.pi)) W.L p-∑ i,max (r i-∑ j,p j) 0
    rw [harea]
    exact hmean
  have houter' : ∀ p∈Δ.set,p∉(cmpData r a).τ • Δ.set → (cmpData r a).ε ≤ A p-∑ i,max (r i-∑ j,p j) 0 := by
    change ∀ p∈Δ.set,p∉(cmpData r a).τ • Δ.set → (cmpData r a).ε ≤ physicalArea W.D W.S (1/((W.L:ℝ)*Real.pi)) W.L p-∑ i,max (r i-∑ j,p j) 0
    rw [harea]
    exact houter
  obtain ⟨he,hneg,hle,hout,hint⟩ := NativeProfile.tolerance_spec Δ hΔ A
    (physicalArea_continuous W.D W.S c W.L).continuousOn r (areaPoly Q r a) (areaPoly_ne_nil Q r a)
    hAF hmean' hε houter'
  have hI : I.Spec := NativeProfile.input_spec Δ hΔ (negativeProfile Q r a) (cmpData r a).τ
    (cmpData r a).ε hτ hτ1 hε hout hint
  have hD := CmpInput.comparatorDatum_spec (I:=I) (negP:=negativeProfile Q r a) hI hneg (fun _ _ => rfl)
  obtain ⟨hm,hmA⟩ := cubicRaw_margin_bounds hA hAB (W.L:ℝ) hΔc hΔn hPS
  have htotal := cubicRawTotalModel_eq hA hAB W.D W.S c W.L 2 ℓ Δ hΔc hΔn hm hmA
  have hmodel : (semanticModel Q r a).Spec := cubicRawSemanticModel_spec hA hAB W.D W.S c W.L 2 ℓ Δ hΔc hΔ hc hB hS hPS
  have hAE := cubicRawSemanticModel_area_eq (hA:=hA) (hAB:=hAB) (D:=W.D) (S:=W.S) (c:=c)
    (L:=(W.L:ℝ)) (q:=2) (ℓ:=ℓ) (Δ:=Δ) (hΔc:=hΔc) (hm:=hm) (hmA:=hmA) hmodel
  change cubicRawOuterArea W.A W.B W.D W.S c W.L Δ.set ℓ=(semanticModel Q r a).baseArea hmodel at hAE
  have hcal : cubicCollarLevel W.A W.B W.D W.S W.L c (cmpData r a).h₁ (cmpData r a).h₂ ((11*I.d/64)/32) ≤ ℓ :=
    le_max_right _ _
  have harea2 : ∀ p∈Δ.set,2*I.d ≤ physicalArea W.D W.S c W.L p := by
    intro p hp
    have hlo : (cmpData r a).ε ≤ physicalArea W.D W.S c W.L p :=
      cubicComparison_physicalArea_lower H hL heD heS p hp
    have hd : I.d ≤ (cmpData r a).ε/4 := min_le_right _ _
    linarith
  have hnorm : RawNormalizationSpec (rawModel Q r a) (datum Q r a).reserve
      ((semanticModel Q r a).baseArea hmodel) := by
    change RawNormalizationSpec (cubicRawTotalModel W.A W.B W.D W.S c W.L 2 ℓ Δ) (11*I.d/64) _
    rw [htotal,←hAE]
    exact cubicRawModel_spec hA hS0 hAB hSB hB hS hL hc hhe' hhd' heA heB hI.d_pos
      Δ hΔc hΔn hm hmA hPS rfl ℓ hcal harea2
  have hAEraw (p : Moments 2) (hp : p∈Δ.set) :
      |(semanticModel Q r a).baseArea hmodel p-A p| < e := by
    have hlev : cubicAreaModulusFormula W.A W.B W.D W.S W.L c (cmpData r a).h₁ (cmpData r a).h₂ e ≤ ℓ := le_max_left _ _
    have herr := cubicAreaModulusFormula_spec hA hS0 hAB hSB hB hS hL hc hhe' hhd' heA heB he ℓ hlev p hp
    have hmass := cubicRawPhysical_mass_eq hA hAB W.D W.S c W.L hΔc hm hmA hPS ℓ p hp ℓ le_rfl
    change cubicRawOuterArea W.A W.B W.D W.S c W.L Δ.set ℓ p=_ at hmass
    rw [←hmass,congrFun hAE p] at herr
    exact herr
  refine ⟨hmodel,?_,hnorm,?_,?_,hD,?_,?_,?_⟩
  · change RawModelAgreement (cubicRawTotalModel W.A W.B W.D W.S c W.L 2 ℓ Δ) _
    rw [htotal]
    exact cubicRawModel_agreement hA hAB W.D W.S c W.L 2 ℓ Δ hΔc hΔn hm hmA
  · exact quadricFlowAtlas_spec ℓ (rawModel Q r a) (quadricModelRawPresentation_inclusion 0 ℓ) rfl
  · rw [show (rawModel Q r a).presentation.inclusion=(Subtype.val : BaseCurve → Affine 2) from
      quadricModelRawPresentation_inclusion 0 ℓ]
    exact quadricRawHandle_cover_ambient 0
  · intro p hp
    have hle' := hle p hp
    change -PolyFn.eval (negativeProfile Q r a) p ≤ A p-∑ i,max (r i-∑ j,p j) 0-e at hle'
    have hlo := (abs_lt.mp (hAEraw p hp)).1
    change -PolyFn.eval (negativeProfile Q r a) p ≤ _
    linarith
  · intro i p hp hs
    obtain ⟨w,hw,heq⟩ := hcaps i ⟨hp,hs⟩
    subst p
    refine ⟨fun j => ?_,fun ν => ?_⟩
    · simpa only [Pi.smul_apply,smul_eq_mul] using mul_nonneg hτ.le (hw.1 j)
    · change (∑ j,Δ.b ν j*((cmpData r a).τ*w j)) ≤ (cmpData r a).τ*Δ.ℓ ν
      have heq : (∑ j,Δ.b ν j*((cmpData r a).τ*w j))=(cmpData r a).τ*∑ j,Δ.b ν j*w j := by
        rw [Finset.mul_sum];exact Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hw.2 ν) hτ.le

  · exact physicalCoupling_representative_near hLr.le hPS
      (primitiveExt_spec hA hAB W.D W.S c W.L hΔc hPS ℓ).2

end SymplecticPacking.BranchLarge3.NativeInner
