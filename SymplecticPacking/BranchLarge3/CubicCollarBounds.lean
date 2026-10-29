import SymplecticPacking.BranchLarge3.CubicAreaModulus
import SymplecticPacking.Explicit

/-!
# Mass in the outer levels of the cubic exhaustion

Uniform mass lost in the outer two levels of the cubic exhaustion.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open OAI.PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set

/-- Reserve two exhaustion levels for the fixed boundary cutoff. -/
def cubicCollarLevel (A B D S L : ℕ) (c h₁ h₂ e : ℝ) : ℕ :=
  cubicAreaModulusFormula A B D S L c h₁ h₂ e + 2

theorem cubicCollarLevel_inner {A B D S L : ℕ} {c h₁ h₂ e : ℝ} {ℓ : ℕ}
    (hℓ : cubicCollarLevel A B D S L c h₁ h₂ e ≤ ℓ) :
    cubicAreaModulusFormula A B D S L c h₁ h₂ e ≤ ℓ-2 := by
  unfold cubicCollarLevel at hℓ
  omega

theorem cubicCollarMass_lt
    {A B D S L : ℕ} (hA : 0 < A) (hS0 : 0 < S)
    (hAB : A ≤ B) (hSB : S ≤ B) (hB : 3*B < D) (hS : 3*S < D) (hL : 0 < L)
    {c h₁ h₂ d₁ d₂ e : ℝ} (hc : 0 < c) (hhd₁ : h₁ < d₁) (hhd₂ : h₂ < d₂)
    (hAd : (A:ℝ) = (L:ℝ)*d₁) (hBd : (B:ℝ) = (L:ℝ)*d₂) (he : 0 < e)
    {ℓ : ℕ} (hℓ : cubicCollarLevel A B D S L c h₁ h₂ e ≤ ℓ)
    {p : Moments 2} (hp : p ∈ region sixModelBounds ![h₁,h₂]) :
    0 ≤ compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
          (manifoldExteriorOneForm (physicalPrimitive (A:=A) (B:=B) D S c (L:ℝ) p)) -
        compactSurfaceFormIntegral (cubicExhaustion_compact (ℓ-2))
          (manifoldExteriorOneForm (physicalPrimitive (A:=A) (B:=B) D S c (L:ℝ) p)) ∧
      compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
          (manifoldExteriorOneForm (physicalPrimitive (A:=A) (B:=B) D S c (L:ℝ) p)) -
        compactSurfaceFormIntegral (cubicExhaustion_compact (ℓ-2))
          (manifoldExteriorOneForm (physicalPrimitive (A:=A) (B:=B) D S c (L:ℝ) p)) < e := by
  have hout := cubicAreaError_nonneg hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd ℓ hp
  have hmono := cubicAreaError_antitone hA hAB hB hS hL hc hhd₁ hhd₂ hAd hBd
    (Nat.sub_le ℓ 2) hp
  have hin := cubicAreaModulusFormula_spec hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd he
    (ℓ-2) (cubicCollarLevel_inner hℓ) p hp
  unfold cubicAreaError at hout hmono
  have hh := (abs_lt.mp hin).1
  constructor <;> linarith

#check_explicit cubicCollarLevel
end SymplecticPacking.BranchLarge3
