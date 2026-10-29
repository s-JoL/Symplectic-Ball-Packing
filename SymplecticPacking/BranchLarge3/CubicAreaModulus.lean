import SymplecticPacking.BranchLarge3.CubicTail

/-!
# An effective area modulus for the cubic exhaustion

The proof uses the uniform variable-residue estimate on punctured end charts.
The residue error decays as an inverse logarithm; `CubicTail.modulus` gives a
concrete exponential tolerance dependence. No extension of the radial form
across the punctures or polynomial convergence rate is assumed.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.FiniteMoment
open scoped ContDiff Manifold Topology
open Set

local instance cubicAreaModulusSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

/-- Area error of the `ℓ`-th cubic exhaustion set at the moment `p`. -/
def cubicAreaError (A B D S L : ℕ) (c : ℝ) (ℓ : ℕ) (p : Moments 2) : ℝ :=
  physicalArea D S c (L : ℝ) p -
    compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c (L : ℝ) p))

/-- Explicit common exhaustion index, independent of the physical moment. -/
def cubicAreaModulusFormula (A B D S _L : ℕ) (c _h₁ _h₂ : ℝ) (e : ℝ) : ℕ :=
  CubicTail.modulus A B D S c e

section Lemmas

variable {A B D S L : ℕ} (hA : 0 < A) (hS0 : 0 < S)
    (hAB : A ≤ B) (hSB : S ≤ B) (hB : 3 * B < D) (hS : 3 * S < D) (hL : 0 < L)
    {c h₁ h₂ d₁ d₂ : ℝ} (hc : 0 < c) (hhd₁ : h₁ < d₁) (hhd₂ : h₂ < d₂)
    (hAd : (A : ℝ) = (L : ℝ) * d₁) (hBd : (B : ℝ) = (L : ℝ) * d₂)
include hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd

/-- The integral over any compact set is at most the limit area (positivity of the radial
form). -/
theorem cubicAreaError_nonneg (ℓ : ℕ) {p : Moments 2} (hp : p ∈ region sixModelBounds ![h₁, h₂]) :
    0 ≤ cubicAreaError A B D S L c ℓ p := by
  have hpS := physicalParameter_maps_six_region (A := A) (B := B) hL hhd₁ hhd₂ hAd hBd hp
  have h := radial_cubic_compact_area_le hA hS0 hAB hSB hB hS hpS hc (cubicExhaustion_compact ℓ)
  unfold cubicAreaError
  rw [sub_nonneg]
  convert h using 1
  · rfl
  have hm : (S : ℝ) - (L : ℝ) * p 0 - (L : ℝ) * p 1 = (S : ℝ) - ((L : ℝ) * p 0 + (L : ℝ) * p 1) :=
    by ring
  simp only [OAI.PackingSufficiencySupport.CubicModel.physicalArea,
    OAI.PackingSufficiencySupport.CubicModel.physicalParameter,
    OAI.PackingSufficiencySupport.FiniteMoment.markedHeight,
    OAI.PackingSufficiencySupport.FiniteMoment.planeVector,
    Matrix.cons_val_zero, Matrix.cons_val_one, hm]

omit hS0 hSB in
/-- The area error is antitone in the level. -/
theorem cubicAreaError_antitone {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') {p : Moments 2}
    (hp : p ∈ region sixModelBounds ![h₁, h₂]) :
    cubicAreaError A B D S L c ℓ' p ≤ cubicAreaError A B D S L c ℓ p := by
  have hpS := physicalParameter_maps_six_region (A := A) (B := B) hL hhd₁ hhd₂ hAd hBd hp
  unfold cubicAreaError
  apply sub_le_sub_left
  apply compactSurfaceFormIntegral_mono _ _ ?_ (positivePlaneTransitions (parameters 0))
    (radialForm_smooth hA hAB _ _ c hpS) (radialForm_skew _ _ _ c _)
    (fun b y hy => (radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc hpS b hy).le)
  intro x hx
  change ‖x.val.1‖ ≤ exhaustionRadius (parameters 0) ℓ'
  have hh : exhaustionRadius (parameters 0) ℓ ≤ exhaustionRadius (parameters 0) ℓ' := by
    dsimp only [exhaustionRadius]
    gcongr
  exact (show ‖x.val.1‖ ≤ exhaustionRadius (parameters 0) ℓ from hx).trans hh

/-- The compact exhaustion contains the controlled cutoff mass, so its area deficit
is at most the explicit punctured-end error. -/
theorem cubicAreaError_le_tail {ℓ : ℕ} (hℓ : 32 ≤ ℓ) {p : Moments 2}
    (hp : p ∈ region sixModelBounds ![h₁, h₂]) :
    cubicAreaError A B D S L c ℓ p ≤ CubicTail.errorBound A B D S c ℓ := by
  have hpS := physicalParameter_maps_six_region (A := A) (B := B) hL hhd₁ hhd₂ hAd hBd hp
  have hmass := CubicTail.radial_mass_error hA hS0 hAB hSB hB hS hpS c ℓ
  have hle := surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions (parameters 0))
    (cubicExhaustion_compact ℓ)
    (shrinking_curveEndCutoff_compact (parameters 0) (by norm_num [CubicTail.inner])
      (fun _ ht => CubicTail.cutoff_one ht) ℓ)
    (CubicTail.cutoff_support_exhaustion hℓ)
    (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth CubicTail.cutoff_smooth ℓ)
      (shrinkingCutoff_compact CubicTail.cutoff_compact ℓ))
    (fun x => (curveEndCutoff_range (parameters 0) (fun t => CubicTail.cutoff_range _) x).2)
    (radialForm_smooth hA hAB _ _ c hpS) (radialForm_skew _ _ _ c _)
    (fun b y hy => (radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc hpS b hy).le)
  have he := (abs_le.mp hmass).1
  have hform : manifoldExteriorOneForm
      (physicalPrimitive (A := A) (B := B) D S c (L : ℝ) p) =
      radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D)
        (cubicMarkedOrder S) c (physicalParameter (L : ℝ) p) := rfl
  have harea : physicalArea D S c (L : ℝ) p =
      c * (3 * ((D : ℝ) - 3 * ((physicalParameter (L : ℝ) p).1 +
        (physicalParameter (L : ℝ) p).2)) -
          2 * markedHeight S (planeVector (physicalParameter (L : ℝ) p).1
            (physicalParameter (L : ℝ) p).2)) * Real.pi := by
    simp [physicalArea, physicalParameter, markedHeight, planeVector, sub_sub]
  unfold cubicAreaError
  rw [hform, harea]
  linarith

/-- The explicit logarithmic-tail modulus works uniformly on the six-model region. -/
theorem cubicAreaModulusFormula_spec {e : ℝ} (he : 0 < e) :
    ∀ ℓ ≥ cubicAreaModulusFormula A B D S L c h₁ h₂ e, ∀ p ∈ region sixModelBounds ![h₁, h₂],
      |compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
        (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c (L : ℝ) p)) -
        physicalArea D S c (L : ℝ) p| < e := by
  intro ℓ hℓ p hp
  have h0 := cubicAreaError_nonneg hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd ℓ hp
  have h32 : 32 ≤ ℓ := (le_max_left _ _).trans hℓ
  have h1 := cubicAreaError_le_tail hA hS0 hAB hSB hB hS hL hc hhd₁ hhd₂ hAd hBd h32 hp
  rw [abs_sub_comm, show physicalArea D S c (L : ℝ) p -
      compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
        (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c (L : ℝ) p)) =
      cubicAreaError A B D S L c ℓ p from rfl, abs_of_nonneg h0]
  exact h1.trans_lt (CubicTail.errorBound_lt he hℓ)

end Lemmas

end SymplecticPacking.BranchLarge3
