import SymplecticPacking.Handle.HandleDeck
import SymplecticPacking.Branch2.Model.Cubic.Handle.SecondStage

/-!
# Deck invariance of `α₁` and of the first Moser path

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`cons:shd4-moser`): with the deck maps `TuE`, `TvE` of `Handle/HandleDeck.lean`,
the ambient primitive `α₁` is horizontal (`alpha1E_horizontal`), smooth and invariant under both
deck maps (`alpha1E_TuE`, `alpha1E_TvE`, `alpha1E_deck`), and every form `Ω_t = Ω₀ + t dα₁` of
the first Moser path is preserved by them (`OmegaT_preserves`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap _root_.Complex ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE Zunit phaseV autE tau tau_re thetaFactor torusZ etaHu etaHv dZu dZv herm3 Zunit_add_one_left Zunit_add_one_right etaExpr_smul Zunit_unit norm_phaseV conj_mul_self_of_norm_one hasDerivAt_Zunit_u hasDerivAt_Zunit_v dZu_eq dZv_eq)
open SymplecticPacking.Return (betaLoc fuC fvC)
open scoped ContDiff Real

attribute [local irreducible] etaHu etaHv

set_option synthInstance.maxHeartbeats 200000

/-! ### The explicit phase -/

/-! ### `η_H` under the deck translations -/

/-! ### The deck maps -/

/-! ### The primitive `β` of `Ω₀` under the deck maps -/

/-! ### Invariance of forms under the deck maps -/

open SymplecticPacking.Bundle (Omega0loc AffineP sl Coef)
open SymplecticPacking.Bundle.Cubic (alpha1E alpha1 OmegaT)

lemma alpha1E_horizontal (P : Branch2.VCubic) (Y v : E4) :
    alpha1E P Y v = alpha1E P Y (e 2) * v 2 + alpha1E P Y (e 3) * v 3 := by
  simp [alpha1E]

lemma contDiff_alpha1E (P : Branch2.VCubic) : ContDiff ℝ ∞ (alpha1E P) := by
  obtain ⟨ha, hb⟩ := Bundle.Cubic.alpha1_affine P
  exact ((contDiff_coef ha (Bundle.Cubic.smooth_alpha1 P 0).1 (Bundle.Cubic.smooth_alpha1 P 1).1).smul
    contDiff_const).add
    ((contDiff_coef hb (Bundle.Cubic.smooth_alpha1 P 0).2 (Bundle.Cubic.smooth_alpha1 P 1).2).smul
      contDiff_const)

lemma alpha1E_TuE (P : Branch2.VCubic) (X : E4) : alpha1E P (TuE X) = alpha1E P X := by
  have hp := deckU.pE_eq X
  change pE (TuE X) = pE X at hp
  have h := Bundle.Cubic.alpha1_periodic P (X 2) (X 3) (pE X)
  unfold alpha1E; rw [hp]
  simp only [dc_apply, TuE, mk_apply2, mk_apply3, h.1, h.2.1]

lemma alpha1E_TvE (P : Branch2.VCubic) (X : E4) : alpha1E P (TvE X) = alpha1E P X := by
  have hp := deckV.pE_eq X
  change pE (TvE X) = pE X at hp
  have h := Bundle.Cubic.alpha1_periodic P (X 2) (X 3) (pE X)
  unfold alpha1E; rw [hp]
  simp only [dc_apply, TvE, mk_apply2, mk_apply3, h.2.2.1, h.2.2.2]

lemma pull1_alpha1E (P : Branch2.VCubic) (T : DeckCore) (hT : ∀ X, alpha1E P (T.T X) = alpha1E P X)
    (X : E4) : pull1 T.T (alpha1E P) X = alpha1E P X :=
  pull1_horizontal T (alpha1E_horizontal P) (hT X)

lemma pull2_d1_alpha1E (P : Branch2.VCubic) (T : DeckCore) (hT : ∀ X, alpha1E P (T.T X) = alpha1E P X)
    (X : E4) : pull2 T.T (d1 (alpha1E P)) X = d1 (alpha1E P) X :=
  pull2_d1_of_pull1 T.smooth (contDiff_alpha1E P) 0
    (fun Y => by rw [pull1_alpha1E P T hT, add_zero]) X

lemma alpha1E_deck (P : Branch2.VCubic) (T : DeckCore) (hT : T = deckU ∨ T = deckV) (X : E4) :
    alpha1E P (T.T X) = alpha1E P X := by
  rcases hT with rfl | rfl
  · exact alpha1E_TuE P X
  · exact alpha1E_TvE P X

/-- **`Ω_t = Ω₀ + t dα₁` and `α₁` are preserved by the deck maps.** -/
theorem OmegaT_preserves (P : Branch2.VCubic) (T : DeckCore) (hT : T = deckU ∨ T = deckV) :
    T.Preserves (OmegaT P) (fun _ => alpha1E P) := by
  refine ⟨fun t X v w => ?_, fun t X v => ?_⟩
  · have h1 := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ => B v w) (pull2_Omega0loc_deck T hT X)
    have h2 := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ => B v w)
      (pull2_d1_alpha1E P T (alpha1E_deck P T hT) X)
    simp only [Forms.pull2_apply] at h1 h2
    simp only [OmegaT, add_apply, smul_apply, smul_eq_mul, h1, h2]
  · have := congrArg (fun B : E4 →L[ℝ] ℝ => B v) (pull1_alpha1E P T (alpha1E_deck P T hT) X)
    simpa only [Forms.pull1_apply] using this

end SymplecticPacking.Handle.Cubic
