import SymplecticPacking.Handle.HandleStages

/-!
# Deck maps and smoothness lemmas for the handle Moser map

`sec:shd-four` (`prop:shd4-moser`): parameter-free ingredients of the concrete handle Moser map
of `Branch2/Model/Cubic/Handle/HandleMoser.lean`.

* `stripU = {u₁ − 1 < u < 1 + u₀}`, an open strip containing the fundamental strip
  (`mem_stripU`);
* `nondeg_deck`: nondegeneracy of a stage is transported by a deck map preserving it;
* `gens`: the deck generators `deckU`, `deckV` of a stage family preserved by both deck maps;
* smoothness of families of forms (`contDiff_d1_const`, `contDiff_Omega0loc`, `contDiff_form2`,
  `ev2`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e pf)
open SymplecticPacking.Bundle (pE dpE u0 u1 annulus OmegaT alpha1E Omega0loc)
open SymplecticPacking.Qhat (Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

variable (P : Params)

/-! ### Agreement with the stage forms of `cons:shd4-eta` and `cons:shd4-xi` over the fundamental strip -/

/-- The open strip `{u₁ − 1 < u < 1 + u₀}` (contains `0 ≤ u < 1`). -/
def stripU : Set E4 := {X | u1 - 1 < X 2 ∧ X 2 < 1 + u0}

lemma isOpen_stripU : IsOpen stripU :=
  (isOpen_lt continuous_const (dc 2).continuous).inter (isOpen_lt (dc 2).continuous continuous_const)

lemma mem_stripU {X : E4} (h : X 2 ∈ Ico (0 : ℝ) 1) : X ∈ stripU :=
  ⟨by linarith [h.1, u1_lt_one], by linarith [h.2, u0_pos]⟩

/-! ### Nondegeneracy -/

/-- Kernel-triviality is transported by deck maps preserving the form. -/
lemma nondeg_deck {Om : ℝ → Form2 E4} {a : ℝ → Form1 E4} (T : DeckCore) (hT : T.Preserves Om a)
    (t : ℝ) {X : E4} (h : ∀ v, (∀ w, Om t X v w = 0) → v = 0) :
    ∀ v, (∀ w, Om t (T.T X) v w = 0) → v = 0 := by
  intro v' hv'
  obtain ⟨v, rfl⟩ := T.dT_surj X v'
  have : v = 0 := h v fun w => by rw [← hT.1 t X v w]; exact hv' _
  rw [this, map_zero]

/-- The deck generators for a stage family preserved by both deck maps. -/
def gens {Om : ℝ → Form2 E4} {a : ℝ → Form1 E4} (h : ∀ T : DeckCore, IsDeck T → T.Preserves Om a) :
    DeckGens Om a where
  Tu := deckU
  Tv := deckV
  hu := ⟨rfl, rfl⟩
  hv := ⟨rfl, rfl⟩
  pres_u := h deckU (Or.inl rfl)
  pres_v := h deckV (Or.inr rfl)

/-! ### The three stages -/

lemma contDiff_d1_const {α : Form1 E4} (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (fun q : ℝ × E4 => d1 α q.2) :=
  contDiff_d1_family (E := fun q => α q.2) (hα.comp contDiff_snd)

lemma contDiff_Omega0loc : ContDiff ℝ ∞ (fun q : ℝ × E4 => Omega0loc q.2) := by
  rw [Omega0loc_eq_d1]; exact contDiff_d1_const contDiff_betaLoc

lemma contDiff_form2 {F : ℝ × E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)}
    (h : ∀ v w, ContDiff ℝ ∞ (fun q => F q v w)) : ContDiff ℝ ∞ F :=
  contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => h v w

lemma ev2 {F : ℝ × E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)} (h : ContDiff ℝ ∞ F) (v w : E4) :
    ContDiff ℝ ∞ (fun q => F q v w) := (h.clm_apply contDiff_const).clm_apply contDiff_const

/-! ### The concatenated Moser data and the handle Moser map -/

end SymplecticPacking.Handle
