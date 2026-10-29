import SymplecticPacking.Handle.HandleMoser
import SymplecticPacking.Embed.Deck

/-!
# The deck maps of the handle as deck maps of the coordinate model

`sec:shd-four` → `sec:rtc-packing` interface: the deck maps `TuE`, `TvE` of
`Handle/HandleDeck.lean` are the deck maps `Embed.deckU`, `Embed.deckV` of `Embed/Deck.lean`
(`deckU_eq`, `deckV_eq`; `deckFactor_eq`: `Embed.deckFactor = phaseV`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open SymplecticPacking.Forms (pull2)
open SymplecticPacking.Bundle (pE OmegaT phaseV autE)
open scoped ContDiff

variable (P : Params)

lemma deckFactor_eq (u v : ℝ) : Embed.deckFactor u v = phaseV u v := by
  simp only [Embed.deckFactor, phaseV, autE, Complex.real_smul, div_eq_inv_mul]
  push_cast; rfl

lemma deckU_eq : Embed.deckU = TuE := rfl

lemma deckV_eq : Embed.deckV = TvE := by
  funext X
  simp only [Embed.deckV, TvE, deckFactor_eq, cV_eq]

end SymplecticPacking.Handle
