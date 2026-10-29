import SymplecticPacking.Handle.HandleMoserSpec
import SymplecticPacking.Branch2.Model.Cubic.Handle.HandleMoser

/-!
# The handle Moser map in the format of the strip embeddings

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` → `sec:str`/`sec:rtc-packing` interface: the concrete handle Moser map
`handlePhi P`, `handlePhiInv P` (`Cubic/Handle/HandleMoser.lean`) in the formats consumed by
`Cubic/Strip/Embed.lean` and `Embed/Deck.lean`.

* `handle_deckEquivariant`: `Embed.DeckEquivariant (handlePhiInv P)` (global);
* `handle_phiInvSpec_strip`: all fields of `Strip.Cubic.PhiInvSpec P (handlePhi P) (handlePhiInv P)`,
  except that `pullback` (with the strip form `OmegaFinal P`) holds on `{p < h} ∩ stripU`,
  `stripU = {u₁ − 1 < u < 1 + u₀}` (on all of `{p < h}` it holds with the periodised
  `OmegaFinalPer P`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open SymplecticPacking.Forms (pull2)
open SymplecticPacking.Bundle (pE phaseV autE)
open SymplecticPacking.Bundle.Cubic (OmegaT)
open scoped ContDiff

variable (P : Branch2.VCubic)

theorem handle_deckEquivariant : Embed.DeckEquivariant (handlePhiInv P) where
  commU X := by rw [deckU_eq]; exact ((handleMoser P).2.2.2.2.2.2.2.2.2 X).2.2.1
  commV X := by rw [deckV_eq]; exact ((handleMoser P).2.2.2.2.2.2.2.2.2 X).2.2.2

theorem handle_phiInvSpec_strip :
    (∀ X, pE X < P.h → ContDiffAt ℝ ∞ (handlePhiInv P) X) ∧
    (∀ X, pE X < P.h → X ∈ stripU →
      pull2 (handlePhiInv P) (OmegaT P 0) X = OmegaFinal P X) ∧
    (∀ X, pE X < P.h → pull2 (handlePhiInv P) (OmegaT P 0) X = OmegaFinalPer P X) ∧
    (∀ X, pE X < P.h → pE (handlePhiInv P X) < P.h) ∧
    (∀ X, pE X < P.h → handlePhi P (handlePhiInv P X) = X) ∧
    (∀ X ∈ Strip.fibreSet, handlePhi P X = X) := by
  obtain ⟨-, hsi, -, hr, -, hpb, hstrip, hlev, hfix, -⟩ := handleMoser P
  have hle : ∀ X, pE X < P.h → pE X ≤ P.h + deltam P := fun X h => by
    linarith [deltam_pos P]
  exact ⟨fun X _ => hsi.contDiffAt, fun X hX hs => by rw [hpb X (hle X hX), hstrip X hs],
    fun X hX => hpb X (hle X hX), fun X hX => ((hlev P.h (Psupp_lt_h P) X).2.2.2).mpr hX,
    fun X _ => hr X, fun X hX => (hfix X hX).1⟩

end SymplecticPacking.Handle.Cubic
