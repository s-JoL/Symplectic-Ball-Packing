import SymplecticPacking.General.Interface
import SymplecticPacking.BranchLarge3.Bridge
import SymplecticPacking.BranchLarge3.Assemble

/-!
# Branch n = 3, one c_j ≥ C/2: the explicit embeddings

`embeddings` and `embeddings_spec` are the interface used by `SymplecticPacking.General.Main`.
The definition is total (it does not take the hypotheses); `embeddings_spec` states its
properties under the branch hypotheses.

For `n = 3` the data are `dataOfBallMaps C (ballMap C c) (enl C c) (rad C c)`: the explicit
OpenAI-normalised ball maps of `Assemble` conjugated by `y ↦ √C Φ⁻¹(F(Φ(y/√C)))` (`Bridge`),
enlarged capacities `C (ρ_i + η)` and domains `C (ρ_i + 2η)` (`Params`). The construction
follows the explicit polynomial route: inner packing over the genus-one curve,
cubic degeneration, relative quadric return, cubic bubble for the large ball, radial shell.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open Problem General

/-- The explicit embedding data in dimension six. -/
def data3 (k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData 3 k :=
  dataOfBallMaps C (ballMap C c) (enl C c) (rad C c)

/-- The explicit enlarged-source embeddings of the branch. -/
def embeddings (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData n k :=
  match n with
  | 3 => data3 k C c
  | _ => ⟨fun _ => id, fun _ => 0, fun _ => 0⟩

/-- The embeddings of the branch satisfy the interface specification. -/
theorem embeddings_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    (hn : n = 3) (hk : 1 ≤ k) (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hpair : ∀ i j, i ≠ j → c i + c j < C) (hvol : ∑ i, c i ^ n < C ^ n)
    (hlarge : ∃ j, C ≤ 2 * c j) :
    EmbeddingSpec n k C c (embeddings n k C c) := by
  subst hn
  have h : Hyp k C c := ⟨hk, hC, hc, hpair, hvol, hlarge⟩
  obtain ⟨hF, hinto, hdisj⟩ := ballMaps_spec h
  exact embeddingSpec_of_ballMaps hC (ballMap C c) (enl C c) (rad C c) hF hinto hdisj
    (lt_enl h) (enl_lt_rad h)

end SymplecticPacking.BranchLarge3
