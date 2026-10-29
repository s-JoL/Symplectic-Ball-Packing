import SymplecticPacking.Branch2.Equal
import SymplecticPacking.Branch2.Unequal

/-!
# Branch n = 2: all 3c_i < C, Σ c_i² < C² (Fermat cubic normal model)

`embeddings` and `embeddings_spec` are the interface used by `SymplecticPacking.General.Main`.
The definition is total (it does not take the hypotheses); `embeddings_spec` states its
properties under the branch hypotheses.

Dispatch (a case distinction on a proposition, allowed at level L1):
* `EqualCase k C c` (`k ≥ 10`, equal capacities, `3/4 < (c/C)√k < 1`): the closed-form linear
  comparison datum of the four-dimensional construction (`Branch2/Equal.lean`);
* otherwise: the finite comparator, the general planar realisation and the cubic model for
  general data (`Branch2/Unequal.lean`).
For `n ≠ 2` the value is irrelevant (the branch is selected only for `n = 2`).
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Problem General

/-- The branch for `n = 2`. -/
def embeddings2 (k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData 2 k :=
  open Classical in
  if h : EqualCase k C c then embeddingsEq k C c h else embeddingsGen k C c

/-- The explicit enlarged-source embeddings of the branch. -/
def embeddings (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData n k :=
  if h : n = 2 then h ▸ embeddings2 k C c else ⟨fun _ => id, fun _ => 0, fun _ => 0⟩

theorem embeddings2_spec {k : ℕ} {C : ℝ} {c : Fin k → ℝ} (hk : 1 ≤ k) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) (hthird : ∀ i, 3 * c i < C) (hvol : ∑ i, c i ^ 2 < C ^ 2) :
    EmbeddingSpec 2 k C c (embeddings2 k C c) := by
  unfold embeddings2
  split_ifs with h
  · exact embeddingsEq_spec h hC hc
  · exact embeddingsGen_spec hk hC hc hthird hvol

/-- The embeddings of the branch satisfy the interface specification. -/
theorem embeddings_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    (hn : n = 2) (hk : 1 ≤ k) (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hthird : ∀ i, 3 * c i < C) (hvol : ∑ i, c i ^ 2 < C ^ 2) :
    EmbeddingSpec n k C c (embeddings n k C c) := by
  subst hn
  unfold embeddings
  rw [dif_pos rfl]
  exact embeddings2_spec hk hC hc hthird hvol

end SymplecticPacking.Branch2
