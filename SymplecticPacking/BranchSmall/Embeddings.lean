import SymplecticPacking.General.Interface
import SymplecticPacking.BranchSmall.Normalized
import SymplecticPacking.HighDim.Rescale

/-!
# Branch n ≥ 3, all c_i < C/2 (complete-intersection curves, vector normal model)

`embeddings` and `embeddings_spec` are the interface used by `SymplecticPacking.General.Main`.
The definition is total (it does not take the hypotheses); `embeddings_spec` states its
properties under the branch hypotheses.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Problem General

/-- The explicit enlarged-source embeddings of the branch: the normalised maps
`BranchSmall.normalized` for `ρ_i = c_i / C`, conjugated to `ℝ^{2n}` (`AmbientPacking.toData`)
and rescaled by `√C` (`HighDim.scaleData`). For `n < 3` the value is irrelevant. -/
def embeddings (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData n k :=
  match n with
  | m + 3 => HighDim.scaleData C (normalized m (rho C c)).toData
  | _ => ⟨fun _ => id, fun _ => 0, fun _ => 0⟩

attribute [local irreducible] normalized

/-- The embeddings of the branch satisfy the interface specification. -/
theorem embeddings_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hsmall : ∀ i, 2 * c i < C) (hvol : ∑ i, c i ^ n < C ^ n) :
    EmbeddingSpec n k C c (embeddings n k C c) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  change EmbeddingSpec (m + 3) k C c
    (HighDim.scaleData C (normalized m (rho C c)).toData)
  have hρ : Hyp (m + 3) (rho C c) :=
    hyp_of_input (n := m + 3) (C := C) (c := c) hn hk hC hc hsmall hvol
  have hp : (normalized m (rho C c)).Spec 1 (rho C c) :=
    normalized_spec (m := m) (ρ := rho C c) hρ
  have hd : EmbeddingSpec (m + 3) k 1 (rho C c) (normalized m (rho C c)).toData :=
    HighDim.AmbientPacking.toData_spec (n := m + 3) (k := k)
      (P := normalized m (rho C c)) (C := 1) (c := rho C c) hp
  exact HighDim.scaleData_spec (n := m + 3) (k := k) (C := C) (c := c)
    (D := (normalized m (rho C c)).toData) hC hd

end SymplecticPacking.BranchSmall
