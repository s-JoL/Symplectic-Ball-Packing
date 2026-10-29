import SymplecticPacking.Branch2.Bridge
import SymplecticPacking.Branch2.Model.Unequal
import SymplecticPacking.Branch2.Model.Embed

/-!
# Branch n = 2, general capacities: assembly (`thm:cub-packing`, `def:ham-normalise`)

Normalise by the target capacity, `ρ_i = c_i/C`, build the cubic-model data
`D = cubicDataOf ρ` (`Model/Unequal.lean`) and conjugate the capacity-scale embeddings
`f_i^cap = D.fcapGen i` (`Model/Embed.lean`) by the single dilation `u ↦ √C u`:
`f_i(u) = √C f_{i+1}^cap(u/√C)`, enlarged capacity `C ρ̄_i`, domain capacity `C ρ̂_i`.
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Set Problem General
open scoped Real ContDiff

/-- Normalised capacities `ρ_i = c_i/C`. -/
def normCap {k : ℕ} (C : ℝ) (c : Fin k → ℝ) : Fin k → ℝ := fun i => c i / C

/-- The embeddings `f_i(u) = √C f_{i+1}^cap(u/√C)` of cubic data `D`, with enlarged and domain
capacities `enl i`, `dom i`. -/
def cubicEmbeddings (k : ℕ) (C : ℝ) (D : CubicData) (enl dom : Fin k → ℝ) : EmbeddingData 2 k :=
  ⟨fun i u => Real.sqrt C • D.fcapGen (i.val + 1) ((Real.sqrt C)⁻¹ • u), enl, dom⟩

/-- The embeddings of valid cubic data satisfy the interface specification as soon as
`c_i < enl_i < dom_i ≤ C ρ̂_{i+1}` and `D` has at least `k` balls. -/
theorem cubicEmbeddings_spec {k : ℕ} {C : ℝ} {c : Fin k → ℝ} {D : CubicData} (hD : D.Valid)
    (hC : 0 < C) (hk : k ≤ D.k) {enl dom : Fin k → ℝ} (hlt : ∀ i, c i < enl i)
    (hle : ∀ i, enl i < dom i) (hdom : ∀ i, dom i ≤ C * D.rhoHat (i.val + 1)) :
    EmbeddingSpec 2 k C c (cubicEmbeddings k C D enl dom) := by
  have hμ : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hμ2 : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC.le
  have hidx : ∀ i : Fin k, 1 ≤ i.val + 1 ∧ i.val + 1 ≤ D.k := fun i => ⟨by omega, by omega⟩
  -- the open domain ball lies in the source ball `{π‖X‖² < ρ̂_{i+1}}`
  have hsrc : ∀ i X, π * ‖X‖ ^ 2 < dom i / Real.sqrt C ^ 2 → X ∈ D.srcBallGen (i.val + 1) :=
    fun i X hX => by
      rw [hμ2, lt_div_iff₀ hC] at hX
      show π * ‖X‖ ^ 2 < D.rhoHat (i.val + 1)
      nlinarith [hdom i]
  have hcl : ∀ i, {X : E4 | π * ‖X‖ ^ 2 ≤ enl i / Real.sqrt C ^ 2} ⊆ D.srcBallGen (i.val + 1) :=
    fun i X hX => hsrc i X (lt_of_le_of_lt hX (div_lt_div_of_pos_right (hle i) (by positivity)))
  apply scaled_spec hμ _ enl dom hlt hle
  · exact fun i X hX => hD.fcapGen_smooth (hidx i).1 (hidx i).2 (hsrc i X hX)
  · exact fun i X hX => hD.fcapGen_symplectic (hidx i).1 (hidx i).2 (hsrc i X hX)
  · exact fun i => (hD.fcapGen_injective (hidx i).1 (hidx i).2).mono (hcl i)
  · intro i j hij
    have hij' : i.val + 1 ≠ j.val + 1 := fun h => hij (Fin.ext (by omega))
    exact (hD.fcapGen_disjoint (hidx i).1 (hidx i).2 (hidx j).1 (hidx j).2 hij').mono
      (image_mono (hcl i)) (image_mono (hcl j))
  · intro i X hX
    rw [hμ2, div_self hC.ne']
    exact hD.fcapGen_mem_ball (hidx i).1 (hidx i).2 (hcl i hX)

/-- **The general-case embeddings** `f_i(u) = √C f_{i+1}^cap(u/√C)`, enlarged capacity `C ρ̄_i`,
domain capacity `C ρ̂_i`. -/
def embeddingsGen (k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData 2 k :=
  cubicEmbeddings k C (cubicDataOf (normCap C c))
    (fun i => C * (cubicDataOf (normCap C c)).rhoBar (i.val + 1))
    (fun i => C * (cubicDataOf (normCap C c)).rhoHat (i.val + 1))

theorem normCap_hyp {k : ℕ} {C : ℝ} {c : Fin k → ℝ} (hk : 1 ≤ k) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) (hthird : ∀ i, 3 * c i < C) (hvol : ∑ i, c i ^ 2 < C ^ 2) :
    Hyp (normCap C c) where
  one_le := hk
  pos := fun i => div_pos (hc i) hC
  third := fun i => by
    show c i / C < 1 / 3
    rw [div_lt_iff₀ hC]; linarith [hthird i]
  vol := by
    show ∑ i, (c i / C) ^ 2 < 1
    simp only [div_pow]
    rw [← Finset.sum_div, div_lt_one (by positivity)]
    exact hvol

/-- **General case of `embeddings_spec`.** -/
theorem embeddingsGen_spec {k : ℕ} {C : ℝ} {c : Fin k → ℝ} (hk : 1 ≤ k) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) (hthird : ∀ i, 3 * c i < C) (hvol : ∑ i, c i ^ 2 < C ^ 2) :
    EmbeddingSpec 2 k C c (embeddingsGen k C c) := by
  have hD := (normCap_hyp hk hC hc hthird hvol).cubicDataOf_valid
  set D := cubicDataOf (normCap C c)
  refine cubicEmbeddings_spec hD hC le_rfl (fun i => ?_) (fun i => ?_) (fun i => le_rfl)
  · have := hD.rho_lt_rhoBar (i := i.val + 1) (by omega) i.isLt
    have e : D.rho (i.val + 1) = c i / C := natIdx_succ _ i
    rw [e, div_lt_iff₀ hC] at this
    linarith
  · exact mul_lt_mul_of_pos_left (hD.rhoBar_lt_rhoHat (by omega) i.isLt) hC

end SymplecticPacking.Branch2
