import SymplecticPacking.Branch2.Unequal

/-!
# Branch n = 2, equal capacities: the linear comparison datum

For `k ≥ 10` equal capacities `c_i = c` with `3/4 < (c/C)√k < 1` the cubic model is run on the
closed-form data `CubicData.ofParams P` of the four-dimensional construction (linear comparison
function `K(p) = (3√k - 9)p`, `prop:cmp-linear`), with `ε = 4(1 - (c/C)√k) ∈ (0,1)`, so that
`ρ = (1 - ε/4)/√k = c/C`. The embeddings are `f_i(u) = √C f_{i+1}^cap(u/√C)`
(`cubicEmbeddings`), with enlarged capacity `c r₃²` and domain capacity `c r₄² = C ρ̄`.
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Metric Set Problem General
open scoped ContDiff Real

/-- The equal case of branch `n = 2`: `k ≥ 10`, all capacities equal, and `3/4 < (c_i/C)√k < 1`. -/
def EqualCase (k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Prop :=
  10 ≤ k ∧ (∀ i j, c i = c j) ∧ ∀ i, 3 / 4 < c i / C * Real.sqrt k ∧ c i / C * Real.sqrt k < 1

namespace EqualCase

variable {k : ℕ} {C : ℝ} {c : Fin k → ℝ}

/-- The common capacity `c = c_0`. -/
def cap (h : EqualCase k C c) : ℝ := c ⟨0, by have := h.1; omega⟩

/-- `ε = 4(1 - (c/C)√k)`. -/
def eps (h : EqualCase k C c) : ℝ := 4 * (1 - h.cap / C * Real.sqrt k)

lemma eps_pos (h : EqualCase k C c) : 0 < h.eps := by
  have := (h.2.2 ⟨0, by have := h.1; omega⟩).2; unfold eps cap; linarith

lemma eps_lt_one (h : EqualCase k C c) : h.eps < 1 := by
  have := (h.2.2 ⟨0, by have := h.1; omega⟩).1; unfold eps cap; linarith

/-- The parameters `(k, ε)` of the four-dimensional construction. -/
def params (h : EqualCase k C c) : Params := ⟨k, h.eps, h.1, h.eps_pos, h.eps_lt_one⟩

end EqualCase

open EqualCase in
/-- **The equal-case embeddings** `f_i(u) = √C f_{i+1}^cap(u/√C)` for the data `ofParams P`. -/
def embeddingsEq (k : ℕ) (C : ℝ) (c : Fin k → ℝ) (h : EqualCase k C c) : EmbeddingData 2 k :=
  cubicEmbeddings k C (CubicData.ofParams h.params) (fun _ => h.cap * h.params.r3 ^ 2)
    (fun _ => h.cap * h.params.r4 ^ 2)

/-! ### The specification -/

namespace EqualCase

variable {k : ℕ} {C : ℝ} {c : Fin k → ℝ} (h : EqualCase k C c)

lemma cap_eq (i : Fin k) : c i = h.cap := h.2.1 i _

/-- `ρ = c/C`. -/
lemma params_rho (hC : 0 < C) : h.params.rho = h.cap / C := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 (by have := h.1; exact_mod_cast (by omega : 0 < k))
  show (1 - h.eps / 4) / Real.sqrt (k : ℝ) = h.cap / C
  unfold eps
  field_simp
  ring

end EqualCase

open EqualCase in
/-- **Equal case of `Branch2.embeddings_spec`.** -/
theorem embeddingsEq_spec {k : ℕ} {C : ℝ} {c : Fin k → ℝ} (h : EqualCase k C c) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) : EmbeddingSpec 2 k C c (embeddingsEq k C c h) := by
  set P := h.params
  obtain ⟨h1, h12, h23, h34, -, -⟩ := P.radii_chain
  have hcap : 0 < h.cap := hc _
  have hρ : h.cap = C * P.rho := by rw [h.params_rho hC]; field_simp
  have hr4 : P.rho * P.r4 ^ 2 = P.rhoBar := by
    rw [P.r4_sq]; unfold Params.rhoBar; field_simp [P.rho_pos.ne']
  refine cubicEmbeddings_spec (CubicData.ofParams_valid P) hC le_rfl (fun i => ?_) (fun i => ?_)
    (fun i => ?_)
  · rw [h.cap_eq i]
    have : 1 < P.r3 ^ 2 := by nlinarith
    nlinarith
  · have : P.r3 ^ 2 < P.r4 ^ 2 := by nlinarith
    nlinarith
  · have hlt := (CubicData.ofParams_valid P).rhoBar_lt_rhoHat (i := i.val + 1) (by omega)
      (show i.val + 1 ≤ P.k from i.isLt)
    have e : (CubicData.ofParams P).rhoBar (i.val + 1) = P.rhoBar := rfl
    rw [e] at hlt
    rw [hρ, mul_assoc, hr4]
    exact (mul_lt_mul_of_pos_left hlt hC).le

end SymplecticPacking.Branch2
