import Mathlib
import SymplecticPacking.Handle.MoserGeneric

/-!
# Flat clocks for concatenating Moser stages

`sec:shd-four` (`cons:shd4-moser`): the clocks `S_i(t) = S(9t − 3i − 1)`
(`S = Real.smoothTransition`, `clock i`) and their derivatives (`dclock i`), which move only on
`[(3i+1)/9, (3i+2)/9]` and are constant near the joins (`clock_zero`, `clock_one`,
`dclock_zero`). Three Moser stages with matching endpoints are concatenated with them in
`Handle/MoserBoxConcat.lean`.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Filter Topology Set ContinuousLinearMap
open SymplecticPacking.Forms (e pf Form1 Form2 d1 IsClosed2 d1_add_apply d1_smul_const)
open SymplecticPacking.Bundle (pE dpE)
open scoped ContDiff

variable {M : MoserParams}

/-- One stage of the Moser path (hypotheses for the parameter `s ∈ [0, 1]`). -/
structure MoserStage (M : MoserParams) where
  Om : ℝ → Form2 E4
  a : ℝ → Form1 E4
  smooth_Om : ContDiff ℝ ∞ (fun q : ℝ × E4 => Om q.1 q.2)
  smooth_a : ContDiff ℝ ∞ (fun q : ℝ × E4 => a q.1 q.2)
  skew : ∀ s x v w, Om s x v w = -Om s x w v
  closed : ∀ s ∈ Icc (0 : ℝ) 1, IsClosed2 (Om s)
  dt : ∀ s x v w, HasDerivAt (fun r => Om r x v w) (d1 (a s) x v w) s
  nondeg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, pE x < M.h + 2 * M.δ → pf (Om s x) ≠ 0
  toric : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, M.Ptor < pE x → pE x < M.h + 2 * M.δ →
    Om s x (M.R x) = -dpE x
  toric_a : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, M.Ptor < pE x → pE x < M.h + 2 * M.δ → a s x (M.R x) = 0
  fibre : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ M.F, a s x = 0
  per_Om : ∀ s x, Om s (x + e 2) = Om s x ∧ Om s (x + e 3) = Om s x
  per_a : ∀ s x, a s (x + e 2) = a s x ∧ a s (x + e 3) = a s x

/-! ### Flat clocks -/

/-- The clock of stage `i`: `S(9t − 3i − 1)`, moving only on `[(3i+1)/9, (3i+2)/9]`. -/
def clock (i : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (9 * t - (3 * i + 1))

/-- Its derivative. -/
def dclock (i : ℕ) (t : ℝ) : ℝ := deriv (clock i) t

lemma contDiff_clock (i : ℕ) : ContDiff ℝ ∞ (clock i) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma contDiff_dclock (i : ℕ) : ContDiff ℝ ∞ (dclock i) :=
  (contDiff_infty_iff_deriv.mp (contDiff_clock i)).2

lemma hasDerivAt_clock (i : ℕ) (t : ℝ) : HasDerivAt (clock i) (dclock i t) t :=
  ((contDiff_clock i).differentiable (by simp) t).hasDerivAt

lemma clock_mem (i : ℕ) (t : ℝ) : clock i t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_zero {i : ℕ} {t : ℝ} (h : 9 * t - (3 * i + 1) ≤ 0) : clock i t = 0 :=
  Real.smoothTransition.zero_of_nonpos h

lemma clock_one {i : ℕ} {t : ℝ} (h : 1 ≤ 9 * t - (3 * i + 1)) : clock i t = 1 :=
  Real.smoothTransition.one_of_one_le h

lemma dclock_zero {i : ℕ} {t : ℝ} (h : 9 * t - (3 * i + 1) < 0 ∨ 1 < 9 * t - (3 * i + 1)) :
    dclock i t = 0 := by
  rcases h with h | h
  · apply deriv_eq_zero_of_eventually_const (c := 0)
    have hO : {r : ℝ | 9 * r - (3 * i + 1) < 0} ∈ 𝓝 t :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds h
    filter_upwards [hO] with r hr using clock_zero (le_of_lt hr)
  · apply deriv_eq_zero_of_eventually_const (c := 1)
    have hO : {r : ℝ | 1 < 9 * r - (3 * i + 1)} ∈ 𝓝 t :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds h
    filter_upwards [hO] with r hr using clock_one (le_of_lt hr)

/-! ### The concatenated path -/

section concat

variable (S : Fin 3 → MoserStage M)

variable {S}

end concat

end SymplecticPacking.Handle
