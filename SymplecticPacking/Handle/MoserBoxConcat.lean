import Mathlib
import SymplecticPacking.Handle.MoserBox
import SymplecticPacking.Handle.MoserConcat

/-!
# Concatenation of Moser stages without periodicity

`sec:shd-four` (`cons:shd4-moser`): concatenation of three Moser stages by the flat clocks of
`Handle/MoserConcat.lean` (`clock`, `dclock`), and deck maps for the concatenated path.

* `MoserStageB M`: one stage `s ↦ (Ω_s, a_s)` with the hypotheses of `MoserBoxData` for
  `s ∈ [0, 1]`; `concat3B` concatenates three stages with matching endpoints;
* `moserPathB`, `moserVariationB`: the concatenated path and its primitive; at each time only
  one stage is active (`moserPathB_cases`);
* `preserves_concat`: a deck map preserving every stage preserves the concatenated path.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Filter Topology Set ContinuousLinearMap
open SymplecticPacking.Forms (e pf Form1 Form2 d1 IsClosed2 d1_add_apply d1_smul_const)
open SymplecticPacking.Bundle (pE dpE)
open scoped ContDiff

variable {M : MoserParams}

/-- One stage of the Moser path (hypotheses for the parameter `s ∈ [0, 1]`), no periodicity. -/
structure MoserStageB (M : MoserParams) where
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

/-! ### The concatenated path -/

section concat

variable (S : Fin 3 → MoserStageB M)

/-- **The concatenated path** `Ω^M_t` (`cons:shd4-moser`). -/
def moserPathB (t : ℝ) : Form2 E4 :=
  (S 0).Om (clock 0 t) + ((S 1).Om (clock 1 t) - (S 1).Om 0) +
    ((S 2).Om (clock 2 t) - (S 2).Om 0)

/-- **The concatenated variation** `a_t` (`cons:shd4-moser`). -/
def moserVariationB (t : ℝ) : Form1 E4 :=
  dclock 0 t • (S 0).a (clock 0 t) + dclock 1 t • (S 1).a (clock 1 t) +
    dclock 2 t • (S 2).a (clock 2 t)

variable {S}

/-- At each time exactly one stage is active. -/
theorem moserPathB_cases (h01 : (S 0).Om 1 = (S 1).Om 0) (h12 : (S 1).Om 1 = (S 2).Om 0)
    (t : ℝ) : ∃ i : Fin 3, ∃ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ,
      moserPathB S t = (S i).Om s ∧ moserVariationB S t = c • (S i).a s := by
  by_cases t1 : t ≤ 1 / 3
  · refine ⟨0, clock 0 t, clock_mem 0 t, dclock 0 t, ?_, ?_⟩
    · simp only [moserPathB, clock_zero (i := 1) (by push_cast; linarith),
        clock_zero (i := 2) (by push_cast; linarith)]
      abel
    · simp only [moserVariationB, dclock_zero (i := 1) (Or.inl (by push_cast; linarith)),
        dclock_zero (i := 2) (Or.inl (by push_cast; linarith)), zero_smul, add_zero]
  by_cases t2 : t ≤ 2 / 3
  · refine ⟨1, clock 1 t, clock_mem 1 t, dclock 1 t, ?_, ?_⟩
    · simp only [moserPathB, clock_one (i := 0) (by push_cast; linarith),
        clock_zero (i := 2) (by push_cast; linarith), h01]
      abel
    · simp only [moserVariationB, dclock_zero (i := 0) (Or.inr (by push_cast; linarith)),
        dclock_zero (i := 2) (Or.inl (by push_cast; linarith)), zero_smul, add_zero, zero_add]
  · refine ⟨2, clock 2 t, clock_mem 2 t, dclock 2 t, ?_, ?_⟩
    · simp only [moserPathB, clock_one (i := 0) (by push_cast; linarith),
        clock_one (i := 1) (by push_cast; linarith), h01, h12]
      abel
    · simp only [moserVariationB, dclock_zero (i := 0) (Or.inr (by push_cast; linarith)),
        dclock_zero (i := 1) (Or.inr (by push_cast; linarith)), zero_smul, zero_add]

lemma moserPathB_zero : moserPathB S 0 = (S 0).Om 0 := by
  simp only [moserPathB, clock_zero (i := 0) (t := 0) (by norm_num),
    clock_zero (i := 1) (t := 0) (by norm_num), clock_zero (i := 2) (t := 0) (by norm_num)]
  abel

lemma moserPathB_one (h01 : (S 0).Om 1 = (S 1).Om 0) (h12 : (S 1).Om 1 = (S 2).Om 0) :
    moserPathB S 1 = (S 2).Om 1 := by
  simp only [moserPathB, clock_one (i := 0) (t := 1) (by norm_num),
    clock_one (i := 1) (t := 1) (by norm_num), clock_one (i := 2) (t := 1) (by norm_num), h01,
    h12]
  abel

lemma moserVariationB_time {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : moserVariationB S t = 0 := by
  have h : ∀ i : ℕ, i ≤ 2 → dclock i t = 0 := by
    intro i hi
    have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast hi
    apply dclock_zero
    rcases not_and_or.mp ht with h | h
    · left; push Not at h; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · right; push Not at h; linarith
  simp only [moserVariationB, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), zero_smul,
    add_zero]

lemma stageB_diff_a (T : MoserStageB M) (s : ℝ) : Differentiable ℝ (T.a s) :=
  (T.smooth_a.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)

/-- `∂_t Ω^M_t = d a_t`. -/
lemma moserPathB_dt (t : ℝ) (x v w : E4) :
    HasDerivAt (fun r => moserPathB S r x v w) (d1 (moserVariationB S t) x v w) t := by
  have hs : ∀ (i : Fin 3) (k : ℕ), HasDerivAt (fun r => (S i).Om (clock k r) x v w)
      (d1 ((S i).a (clock k t)) x v w * dclock k t) t := fun i k =>
    ((S i).dt (clock k t) x v w).comp t (hasDerivAt_clock k t)
  have h := ((hs 0 0).add ((hs 1 1).sub_const ((S 1).Om 0 x v w))).add
    ((hs 2 2).sub_const ((S 2).Om 0 x v w))
  have dd : ∀ (i : Fin 3) (k : ℕ), DifferentiableAt ℝ (dclock k t • (S i).a (clock k t)) x :=
    fun i k => ((stageB_diff_a (S i) _) x).const_smul _
  have hd : d1 (moserVariationB S t) x = dclock 0 t • d1 ((S 0).a (clock 0 t)) x +
      dclock 1 t • d1 ((S 1).a (clock 1 t)) x + dclock 2 t • d1 ((S 2).a (clock 2 t)) x := by
    unfold moserVariationB
    rw [d1_add_apply ((dd 0 0).add (dd 1 1)) (dd 2 2), d1_add_apply (dd 0 0) (dd 1 1),
      d1_smul_const, d1_smul_const, d1_smul_const]
    rfl
  have e : d1 (moserVariationB S t) x v w = d1 ((S 0).a (clock 0 t)) x v w * dclock 0 t +
      d1 ((S 1).a (clock 1 t)) x v w * dclock 1 t +
      d1 ((S 2).a (clock 2 t)) x v w * dclock 2 t := by
    rw [hd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact h

lemma moserPathB_smooth : ContDiff ℝ ∞ (fun q : ℝ × E4 => moserPathB S q.1 q.2) := by
  have hs : ∀ i : Fin 3, ContDiff ℝ ∞ (fun q : ℝ × E4 => (S i).Om (clock i q.1) q.2) := fun i =>
    (S i).smooth_Om.comp (((contDiff_clock i).comp contDiff_fst).prodMk contDiff_snd)
  have hc : ∀ i : Fin 3, ContDiff ℝ ∞ (fun q : ℝ × E4 => (S i).Om 0 q.2) := fun i =>
    (S i).smooth_Om.comp (contDiff_const.prodMk contDiff_snd)
  exact ((hs 0).add ((hs 1).sub (hc 1))).add ((hs 2).sub (hc 2))

lemma moserVariationB_smooth : ContDiff ℝ ∞ (fun q : ℝ × E4 => moserVariationB S q.1 q.2) := by
  have hs : ∀ i : Fin 3, ContDiff ℝ ∞
      (fun q : ℝ × E4 => dclock i q.1 • (S i).a (clock i q.1) q.2) := fun i =>
    ((contDiff_dclock i).comp contDiff_fst).smul
      ((S i).smooth_a.comp (((contDiff_clock i).comp contDiff_fst).prodMk contDiff_snd))
  exact ((hs 0).add (hs 1)).add (hs 2)

/-- **The concatenated Moser data** (`cons:shd4-moser`), box version. -/
def concat3B (S : Fin 3 → MoserStageB M) (h01 : (S 0).Om 1 = (S 1).Om 0)
    (h12 : (S 1).Om 1 = (S 2).Om 0) : MoserBoxData M where
  Om := moserPathB S
  a := moserVariationB S
  smooth_Om := moserPathB_smooth
  smooth_a := moserVariationB_smooth
  skew t x v w := by
    simp only [moserPathB, Pi.add_apply, Pi.sub_apply, add_apply, sub_apply]
    rw [(S 0).skew, (S 1).skew _ x v, (S 1).skew 0 x v, (S 2).skew _ x v, (S 2).skew 0 x v]
    ring
  closed t := by
    obtain ⟨i, s, hs, c, h1, -⟩ := moserPathB_cases h01 h12 t
    rw [h1]; exact (S i).closed s hs
  dt := moserPathB_dt
  nondeg t x hx := by
    obtain ⟨i, s, hs, c, h1, -⟩ := moserPathB_cases h01 h12 t
    rw [h1]; exact (S i).nondeg s hs x hx
  toric t x h1 h2 := by
    obtain ⟨i, s, hs, c, e1, -⟩ := moserPathB_cases h01 h12 t
    rw [e1]; exact (S i).toric s hs x h1 h2
  toric_a t x h1 h2 := by
    obtain ⟨i, s, hs, c, -, e2⟩ := moserPathB_cases h01 h12 t
    rw [e2]; simp [(S i).toric_a s hs x h1 h2]
  fibre t x hx := by
    obtain ⟨i, s, hs, c, -, e2⟩ := moserPathB_cases h01 h12 t
    rw [e2]; simp [(S i).fibre s hs x hx]
  time_supp t ht := moserVariationB_time ht

/-- **Deck maps for the concatenated path**: a deck map preserving all three stages (at all
parameters) preserves the concatenated path and variation. -/
theorem preserves_concat {S : Fin 3 → MoserStageB M} (T : DeckCore)
    (hT : ∀ i, T.Preserves (S i).Om (S i).a) :
    T.Preserves (moserPathB S) (moserVariationB S) := by
  refine ⟨fun t x v w => ?_, fun t x v => ?_⟩
  · simp only [moserPathB, Pi.add_apply, Pi.sub_apply, add_apply, sub_apply, (hT 0).1,
      (hT 1).1, (hT 2).1]
  · simp only [moserVariationB, Pi.add_apply, Pi.smul_apply, add_apply, smul_apply,
      (hT 0).2, (hT 1).2, (hT 2).2]

end concat

end SymplecticPacking.Handle
