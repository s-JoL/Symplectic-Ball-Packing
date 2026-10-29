import SymplecticPacking.Effective.Names

/-!
# Rational quadrature on the unit interval

Finite rational quadrature with a proved error bound on the unit interval.
-/

namespace SymplecticPacking.Effective

open Set MeasureTheory
open scoped BigOperators

namespace Quadrature

noncomputable def grid (N i : ℕ) : ℝ := (i : ℝ) / N

theorem grid_step {N : ℕ} (hN : 0 < N) (i : ℕ) :
    grid N (i + 1) - grid N i = 1 / (N : ℝ) := by
  simp only [grid, Nat.cast_add, Nat.cast_one]
  ring

theorem grid_mem {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    grid N i ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  exact ⟨div_nonneg (Nat.cast_nonneg _) hNr.le,
    (div_le_one hNr).mpr (by exact_mod_cast hi)⟩

theorem cell_error {f : ℝ → ℝ} (hf : Continuous f) {a b L : ℝ}
    (hab : a ≤ b)
    (hbound : ∀ x ∈ Icc a b, |f x - f a| ≤ L * (b - a)) :
    |(∫ x in a..b, f x) - (b - a) * f a| ≤ L * (b - a) ^ 2 := by
  have hint : IntervalIntegrable f volume a b := hf.intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f x - f a) (C := L * (b - a)) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      exact hbound x ⟨hx.1.le, hx.2⟩)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simpa only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (sub_nonneg.mpr hab),
    mul_assoc, ← pow_two] using h

noncomputable def realSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, f (grid N i)) / N

/-- The left rectangle rule needs only a Lipschitz bound on the integration interval. -/
theorem realSum_error {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|) {N : ℕ} (hN : 0 < N) :
    |(∫ x in (0 : ℝ)..1, f x) - realSum f N| ≤ L / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcell (i : ℕ) (hi : i ∈ Finset.range N) :
      |(∫ x in grid N i..grid N (i + 1), f x) - (1 / (N : ℝ)) * f (grid N i)| ≤
        L / (N : ℝ) ^ 2 := by
    have hiN := Finset.mem_range.mp hi
    have ha := grid_mem hN hiN.le
    have hb := grid_mem hN (Nat.succ_le_iff.mpr hiN)
    have hab : grid N i ≤ grid N (i + 1) := by
      rw [← sub_nonneg, grid_step hN]
      positivity
    have herr := cell_error hf hab (L := L) (by
      intro x hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
      have hdist : |x - grid N i| ≤ grid N (i + 1) - grid N i := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
        linarith [hx.2]
      exact (hlip x hx01 _ ha).trans (mul_le_mul_of_nonneg_left hdist hL))
    rw [grid_step hN] at herr
    convert herr using 1 <;> field_simp
  have hsum : (∑ i ∈ Finset.range N, ∫ x in grid N i..grid N (i + 1), f x) =
      ∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := grid N) (n := N) (μ := volume) (fun _ _ => hf.intervalIntegrable _ _)
    simpa only [grid, Nat.cast_zero, zero_div, div_self hNr.ne'] using h
  have herr := (Finset.abs_sum_le_sum_abs
    (fun i => (∫ x in grid N i..grid N (i + 1), f x) -
      (1 / (N : ℝ)) * f (grid N i)) (Finset.range N)).trans
        (Finset.sum_le_sum hcell)
  rw [Finset.sum_sub_distrib, hsum, ← Finset.mul_sum] at herr
  have hcancel : (N : ℝ) * (L / (N : ℝ) ^ 2) = L / N := by
    field_simp
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, ← div_eq_inv_mul,
    realSum, hcancel] using herr

/-- Every operation in this finite sum is rational arithmetic or a query to the
supplied value-name evaluator. -/
def rationalSum (q : ℚ → ℕ → ℚ) (N n : ℕ) : ℚ :=
  (∑ i ∈ Finset.range N, q ((i : ℚ) / N) n) / N

theorem rationalSum_sample_error {q : ℚ → ℕ → ℚ} {f : ℝ → ℝ}
    {N n : ℕ} (hN : 0 < N) {e : ℝ}
    (hq : ∀ i < N, |(q ((i : ℚ) / N) n : ℝ) - f (grid N i)| ≤ e) :
    |(rationalSum q N n : ℝ) - realSum f N| ≤ e := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h := (Finset.abs_sum_le_sum_abs
    (fun i : ℕ => (q ((i : ℚ) / N) n : ℝ) - f (grid N i)) (Finset.range N)).trans
      (Finset.sum_le_sum (fun i hi => hq i (Finset.mem_range.mp hi)))
  have heq : (rationalSum q N n : ℝ) - realSum f N =
      (∑ i ∈ Finset.range N, ((q ((i : ℚ) / N) n : ℝ) - f (grid N i))) / N := by
    simp only [rationalSum, realSum, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
      Finset.sum_sub_distrib, sub_div]
  rw [heq, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm e] using h

/-- Sample-error control for any finite rational list of queried values; this
allows the evaluator to use its original finite input codes without re-encoding. -/
theorem samples_error {f : ℝ → ℝ} (v : ℕ → ℚ) {N : ℕ} (hN : 0 < N) {e : ℝ}
    (hv : ∀ i < N, |(v i:ℝ)-f (grid N i)| ≤ e) :
    |((∑ i ∈ Finset.range N, v i : ℚ):ℝ)/(N:ℝ)-realSum f N| ≤ e := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have h := (Finset.abs_sum_le_sum_abs
    (fun i : ℕ => (v i:ℝ)-f (grid N i)) (Finset.range N)).trans
      (Finset.sum_le_sum (fun i hi => hv i (Finset.mem_range.mp hi)))
  have heq : ((∑ i ∈ Finset.range N, v i : ℚ):ℝ)/(N:ℝ)-realSum f N =
      (∑ i ∈ Finset.range N, ((v i:ℝ)-f (grid N i)))/(N:ℝ) := by
    simp only [realSum, Rat.cast_sum, Finset.sum_sub_distrib, sub_div]
  rw [heq, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm e] using h

def mesh (K n : ℕ) : ℕ := 2 ^ (n + K + 1)

theorem mesh_pos (K n : ℕ) : 0 < mesh K n := by unfold mesh; positivity

theorem mesh_error {L : ℝ} {K : ℕ} (hL : L ≤ (2 : ℝ) ^ K) (n : ℕ) :
    L / (mesh K n : ℝ) ≤ (radius (n + 1) : ℝ) := by
  rw [radius_cast, div_pow, one_pow]
  have hden : (0 : ℝ) < mesh K n := Nat.cast_pos.mpr (mesh_pos K n)
  rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 2 ^ (n + 1))]
  have heq : (mesh K n : ℝ) = (2 : ℝ) ^ K * 2 ^ (n + 1) := by
    simp only [mesh, Nat.cast_pow, Nat.cast_ofNat]
    rw [show n + K + 1 = K + (n + 1) by omega, pow_add]
  rw [heq, one_mul]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

def integralName (q : ℚ → ℕ → ℚ) (K n : ℕ) : ℚ :=
  rationalSum q (mesh K n) (n + 1)

/-- This is a rational name of the integral, with a finite, explicit number
of value queries at each requested precision. -/
theorem integralName_spec {q : ℚ → ℕ → ℚ} {f : ℝ → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|)
    (hq : ∀ x : ℚ, Names (q x) (f x)) {K : ℕ} (hK : L ≤ (2 : ℝ) ^ K) :
    Names (integralName q K) (∫ x in (0 : ℝ)..1, f x) := by
  intro n
  have hs := rationalSum_sample_error (mesh_pos K n) (n := n + 1)
    (f := f) (e := (radius (n + 1) : ℝ)) (by
      intro i _
      simpa only [grid, Rat.cast_div, Rat.cast_natCast] using hq ((i : ℚ) / mesh K n) (n + 1))
  have hi := realSum_error hf hL hlip (mesh_pos K n)
  have hm := mesh_error hK n
  have hrad : (radius (n + 1) : ℝ) = (radius n : ℝ) / 2 := by
    exact_mod_cast radius_succ n
  have htriangle := abs_sub_le (rationalSum q (mesh K n) (n + 1) : ℝ)
    (realSum f (mesh K n)) (∫ x in (0 : ℝ)..1, f x)
  rw [abs_sub_comm (realSum f (mesh K n))] at htriangle
  change |(rationalSum q (mesh K n) (n + 1) : ℝ) - (∫ x in (0 : ℝ)..1, f x)| ≤ _
  linarith

end Quadrature
end SymplecticPacking.Effective
