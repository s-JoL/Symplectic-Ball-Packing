import SymplecticPacking.Params

/-!
# Constants of the inner map

Scalar facts about the Morse function `R` of the unpatched inner map, including
`0 < pstar < h`.
-/

noncomputable section

namespace SymplecticPacking

namespace Params

variable (P : Params)

def m : ℝ := (P.B - P.A) / 2
def n : ℝ := (P.A + P.B) / 2
def r : ℝ := Real.sqrt (P.A * P.B)
/-- `η = e/(8n)` with `e = e_q`. -/
def eta : ℝ := P.eq_ / (8 * P.n)
def xstar : ℝ := -P.m * P.eta / P.r
def pstar : ℝ := P.a + P.xstar
/-- `δ = e/8`. -/
def delta : ℝ := P.eq_ / 8

/-- `R(x) = m(x* + x) + n √((x*+x)² + η²) - η r`. -/
def Rmorse (x : ℝ) : ℝ :=
  P.m * (P.xstar + x) + P.n * Real.sqrt ((P.xstar + x) ^ 2 + P.eta ^ 2) - P.eta * P.r

lemma n_pos : 0 < P.n := by unfold n; linarith [P.A_pos, P.B_pos]
lemma r_pos : 0 < P.r := Real.sqrt_pos.mpr (mul_pos P.A_pos P.B_pos)
lemma eta_pos : 0 < P.eta := div_pos P.eq_pos (by linarith [P.n_pos])

lemma r_sq : P.r ^ 2 = P.A * P.B := Real.sq_sqrt (mul_pos P.A_pos P.B_pos).le

/-- `n² - m² = r²`. -/
lemma n_sq_sub_m_sq : P.n ^ 2 - P.m ^ 2 = P.r ^ 2 := by rw [P.r_sq]; unfold n m; ring

lemma r_le_n : P.r ≤ P.n := by
  have h := P.n_sq_sub_m_sq
  nlinarith [sq_nonneg P.m, P.r_pos, P.n_pos]

/-- `Rcal(x) = m (x - a) + n |x - a|`. -/
lemma Rcal_eq (x : ℝ) : P.Rcal x = P.m * (x - P.a) + P.n * |x - P.a| := by
  unfold Rcal m n
  split_ifs with hx
  · rw [abs_of_nonpos (by linarith)]; ring
  · rw [abs_of_pos (by rw [not_le] at hx; linarith)]; ring

/-- `R(0) = 0`. -/
theorem Rmorse_zero : P.Rmorse 0 = 0 := by
  have hr := P.r_pos
  have hn := P.n_pos
  have he := P.eta_pos
  have hsq : P.xstar ^ 2 + P.eta ^ 2 = (P.eta * P.n / P.r) ^ 2 := by
    unfold xstar
    have := P.n_sq_sub_m_sq
    field_simp
    nlinarith
  unfold Rmorse
  rw [add_zero, hsq, Real.sqrt_sq (by positivity)]
  unfold xstar
  field_simp
  nlinarith [P.n_sq_sub_m_sq]

/-- `|R(x - pstar) - Rcal(x)| ≤ δ` for every real `x`. -/
theorem Rmorse_close (x : ℝ) : |P.Rmorse (x - P.pstar) - P.Rcal x| ≤ P.delta := by
  have hn := P.n_pos
  have he := P.eta_pos
  have hr := P.r_pos
  set y := x - P.a with hy
  have hxy : P.xstar + (x - P.pstar) = y := by unfold pstar; ring
  have hdiff : P.Rmorse (x - P.pstar) - P.Rcal x =
      P.n * (Real.sqrt (y ^ 2 + P.eta ^ 2) - |y|) - P.eta * P.r := by
    unfold Rmorse; rw [hxy, P.Rcal_eq]; ring
  have h0 : |y| ≤ Real.sqrt (y ^ 2 + P.eta ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : Real.sqrt (y ^ 2 + P.eta ^ 2) ≤ |y| + P.eta := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg y, sq_abs y]
  have hrn := P.r_le_n
  have hδ : P.eta * P.n = P.delta := by
    unfold eta delta; field_simp
  rw [hdiff, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **Audit supplement §12.2**: `Rcal(pstar) ≤ e/8 < h`, hence `0 < pstar < h`. -/
theorem pstar_mem : 0 < P.pstar ∧ P.pstar < P.h := by
  have hc := P.Rmorse_close P.pstar
  rw [sub_self, P.Rmorse_zero, zero_sub, abs_neg, abs_of_nonneg (P.Rcal_nonneg _)] at hc
  have hδh : P.delta < P.h := by
    unfold delta; have := P.eq_le_h; have := P.h_pos; linarith
  have hlt : P.Rcal P.pstar < P.h := lt_of_le_of_lt hc hδh
  have hAa : P.h / P.A = P.a := by
    unfold A; field_simp [P.h_pos.ne', P.a_pos.ne']
  have hBa : P.h / P.B = P.h - P.a := by
    unfold B; have : P.h - P.a ≠ 0 := by linarith [P.a_lt_h]
    field_simp [P.h_pos.ne']
  have hA := P.A_pos
  have hB := P.B_pos
  unfold Rcal at hlt
  split_ifs at hlt with hx
  · refine ⟨?_, by linarith [P.a_lt_h]⟩
    -- A (a - pstar) < h = A a
    have : P.A * (P.a - P.pstar) < P.A * P.a := by
      calc P.A * (P.a - P.pstar) < P.h := hlt
        _ = P.A * P.a := by rw [← hAa]; field_simp
    nlinarith
  · rw [not_le] at hx
    refine ⟨by linarith [P.a_pos], ?_⟩
    have : P.B * (P.pstar - P.a) < P.B * (P.h - P.a) := by
      calc P.B * (P.pstar - P.a) < P.h := hlt
        _ = P.B * (P.h - P.a) := by rw [← hBa]; field_simp
    nlinarith

end Params

end SymplecticPacking
