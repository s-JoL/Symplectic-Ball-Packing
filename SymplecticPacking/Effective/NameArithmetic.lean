import SymplecticPacking.Effective.RationalArithmetic
import SymplecticPacking.Effective.OracleCertificates

/-!
# Arithmetic on rational-code names

Sums, negatives, halves, absolute values, maxima and products of names, relative to the same
input oracles.
-/

namespace SymplecticPacking.Effective
namespace CodeName

open RationalCode

def Names (q : ℕ → ℕ) (x : ℝ) : Prop := Effective.Names (fun n => value (q n)) x

def add (q r : ℕ → ℕ) (n : ℕ) : ℕ := addCode (q (n + 1)) (r (n + 1))
def neg (q : ℕ → ℕ) (n : ℕ) : ℕ := negCode (q n)
def half (q : ℕ → ℕ) (n : ℕ) : ℕ := divideNatCode (q n) 1
def absolute (q : ℕ → ℕ) (n : ℕ) : ℕ := absCode (q n)
def maximum (q r : ℕ → ℕ) (n : ℕ) : ℕ := maxCode (q n) (r n)

/-- A magnitude bound uses the rational value, including its denominator.
Large unnormalised representations do not inflate the requested precision. -/
def magnitude (u : ℕ) : ℕ :=
  ((positiveNumerator u-negativeNumerator u)+(negativeNumerator u-positiveNumerator u)) /
    denominator u+2

def productBudget (u v : ℕ) : ℕ := magnitude u+magnitude v+1

def mul (q r : ℕ → ℕ) (n : ℕ) : ℕ :=
  let K := productBudget (q 0) (r 0)
  mulCode (q (n + K)) (r (n + K))

theorem constant_spec (c : ℕ) : Names (fun _ => c) (value c) := names_rational (value c)

theorem add_spec {q r : ℕ → ℕ} {x y : ℝ} (hq : Names q x) (hr : Names r y) :
    Names (add q r) (x + y) := by
  intro n
  change |(value (addCode (q (n+1)) (r (n+1))) : ℝ) - (x+y)| ≤ _
  rw [value_addCode, Rat.cast_add]
  simpa only [addNames, Rat.cast_add] using (names_add hq hr n)

theorem neg_spec {q : ℕ → ℕ} {x : ℝ} (hq : Names q x) : Names (neg q) (-x) := by
  intro n
  change |(value (negCode (q n)) : ℝ) - -x| ≤ _
  rw [value_negCode, Rat.cast_neg]
  simpa only [negName, Rat.cast_neg] using (names_neg hq n)

theorem half_spec {q : ℕ → ℕ} {x : ℝ} (hq : Names q x) : Names (half q) (x / 2) := by
  intro n
  have hq0 := hq n
  have he : (0 : ℝ) ≤ (radius n : ℝ) := by exact_mod_cast (radius_pos n).le
  simp only [half, value_divideNatCode, Nat.cast_one, one_add_one_eq_two,
    Rat.cast_div, Rat.cast_ofNat]
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem abs_spec {q : ℕ → ℕ} {x : ℝ} (hq : Names q x) : Names (absolute q) |x| := by
  intro n
  change |(value (absCode (q n)) : ℝ) - (|x|)| ≤ _
  rw [value_absCode, Rat.cast_abs]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (hq n)

theorem max_spec {q r : ℕ → ℕ} {x y : ℝ} (hq : Names q x) (hr : Names r y) :
    Names (maximum q r) (Max.max x y) := by
  intro n
  change |(value (maxCode (q n) (r n)) : ℝ) - Max.max x y| ≤ _
  rw [value_maxCode, Rat.cast_max]
  obtain ⟨hq0, hq1⟩ := abs_le.mp (hq n)
  obtain ⟨hr0, hr1⟩ := abs_le.mp (hr n)
  have hqmax := le_max_left (value (q n) : ℝ) (value (r n))
  have hrmax := le_max_right (value (q n) : ℝ) (value (r n))
  have hxmax := le_max_left x y
  have hymax := le_max_right x y
  apply abs_le.mpr
  constructor
  · have h : Max.max x y ≤ Max.max (value (q n) : ℝ) (value (r n)) + (radius n : ℝ) :=
      max_le (by linarith) (by linarith)
    linarith
  · have h : Max.max (value (q n) : ℝ) (value (r n)) ≤ Max.max x y + (radius n : ℝ) :=
      max_le (by linarith) (by linarith)
    linarith

theorem value_abs_bound (u : ℕ) :
    |(value u : ℝ)| ≤ (positiveNumerator u : ℝ) + negativeNumerator u := by
  have hd : (1 : ℝ) ≤ denominator u := by
    exact_mod_cast (show 1 ≤ denominator u by unfold denominator; omega)
  have hn : |(positiveNumerator u : ℝ) - negativeNumerator u| ≤
      (positiveNumerator u : ℝ) + negativeNumerator u := by
    have ha : (0 : ℝ) ≤ positiveNumerator u := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ negativeNumerator u := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [value, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, abs_div,
    abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
  exact hn.trans (le_mul_of_one_le_right (by positivity) hd)

theorem value_abs_bound_magnitude (u : ℕ) : |(value u:ℝ)|+1 ≤ (magnitude u:ℝ) := by
  let N := (positiveNumerator u-negativeNumerator u)+(negativeNumerator u-positiveNumerator u)
  let D := denominator u
  have hD : 0 < D := denominator_pos u
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hden : ((D-1:ℕ):ℝ)+1 = D := by exact_mod_cast Nat.sub_add_cancel hD
  have habs : |(value u:ℝ)| = (N:ℝ)/(D:ℝ) := by
    have he := congrArg (fun v : ℚ => (v:ℝ)) (value_absCode u)
    rw [Rat.cast_abs] at he
    rw [← he, absCode, value_encode]
    simp only [Nat.cast_zero, sub_zero, Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
    rw [hden]
  have hlt : N < D*(N/D+1) := by
    have hm := Nat.mod_lt N hD
    have he := Nat.mod_add_div N D
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hreal : (N:ℝ) ≤ (D:ℝ)*((N/D:ℕ)+1) := by exact_mod_cast hlt.le
  have hdiv : (N:ℝ)/(D:ℝ) ≤ ((N/D:ℕ):ℝ)+1 := (div_le_iff₀ hDr).mpr (by nlinarith)
  rw [habs]
  change (N:ℝ)/(D:ℝ)+1 ≤ ((N/D+2:ℕ):ℝ)
  push_cast
  linarith

theorem named_abs_bound_magnitude {q : ℕ → ℕ} {x : ℝ} (hq : Names q x) :
    |x| ≤ (magnitude (q 0):ℝ) := by
  have he := hq 0
  simp only [radius, pow_zero, Rat.cast_one] at he
  have ht := abs_add_le (x-(value (q 0):ℝ)) (value (q 0):ℝ)
  rw [sub_add_cancel, abs_sub_comm] at ht
  linarith [value_abs_bound_magnitude (q 0)]

theorem mul_spec {q r : ℕ → ℕ} {x y : ℝ} (hq : Names q x) (hr : Names r y) :
    Names (mul q r) (x * y) := by
  intro n
  let K := productBudget (q 0) (r 0)
  let e : ℝ := radius (n + K)
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact_mod_cast (radius_pos (n + K)).le
  have he1 : e ≤ 1 := by
    dsimp [e]
    rw [radius_cast]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hK : |x| + |y| + 1 ≤ (K : ℝ) := by
    have hx := named_abs_bound_magnitude hq
    have hy := named_abs_bound_magnitude hr
    dsimp only [K, productBudget]
    push_cast
    linarith
  have hq0 := hq (n + K)
  have hr0 := hr (n + K)
  have hry : |(value (r (n + K)) : ℝ)| ≤ |y| + 1 := by
    have h := abs_add_le ((value (r (n + K)) : ℝ) - y) y
    rw [sub_add_cancel] at h
    linarith
  have herr : |(value (mul q r n) : ℝ) - x * y| ≤ (K : ℝ) * e := by
    have heq : (value (mul q r n) : ℝ) - x * y =
        ((value (q (n + K)) : ℝ) - x) * (value (r (n + K)) : ℝ) +
          x * ((value (r (n + K)) : ℝ) - y) := by
      simp only [mul, value_mulCode, Rat.cast_mul, K]
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    have hb1 := mul_le_mul hq0 hry (abs_nonneg _) he0
    have hb2 := mul_le_mul_of_nonneg_left hr0 (abs_nonneg x)
    nlinarith
  have hpow : (K : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast (show K < 2 ^ K from Nat.lt_two_pow_self).le
  have hcancel : (2 : ℝ) ^ K * e = (radius n : ℝ) := by
    dsimp [e]
    rw [radius_cast, radius_cast, pow_add]
    have hp : (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ K = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ K) =
          (1 / 2 : ℝ) ^ n * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ K) := by ring
      _ = (1 / 2 : ℝ) ^ n := by rw [hp, mul_one]
  exact herr.trans ((mul_le_mul_of_nonneg_right hpow he0).trans_eq hcancel)

theorem neg_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (neg q) := by
  have h := Oracle.comp (Oracle.of_computable primitive_negCode.to_comp) hq
  exact h.of_eq (fun _ => rfl)

theorem half_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (half q) := by
  have hh : Oracle.Total O (fun n => divideNatCode n 1) :=
    Oracle.of_computable (primitive_divideNatCode.comp Primrec.id (Primrec.const 1)).to_comp
  exact (Oracle.comp hh hq).of_eq (fun _ => rfl)

theorem abs_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (absolute q) :=
  (Oracle.comp (Oracle.of_computable primitive_absCode.to_comp) hq).of_eq (fun _ => rfl)

theorem max_recursive {O : Set (ℕ →. ℕ)} {q r : ℕ → ℕ}
    (hq : Oracle.Total O q) (hr : Oracle.Total O r) : Oracle.Total O (maximum q r) := by
  have hm : Oracle.Total O (fun p => maxCode (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_maxCode.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  exact (Oracle.comp hm (Oracle.pair hq hr)).of_eq fun _ => by simp only [Nat.unpair_pair]; rfl

theorem primitive_magnitude : Primrec magnitude := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  have hn := Primrec.nat_add.comp (Primrec.nat_sub.comp a b) (Primrec.nat_sub.comp b a)
  exact Primrec.nat_add.comp (Primrec.nat_div.comp hn primitive_denominator) (Primrec.const 2)

theorem primitive_productBudget : Primrec₂ productBudget :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (primitive_magnitude.comp Primrec.fst)
    (primitive_magnitude.comp Primrec.snd)) (Primrec.const 1)

theorem mul_recursive {O : Set (ℕ →. ℕ)} {q r : ℕ → ℕ}
    (hq : Oracle.Total O q) (hr : Oracle.Total O r) : Oracle.Total O (mul q r) := by
  have hzero : Oracle.Total O (fun _ : ℕ => 0) := Oracle.of_computable (Computable.const 0)
  have hq0 : Oracle.Total O (fun _ : ℕ => q 0) := Oracle.comp hq hzero
  have hr0 : Oracle.Total O (fun _ : ℕ => r 0) := Oracle.comp hr hzero
  have hB : Oracle.Total O (fun p => productBudget (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_productBudget.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  have hK := Oracle.comp hB (Oracle.pair hq0 hr0)
  have hshift₀ := Oracle.comp (Oracle.addPair (O := O))
    (Oracle.pair (Oracle.of_computable Computable.id) hK)
  have hshift : Oracle.Total O (fun n => n + productBudget (q 0) (r 0)) :=
    hshift₀.of_eq (fun _ => by simp only [Nat.unpair_pair, id_eq])
  have hp := Oracle.pair (Oracle.comp hq hshift) (Oracle.comp hr hshift)
  have hm : Oracle.Total O (fun p => mulCode (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_mulCode.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  exact (Oracle.comp hm hp).of_eq fun _ => by simp only [Nat.unpair_pair]; rfl

end CodeName
end SymplecticPacking.Effective
