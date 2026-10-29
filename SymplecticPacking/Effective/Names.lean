import Mathlib

/-!
# Rational names and certified strict inequalities

A name is supplied as a rational-valued oracle with error at most 2⁻ⁿ. No arbitrary
name oracle is asserted to be a computable function: computability of the geometric
evaluators and operations is an additional theorem, not part of this representation.
-/

namespace SymplecticPacking.Effective

open Filter Topology

/-- Rational error radius, computed by finite rational arithmetic. -/
def radius (n : ℕ) : ℚ := (1 / 2) ^ n

theorem radius_pos (n : ℕ) : 0 < radius n := pow_pos (by norm_num) _

theorem radius_cast (n : ℕ) : (radius n : ℝ) = (1 / 2 : ℝ) ^ n := by
  simp [radius]

theorem radius_succ (n : ℕ) : radius (n + 1) = radius n / 2 := by
  simp [radius, pow_succ, div_eq_mul_inv]

theorem radius_tendsto : Tendsto (fun n => (radius n : ℝ)) atTop (𝓝 0) := by
  simp_rw [radius_cast]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The supplied rational stream approximates `x` with the stated uniform error. -/
def Names (q : ℕ → ℚ) (x : ℝ) : Prop :=
  ∀ n, |(q n : ℝ) - x| ≤ (radius n : ℝ)

theorem names_rational (q : ℚ) : Names (fun _ => q) (q : ℝ) := by
  intro n
  simp only [sub_self, abs_zero]
  exact_mod_cast (radius_pos n).le

/-- Two precision bits are shared between the summands by shifting one input bit. -/
def addNames (q r : ℕ → ℚ) (n : ℕ) : ℚ := q (n + 1) + r (n + 1)

theorem names_add {q r : ℕ → ℚ} {x y : ℝ} (hq : Names q x) (hr : Names r y) :
    Names (addNames q r) (x + y) := by
  intro n
  have hq' := hq (n + 1)
  have hr' := hr (n + 1)
  have hrad : (radius (n + 1) : ℝ) = (radius n : ℝ) / 2 := by
    exact_mod_cast radius_succ n
  have heq : ((addNames q r n : ℚ) : ℝ) - (x + y) =
      ((q (n + 1) : ℝ) - x) + ((r (n + 1) : ℝ) - y) := by
    simp only [addNames, Rat.cast_add]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

def negName (q : ℕ → ℚ) (n : ℕ) : ℚ := -q n

theorem names_neg {q : ℕ → ℚ} {x : ℝ} (hq : Names q x) : Names (negName q) (-x) := by
  intro n
  simp only [negName, Rat.cast_neg]
  rw [show -(q n : ℝ) - -x = -((q n : ℝ) - x) by ring, abs_neg]
  exact hq n

/-- The name of a difference must pay the error from both operands. -/
def subNames (q r : ℕ → ℚ) (n : ℕ) : ℚ := q (n + 1) - r (n + 1)

theorem names_sub {q r : ℕ → ℚ} {x y : ℝ} (hq : Names q x) (hr : Names r y) :
    Names (subNames q r) (x - y) := by
  simpa [Names, subNames, addNames, negName, sub_eq_add_neg] using names_add hq (names_neg hr)

/-- A rational lower endpoint above zero certifies positivity of the named real. -/
theorem positive_of_certificate {q : ℕ → ℚ} {x : ℝ} (hq : Names q x) {n : ℕ}
    (hcert : radius n < q n) : 0 < x := by
  have herror := (abs_le.mp (hq n)).2
  have hcert' : (radius n : ℝ) < (q n : ℝ) := by exact_mod_cast hcert
  linarith

/-- Every strictly positive named real is certified at all sufficiently fine precisions. -/
theorem eventually_positive_certificate {q : ℕ → ℚ} {x : ℝ} (hq : Names q x)
    (hx : 0 < x) : ∀ᶠ n in atTop, radius n < q n := by
  have hsmall : ∀ᶠ n in atTop, (radius n : ℝ) < x / 2 :=
    (tendsto_order.mp radius_tendsto).2 _ (by linarith)
  filter_upwards [hsmall] with n hn
  have herror := (abs_le.mp (hq n)).1
  have hcert : (radius n : ℝ) < (q n : ℝ) := by linarith
  exact_mod_cast hcert

/-- Strict inequalities can be certified using only their rational name values. -/
def ltCertificate (q r : ℕ → ℚ) (n : ℕ) : Bool :=
  decide (q n + radius n < r n - radius n)

theorem ltCertificate_sound {q r : ℕ → ℚ} {x y : ℝ}
    (hq : Names q x) (hr : Names r y) {n : ℕ} (hcert : ltCertificate q r n = true) : x < y := by
  have hc : q n + radius n < r n - radius n := of_decide_eq_true hcert
  have hc' : (q n : ℝ) + (radius n : ℝ) < (r n : ℝ) - (radius n : ℝ) := by exact_mod_cast hc
  have hx := (abs_le.mp (hq n)).1
  have hy := (abs_le.mp (hr n)).2
  linarith

theorem eventually_ltCertificate {q r : ℕ → ℚ} {x y : ℝ}
    (hq : Names q x) (hr : Names r y) (hxy : x < y) :
    ∀ᶠ n in atTop, ltCertificate q r n = true := by
  have hsmall : ∀ᶠ n in atTop, (radius n : ℝ) < (y - x) / 4 :=
    (tendsto_order.mp radius_tendsto).2 _ (by linarith)
  filter_upwards [hsmall] with n hn
  have hx := (abs_le.mp (hq n)).2
  have hy := (abs_le.mp (hr n)).1
  have hc : (q n : ℝ) + (radius n : ℝ) < (r n : ℝ) - (radius n : ℝ) := by linarith
  have hc' : q n + radius n < r n - radius n := by exact_mod_cast hc
  exact decide_eq_true hc'

end SymplecticPacking.Effective
