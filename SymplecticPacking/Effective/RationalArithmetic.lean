import SymplecticPacking.Effective.RationalCode

/-!
# Arithmetic on rational codes

Rational operations on finite natural codes, without normalization or real tests.
-/

namespace SymplecticPacking.Effective.RationalCode

def zeroCode : ℕ := encode 0 0 0

def dyadicCode (n : ℕ) : ℕ := encode 1 0 (2 ^ n - 1)

/-- Strict comparison of two rational codes by natural cross multiplication. -/
def Less (u v : ℕ) : Prop :=
  positiveNumerator u * denominator v + negativeNumerator v * denominator u <
    positiveNumerator v * denominator u + negativeNumerator u * denominator v

instance : DecidableRel Less := fun _ _ => inferInstanceAs (Decidable (_ < _))

def negCode (u : ℕ) : ℕ :=
  encode (negativeNumerator u) (positiveNumerator u) (denominator u - 1)

def absCode (u : ℕ) : ℕ :=
  encode ((positiveNumerator u - negativeNumerator u) +
    (negativeNumerator u - positiveNumerator u)) 0 (denominator u - 1)

def maxCode (u v : ℕ) : ℕ := if Less u v then v else u

/-- Reciprocal of a finite rational value, with the field convention `0⁻¹ = 0`. -/
def invCode (u : ℕ) : ℕ :=
  if positiveNumerator u = negativeNumerator u then zeroCode
  else if negativeNumerator u < positiveNumerator u then
    encode (denominator u) 0 (positiveNumerator u-negativeNumerator u-1)
  else encode 0 (denominator u) (negativeNumerator u-positiveNumerator u-1)

def addCode (u v : ℕ) : ℕ :=
  encode (positiveNumerator u * denominator v + positiveNumerator v * denominator u)
    (negativeNumerator u * denominator v + negativeNumerator v * denominator u)
    (denominator u * denominator v - 1)

def mulCode (u v : ℕ) : ℕ :=
  encode (positiveNumerator u * positiveNumerator v + negativeNumerator u * negativeNumerator v)
    (positiveNumerator u * negativeNumerator v + negativeNumerator u * positiveNumerator v)
    (denominator u * denominator v - 1)

def divideNatCode (u N : ℕ) : ℕ :=
  encode (positiveNumerator u) (negativeNumerator u) (denominator u * (N + 1) - 1)

theorem denominator_pos (u : ℕ) : 0 < denominator u := by unfold denominator; omega

theorem value_zeroCode : value zeroCode = 0 := by simp [zeroCode, value_encode]

theorem value_dyadicCode (n : ℕ) : value (dyadicCode n) = radius n := by
  rw [dyadicCode, value_encode]
  have hp : 0 < 2 ^ n := by positivity
  have hd : ((2 ^ n - 1 : ℕ) : ℚ) + 1 = 2 ^ n := by
    exact_mod_cast Nat.sub_add_cancel hp
  simp only [Nat.cast_one, Nat.cast_zero, sub_zero, hd, radius, div_pow, one_pow]

theorem less_iff (u v : ℕ) : Less u v ↔ value u < value v := by
  have hu : (0 : ℚ) < denominator u := by unfold denominator; positivity
  have hv : (0 : ℚ) < denominator v := by unfold denominator; positivity
  unfold Less value
  rw [div_lt_div_iff₀ hu hv]
  constructor
  · intro h
    have hq : (positiveNumerator u : ℚ) * denominator v + negativeNumerator v * denominator u <
        positiveNumerator v * denominator u + negativeNumerator u * denominator v := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (positiveNumerator u : ℚ) * denominator v + negativeNumerator v * denominator u <
        positiveNumerator v * denominator u + negativeNumerator u * denominator v := by nlinarith
    exact_mod_cast hq

theorem value_negCode (u : ℕ) : value (negCode u) = -value u := by
  rw [negCode, value_encode]
  have hd : denominator u - 1 + 1 = denominator u := Nat.sub_add_cancel (denominator_pos u)
  have hdq : ((denominator u - 1 : ℕ) : ℚ) + 1 = denominator u := by exact_mod_cast hd
  rw [hdq, value]
  ring

theorem value_absCode (u : ℕ) : value (absCode u) = |value u| := by
  rw [absCode, value_encode]
  have hd : denominator u - 1 + 1 = denominator u := Nat.sub_add_cancel (denominator_pos u)
  have hdq : ((denominator u - 1 : ℕ) : ℚ) + 1 = denominator u := by exact_mod_cast hd
  have hdpos : (0 : ℚ) < denominator u := by exact_mod_cast denominator_pos u
  rw [hdq, value, abs_div, abs_of_pos hdpos]
  simp only [Nat.cast_zero, sub_zero]
  congr 1
  by_cases h : negativeNumerator u ≤ positiveNumerator u
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [Nat.sub_eq_zero_of_le h', zero_add, Nat.cast_sub h',
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h'))]
    ring

theorem value_maxCode (u v : ℕ) : value (maxCode u v) = max (value u) (value v) := by
  by_cases h : Less u v
  · simp only [maxCode, if_pos h, max_eq_right ((less_iff _ _).mp h).le]
  · simp only [maxCode, if_neg h, max_eq_left (le_of_not_gt (mt (less_iff _ _).mpr h))]

theorem value_invCode (u : ℕ) : value (invCode u) = (value u)⁻¹ := by
  by_cases he : positiveNumerator u = negativeNumerator u
  · rw [invCode, if_pos he, value_zeroCode]
    simp only [value, he, sub_self, zero_div, inv_zero]
  · by_cases hp : negativeNumerator u < positiveNumerator u
    · have hd : positiveNumerator u-negativeNumerator u-1+1 =
          positiveNumerator u-negativeNumerator u := by omega
      have hdq : ((positiveNumerator u-negativeNumerator u-1 : ℕ) : ℚ)+1 =
          (positiveNumerator u : ℚ)-negativeNumerator u := by
        have hc : ((positiveNumerator u-negativeNumerator u-1+1 : ℕ) : ℚ) =
            (positiveNumerator u : ℚ)-negativeNumerator u := by rw [hd, Nat.cast_sub hp.le]
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      rw [invCode, if_neg he, if_pos hp, value_encode, hdq]
      simp only [Nat.cast_zero, sub_zero, value, inv_div]
    · have hp' : positiveNumerator u < negativeNumerator u := by omega
      have hd : negativeNumerator u-positiveNumerator u-1+1 =
          negativeNumerator u-positiveNumerator u := by omega
      have hdq : ((negativeNumerator u-positiveNumerator u-1 : ℕ) : ℚ)+1 =
          (negativeNumerator u : ℚ)-positiveNumerator u := by
        have hc : ((negativeNumerator u-positiveNumerator u-1+1 : ℕ) : ℚ) =
            (negativeNumerator u : ℚ)-positiveNumerator u := by rw [hd, Nat.cast_sub hp'.le]
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      rw [invCode, if_neg he, if_neg hp, value_encode, hdq]
      simp only [Nat.cast_zero, zero_sub, value, inv_div]
      rw [show (negativeNumerator u : ℚ)-positiveNumerator u =
          -((positiveNumerator u : ℚ)-negativeNumerator u) by ring, div_neg, neg_div, neg_neg]

theorem value_addCode (u v : ℕ) : value (addCode u v) = value u + value v := by
  rw [addCode, value_encode]
  have hp : 0 < denominator u * denominator v := Nat.mul_pos (denominator_pos u) (denominator_pos v)
  have hd : denominator u * denominator v - 1 + 1 = denominator u * denominator v :=
    Nat.sub_add_cancel hp
  have hdq : ((denominator u * denominator v - 1 : ℕ) : ℚ) + 1 =
      (denominator u : ℚ) * denominator v := by exact_mod_cast hd
  have hu : (denominator u : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos u).ne'
  have hv : (denominator v : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos v).ne'
  rw [hdq]
  simp only [Nat.cast_add, Nat.cast_mul, value]
  field_simp
  ring

theorem value_mulCode (u v : ℕ) : value (mulCode u v) = value u * value v := by
  rw [mulCode, value_encode]
  have hp : 0 < denominator u * denominator v := Nat.mul_pos (denominator_pos u) (denominator_pos v)
  have hd : denominator u * denominator v - 1 + 1 = denominator u * denominator v :=
    Nat.sub_add_cancel hp
  have hdq : ((denominator u * denominator v - 1 : ℕ) : ℚ) + 1 =
      (denominator u : ℚ) * denominator v := by exact_mod_cast hd
  rw [hdq]
  simp only [Nat.cast_add, Nat.cast_mul, value]
  ring

theorem value_divideNatCode (u N : ℕ) : value (divideNatCode u N) = value u / (N + 1) := by
  rw [divideNatCode, value_encode]
  have hp : 0 < denominator u * (N + 1) := Nat.mul_pos (denominator_pos u) (Nat.succ_pos N)
  have hd : denominator u * (N + 1) - 1 + 1 = denominator u * (N + 1) := Nat.sub_add_cancel hp
  have hdq : ((denominator u * (N + 1) - 1 : ℕ) : ℚ) + 1 =
      (denominator u : ℚ) * (N + 1) := by exact_mod_cast hd
  rw [hdq, value, div_div]

theorem primitive_positiveNumerator : Primrec positiveNumerator :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))

theorem primitive_negativeNumerator : Primrec negativeNumerator :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))

theorem primitive_denominator : Primrec denominator :=
  Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)

theorem primitive_dyadicCode : Primrec dyadicCode := by
  have hp : Primrec (fun n : ℕ => 2 ^ n) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.const 1) (Primrec.const 0))
    (Primrec.nat_sub.comp hp (Primrec.const 1))

theorem primitive_less : PrimrecRel Less := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  have d := primitive_denominator
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (a.comp Primrec.fst) (d.comp Primrec.snd))
      (Primrec.nat_mul.comp (b.comp Primrec.snd) (d.comp Primrec.fst)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (a.comp Primrec.snd) (d.comp Primrec.fst))
      (Primrec.nat_mul.comp (b.comp Primrec.fst) (d.comp Primrec.snd)))

theorem primitive_negCode : Primrec negCode := by
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp primitive_negativeNumerator primitive_positiveNumerator)
    (Primrec.nat_sub.comp primitive_denominator (Primrec.const 1))

theorem primitive_absCode : Primrec absCode := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.nat_sub.comp a b) (Primrec.nat_sub.comp b a))
      (Primrec.const 0))
    (Primrec.nat_sub.comp primitive_denominator (Primrec.const 1))

theorem primitive_maxCode : Primrec₂ maxCode :=
  Primrec.ite primitive_less Primrec.snd Primrec.fst

theorem primitive_invCode : Primrec invCode := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  have d := primitive_denominator
  exact Primrec.ite (Primrec.eq.comp a b) (Primrec.const zeroCode)
    (Primrec.ite (Primrec.nat_lt.comp b a)
      (Primrec₂.natPair.comp (Primrec₂.natPair.comp d (Primrec.const 0))
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp a b) (Primrec.const 1)))
      (Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.const 0) d)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp b a) (Primrec.const 1))))

theorem primitive_addCode : Primrec₂ addCode := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  have d := primitive_denominator
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (a.comp Primrec.fst) (d.comp Primrec.snd))
        (Primrec.nat_mul.comp (a.comp Primrec.snd) (d.comp Primrec.fst)))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (b.comp Primrec.fst) (d.comp Primrec.snd))
        (Primrec.nat_mul.comp (b.comp Primrec.snd) (d.comp Primrec.fst))))
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (d.comp Primrec.fst) (d.comp Primrec.snd))
      (Primrec.const 1))

theorem primitive_mulCode : Primrec₂ mulCode := by
  have a := primitive_positiveNumerator
  have b := primitive_negativeNumerator
  have d := primitive_denominator
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (a.comp Primrec.fst) (a.comp Primrec.snd))
        (Primrec.nat_mul.comp (b.comp Primrec.fst) (b.comp Primrec.snd)))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (a.comp Primrec.fst) (b.comp Primrec.snd))
        (Primrec.nat_mul.comp (b.comp Primrec.fst) (a.comp Primrec.snd))))
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (d.comp Primrec.fst) (d.comp Primrec.snd))
      (Primrec.const 1))

theorem primitive_divideNatCode : Primrec₂ divideNatCode := by
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (primitive_positiveNumerator.comp Primrec.fst)
      (primitive_negativeNumerator.comp Primrec.fst))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (primitive_denominator.comp Primrec.fst)
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))
      (Primrec.const 1))

end SymplecticPacking.Effective.RationalCode
