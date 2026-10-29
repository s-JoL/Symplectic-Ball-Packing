import OAI.Geometry.BallPacking.Models.CubicPhysicalLocality

/-!
# Step S2: the integer weights `L, A, B, D, S` (explicit)

For rationals `a, d₁, d₂` with `1/2 < a < 1`, `0 < d₁ < 1 - a < d₂ < (2-a)/3` and a lower bound
`Q`, put `L₀ = den a · den d₁ · den d₂` and `L = (Q+1) L₀`; then

  `A = L d₁, B = L d₂, D = L (2 - a), S = L (1 - a)`

are natural numbers (OpenAI `exists_six_cubic_inner_weights_large`, de-existentialised).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

/-- `q · m` as an integer when `den q ∣ m`. -/
def scaled (q : ℚ) (m : ℕ) : ℤ := q.num * ((m / q.den : ℕ) : ℤ)

lemma scaled_cast (q : ℚ) {m : ℕ} (hm : q.den ∣ m) : ((scaled q m : ℤ) : ℝ) = (q : ℝ) * m := by
  obtain ⟨t, rfl⟩ := hm
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  unfold scaled
  rw [Nat.mul_div_cancel_left t q.den_pos]
  push_cast
  rw [Rat.cast_def]
  field_simp

/-- The integer weights. -/
structure Weights where
  L : ℕ
  A : ℕ
  B : ℕ
  D : ℕ
  S : ℕ

/-- `L = (Q + 1) · den a · den d₁ · den d₂`. -/
def weightL (Q : ℕ) (a d₁ d₂ : ℚ) : ℕ := (Q + 1) * (a.den * d₁.den * d₂.den)

/-- The explicit weights. -/
def weights (Q : ℕ) (a d₁ d₂ : ℚ) : Weights where
  L := weightL Q a d₁ d₂
  A := (scaled d₁ (weightL Q a d₁ d₂)).toNat
  B := (scaled d₂ (weightL Q a d₁ d₂)).toNat
  D := (2 * (weightL Q a d₁ d₂ : ℤ) - scaled a (weightL Q a d₁ d₂)).toNat
  S := ((weightL Q a d₁ d₂ : ℤ) - scaled a (weightL Q a d₁ d₂)).toNat

lemma toNat_cast {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
  rw [← this]; norm_cast

theorem weights_spec (Q : ℕ) {a d₁ d₂ : ℚ}
    (ha : (1 : ℚ) / 2 < a) (ha1 : a < 1)
    (hd₁0 : 0 < d₁) (hd₁ : d₁ < 1 - a) (hd₂s : 1 - a < d₂) (hd₂ : d₂ < (2 - a) / 3) :
    let W := weights Q a d₁ d₂
    Q < W.L ∧ 0 < W.L ∧ 0 < W.A ∧ 0 < W.S ∧ W.A < W.S ∧ W.A ≤ W.B ∧ W.S ≤ W.B ∧
      3 * W.B < W.D ∧ 3 * W.S < W.D ∧
      (W.A : ℝ) = (W.L : ℝ) * (d₁ : ℝ) ∧ (W.B : ℝ) = (W.L : ℝ) * (d₂ : ℝ) ∧
      (W.D : ℝ) = (W.L : ℝ) * (2 - (a : ℝ)) ∧ (W.S : ℝ) = (W.L : ℝ) * (1 - (a : ℝ)) := by
  intro W
  set L := weightL Q a d₁ d₂ with hLdef
  have hL0 : 0 < a.den * d₁.den * d₂.den :=
    Nat.mul_pos (Nat.mul_pos a.den_pos d₁.den_pos) d₂.den_pos
  have hLpos : 0 < L := Nat.mul_pos (Nat.succ_pos Q) hL0
  have hQL : Q < L := by
    have : (Q + 1) * 1 ≤ L := Nat.mul_le_mul_left _ hL0
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hda : a.den ∣ L := ⟨(Q + 1) * (d₁.den * d₂.den), by rw [hLdef, weightL]; ring⟩
  have hd1 : d₁.den ∣ L := ⟨(Q + 1) * (a.den * d₂.den), by rw [hLdef, weightL]; ring⟩
  have hd2 : d₂.den ∣ L := ⟨(Q + 1) * (a.den * d₁.den), by rw [hLdef, weightL]; ring⟩
  have ha' : (1 : ℝ) / 2 < (a : ℝ) := by
    have hh : (((1 : ℚ) / 2 : ℚ) : ℝ) < (a : ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢; exact hh
  have ha1' : (a : ℝ) < 1 := by exact_mod_cast ha1
  have hd₁0' : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁0
  have hd₁' : (d₁ : ℝ) < 1 - (a : ℝ) := by exact_mod_cast hd₁
  have hd₂s' : 1 - (a : ℝ) < d₂ := by exact_mod_cast hd₂s
  have hd₂' : (d₂ : ℝ) < (2 - (a : ℝ)) / 3 := by exact_mod_cast hd₂
  -- real values of the four integers
  have eA : ((scaled d₁ L : ℤ) : ℝ) = L * (d₁ : ℝ) := by rw [scaled_cast _ hd1]; ring
  have eB : ((scaled d₂ L : ℤ) : ℝ) = L * (d₂ : ℝ) := by rw [scaled_cast _ hd2]; ring
  have eD : (((2 * (L : ℤ) - scaled a L) : ℤ) : ℝ) = L * (2 - (a : ℝ)) := by
    push_cast; rw [scaled_cast _ hda]; ring
  have eS : ((((L : ℤ) - scaled a L) : ℤ) : ℝ) = L * (1 - (a : ℝ)) := by
    push_cast; rw [scaled_cast _ hda]; ring
  have nA : 0 ≤ scaled d₁ L := by
    have : (0 : ℝ) ≤ ((scaled d₁ L : ℤ) : ℝ) := by rw [eA]; positivity
    exact_mod_cast this
  have nB : 0 ≤ scaled d₂ L := by
    have : (0 : ℝ) ≤ ((scaled d₂ L : ℤ) : ℝ) := by rw [eB]; nlinarith
    exact_mod_cast this
  have nD : 0 ≤ 2 * (L : ℤ) - scaled a L := by
    have : (0 : ℝ) ≤ (((2 * (L : ℤ) - scaled a L) : ℤ) : ℝ) := by rw [eD]; nlinarith
    exact_mod_cast this
  have nS : 0 ≤ (L : ℤ) - scaled a L := by
    have : (0 : ℝ) ≤ ((((L : ℤ) - scaled a L) : ℤ) : ℝ) := by rw [eS]; nlinarith
    exact_mod_cast this
  have hA : (W.A : ℝ) = L * (d₁ : ℝ) := by
    show (((scaled d₁ L).toNat : ℕ) : ℝ) = _; rw [toNat_cast nA, eA]
  have hB : (W.B : ℝ) = L * (d₂ : ℝ) := by
    show (((scaled d₂ L).toNat : ℕ) : ℝ) = _; rw [toNat_cast nB, eB]
  have hD : (W.D : ℝ) = L * (2 - (a : ℝ)) := by
    show (((2 * (L : ℤ) - scaled a L).toNat : ℕ) : ℝ) = _; rw [toNat_cast nD, eD]
  have hS : (W.S : ℝ) = L * (1 - (a : ℝ)) := by
    show ((((L : ℤ) - scaled a L).toNat : ℕ) : ℝ) = _; rw [toNat_cast nS, eS]
  have hWL : W.L = L := rfl
  rw [hWL]
  refine ⟨hQL, hLpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA, hB, hD, hS⟩
  · apply (Nat.cast_pos (α := ℝ)).mp; rw [hA]; exact mul_pos hLr hd₁0'
  · apply (Nat.cast_pos (α := ℝ)).mp; rw [hS]; exact mul_pos hLr (by linarith)
  · apply (Nat.cast_lt (α := ℝ)).mp; rw [hA, hS]; exact mul_lt_mul_of_pos_left hd₁' hLr
  · apply (Nat.cast_le (α := ℝ)).mp; rw [hA, hB]
    exact mul_le_mul_of_nonneg_left (by linarith) hLr.le
  · apply (Nat.cast_le (α := ℝ)).mp; rw [hS, hB]
    exact mul_le_mul_of_nonneg_left (by linarith) hLr.le
  · have hp : 3 * (W.B : ℝ) < (W.D : ℝ) := by rw [hB, hD]; nlinarith
    exact_mod_cast hp
  · have hp : 3 * (W.S : ℝ) < (W.D : ℝ) := by rw [hS, hD]; nlinarith
    exact_mod_cast hp

end SymplecticPacking.BranchLarge3
