import SymplecticPacking.General.Ham.Linear.Unitary

/-!
# Realification of complex matrices

`realify g = [[Re g, -Im g], [Im g, Re g]]` is a ring homomorphism `Mat_n(ℂ) → Mat_{2n}(ℝ)` (the
matrix of `z ↦ g z` under `z = q + i p`), with `realify (i · 1) = J`; a real matrix commuting with
`J` is the realification of `U₁₁ + i U₂₁`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix

variable {n : ℕ}

/-- Complex `n × n` matrices. -/
abbrev CSq (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The realification `[[Re g, -Im g], [Im g, Re g]]`. -/
def realify (g : CSq n) : Mat n :=
  fromBlocks (g.map Complex.re) (-(g.map Complex.im)) (g.map Complex.im) (g.map Complex.re)

lemma realify_one : realify (1 : CSq n) = 1 := by
  rw [realify, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

lemma realify_zero : realify (0 : CSq n) = 0 := by
  simp [realify]

lemma realify_add (g h : CSq n) : realify (g + h) = realify g + realify h := by
  simp only [realify, fromBlocks_add]
  congr 1 <;> ext i j <;> simp <;> ring

lemma realify_mul (g h : CSq n) : realify (g * h) = realify g * realify h := by
  simp only [realify, fromBlocks_multiply]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum,
      Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> ring

/-- Realification as a ring homomorphism. -/
def realifyHom : CSq n →+* Mat n where
  toFun := realify
  map_one' := realify_one
  map_mul' := realify_mul
  map_zero' := realify_zero
  map_add' := realify_add

lemma realify_smul_one (z : ℂ) : realify (z • (1 : CSq n)) = z.re • (1 : Mat n) + z.im • Jm n := by
  simp only [realify, Jm, J, fromBlocks_smul, ← fromBlocks_one, fromBlocks_add]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- A real matrix commuting with `J` is the realification of `U₁₁ + i U₂₁`. -/
lemma realify_of_comm_J {U : Mat n} (h : U * Jm n = Jm n * U) :
    realify (U.toBlocks₁₁.map (↑) + Complex.I • U.toBlocks₂₁.map (↑)) = U := by
  have hb : fromBlocks U.toBlocks₁₁ U.toBlocks₁₂ U.toBlocks₂₁ U.toBlocks₂₂ * Jm n =
      Jm n * fromBlocks U.toBlocks₁₁ U.toBlocks₁₂ U.toBlocks₂₁ U.toBlocks₂₂ := by
    rw [fromBlocks_toBlocks]; exact h
  simp only [Jm, J, fromBlocks_multiply] at hb
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.one_mul, Matrix.neg_mul] at hb
  obtain ⟨h1, h2, -, -⟩ := Matrix.fromBlocks_inj.mp hb
  conv_rhs => rw [← fromBlocks_toBlocks U]
  rw [realify]
  congr 1
  · ext i j; simp
  · rw [h1]; ext i j; simp
  · ext i j; simp
  · rw [← neg_neg U.toBlocks₂₂, ← h2]; ext i j; simp

end SymplecticPacking.General.Ham.Linear
