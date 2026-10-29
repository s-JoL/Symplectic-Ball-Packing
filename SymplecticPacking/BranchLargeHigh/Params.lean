import SymplecticPacking.General.Interface

/-!
# Auxiliary parameters of the one-large-ball branch

Paper `lem:lrg-auxiliary`. Normalised capacities
`ρ_i = c_i / C`. A ball is *large* if `C ≤ 2 c_i`; under the pair inequality there is at most one,
the distinguished ball `j`, and `A = ρ_j = max_i ρ_i`. We give the auxiliary data by an explicit
formula (no search): one increment `t > 0`,

  `a = A + t`,   `r_i = ρ_i + t`  (`i` small),

with `t = min(g/4, 1, V/(2 n k 2ⁿ))`, `g = 1 - A - max_{i small} ρ_i` (pair slack) and
`V = 1 - Σ ρ_i^n` (volume slack). Then `1/2 < a < 1`, `ρ_i < r_i < 1 - a` and
`a^n + Σ_{i small} r_i^n < 1` (`aux_spec`).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Finset

variable {k : ℕ}

/-- Normalised capacities `ρ_i = c_i / C`. -/
def rho (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := c i / C

/-- The small balls: index type `{i // ¬ C ≤ 2 c_i}`. -/
abbrev Small (k : ℕ) (C : ℝ) (c : Fin k → ℝ) := {i : Fin k // ¬ C ≤ 2 * c i}

/-- `A = max_i ρ_i` (with `0` for the empty family). -/
def bigA (C : ℝ) (c : Fin k → ℝ) : ℝ := univ.fold max 0 (rho C c)

/-- `max_{i small} ρ_i` (with `0` if there is no small ball). -/
def smallMax (C : ℝ) (c : Fin k → ℝ) : ℝ :=
  univ.fold max 0 (fun i => if C ≤ 2 * c i then 0 else rho C c i)

/-- Pair slack `g = 1 - A - max_{small} ρ_i`. -/
def gapPair (C : ℝ) (c : Fin k → ℝ) : ℝ := 1 - bigA C c - smallMax C c

/-- Volume slack `V = 1 - Σ ρ_i^n`. -/
def gapVol (n : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ := 1 - ∑ i, rho C c i ^ n

/-- The increment `t`. -/
def tInc (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ :=
  min (min (gapPair C c / 4) 1) (gapVol n C c / (2 * (n * k * 2 ^ n)))

/-- The reserved central capacity `a = A + t`. -/
def aPar (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ := bigA C c + tInc n k C c

/-- The auxiliary capacities `r_i = ρ_i + t` (used for the small balls). -/
def rPar (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := rho C c i + tInc n k C c

/-- `(x + t)^n ≤ x^n + t n 2^n` for `0 ≤ x, t ≤ 1`. -/
lemma pow_add_le (n : ℕ) {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (x + t) ^ n ≤ x ^ n + t * n * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
    have hxn0 : 0 ≤ x ^ n := pow_nonneg hx0 n
    have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
    have h2' : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (x + t) ^ (n + 1) = (x + t) ^ n * (x + t) := pow_succ _ _
      _ ≤ (x ^ n + t * n * 2 ^ n) * (x + t) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ = x ^ n * x + t * x ^ n + t * n * 2 ^ n * (x + t) := by ring
      _ ≤ x ^ n * x + t + t * n * 2 ^ n * 2 := by
          have : t * n * 2 ^ n * (x + t) ≤ t * n * 2 ^ n * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hxn ht0]
      _ ≤ x ^ (n + 1) + t * ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) := by
          rw [pow_succ, pow_succ]; push_cast
          nlinarith [mul_le_mul_of_nonneg_left h2' ht0]

section spec

variable {n : ℕ} {C : ℝ} {c : Fin k → ℝ}

/-- The hypotheses of the branch, normalised. -/
structure BranchHyp (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Prop where
  n_pos : 1 ≤ n
  k_pos : 1 ≤ k
  C_pos : 0 < C
  c_pos : ∀ i, 0 < c i
  pair : ∀ i j, i ≠ j → c i + c j < C
  vol : ∑ i, c i ^ n < C ^ n
  large : ∃ j, C ≤ 2 * c j

variable (hB : BranchHyp n k C c)
include hB

lemma rho_pos (i : Fin k) : 0 < rho C c i := div_pos (hB.c_pos i) hB.C_pos

lemma sum_rho_pow : ∑ i, rho C c i ^ n < 1 := by
  have hC := hB.C_pos
  have : ∑ i, rho C c i ^ n = (∑ i, c i ^ n) / C ^ n := by
    simp only [rho, div_pow, Finset.sum_div]
  rw [this, div_lt_one (by positivity)]; exact hB.vol

lemma rho_lt_one (i : Fin k) : rho C c i < 1 := by
  have h := sum_rho_pow hB
  have hle : rho C c i ^ n ≤ ∑ j, rho C c j ^ n :=
    Finset.single_le_sum (f := fun j => rho C c j ^ n)
      (fun j _ => pow_nonneg (rho_pos hB j).le n) (mem_univ i)
  by_contra hcon; push_neg at hcon
  have : 1 ≤ rho C c i ^ n := one_le_pow₀ hcon
  linarith

lemma large_iff (i : Fin k) : C ≤ 2 * c i ↔ 1 ≤ 2 * rho C c i := by
  have hC := hB.C_pos
  rw [rho, mul_div_assoc', le_div_iff₀ hC, one_mul]

/-- At most one large ball. -/
lemma large_unique {i j : Fin k} (hi : C ≤ 2 * c i) (hj : C ≤ 2 * c j) : i = j := by
  by_contra h
  have := hB.pair i j h
  linarith

lemma small_lt {i j : Fin k} (hj : C ≤ 2 * c j) (hi : ¬ C ≤ 2 * c i) :
    rho C c i + rho C c j < 1 := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have := hB.pair i j hij
  have hC := hB.C_pos
  rw [rho, rho, ← add_div, div_lt_one hC]; exact this

lemma bigA_eq {j : Fin k} (hj : C ≤ 2 * c j) : bigA C c = rho C c j := by
  apply le_antisymm
  · rw [bigA, Finset.fold_max_le]
    refine ⟨(rho_pos hB j).le, fun i _ => ?_⟩
    by_cases hi : C ≤ 2 * c i
    · rw [large_unique hB hi hj]
    · have := small_lt hB hj hi
      have := (large_iff hB j).1 hj
      linarith
  · rw [bigA, Finset.le_fold_max]; exact Or.inr ⟨j, mem_univ _, le_rfl⟩

lemma smallMax_nonneg : 0 ≤ smallMax C c := by
  rw [smallMax, Finset.le_fold_max]; exact Or.inl le_rfl

lemma gapPair_pos : 0 < gapPair C c := by
  obtain ⟨j, hj⟩ := hB.large
  have hlt : smallMax C c < 1 - rho C c j := by
    rw [smallMax, Finset.fold_max_lt]
    refine ⟨by linarith [rho_lt_one hB j], fun i _ => ?_⟩
    split_ifs with hi
    · linarith [rho_lt_one hB j]
    · linarith [small_lt hB hj hi]
  rw [gapPair, bigA_eq hB hj]; linarith

lemma gapVol_pos : 0 < gapVol n C c := by rw [gapVol]; linarith [sum_rho_pow hB]

lemma tInc_pos : 0 < tInc n k C c := by
  have := gapPair_pos hB
  have := gapVol_pos hB
  have hn : (0 : ℝ) < n := by exact_mod_cast hB.n_pos
  have hk : (0 : ℝ) < k := by exact_mod_cast hB.k_pos
  unfold tInc
  apply lt_min (lt_min (by linarith) one_pos)
  positivity

lemma tInc_le_gap : tInc n k C c ≤ gapPair C c / 4 :=
  (min_le_left _ _).trans (min_le_left _ _)

lemma tInc_le_one : tInc n k C c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)

lemma tInc_le_vol : tInc n k C c ≤ gapVol n C c / (2 * (n * k * 2 ^ n)) := min_le_right _ _

/-- `Σ_i (ρ_i + t)^n < 1`. -/
lemma sum_shift_pow_lt : ∑ i, (rho C c i + tInc n k C c) ^ n < 1 := by
  have ht0 := (tInc_pos hB).le
  have ht1 := tInc_le_one hB
  have hn : (0 : ℝ) < n := by exact_mod_cast hB.n_pos
  have hk : (0 : ℝ) < k := by exact_mod_cast hB.k_pos
  have h1 : ∑ i, (rho C c i + tInc n k C c) ^ n ≤
      ∑ i, (rho C c i ^ n + tInc n k C c * n * 2 ^ n) :=
    Finset.sum_le_sum fun i _ =>
      pow_add_le n (rho_pos hB i).le (rho_lt_one hB i).le ht0 ht1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * (tInc n k C c * n * 2 ^ n) ≤ gapVol n C c / 2 := by
    have := tInc_le_vol hB
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have := gapVol_pos hB
  unfold gapVol at h2 this
  linarith

/-- **`lem:lrg-auxiliary`.** The auxiliary parameters satisfy `1/2 < a < 1`,
`ρ_i < r_i < 1 - a` for the small balls and `a^n + Σ_{small} r_i^n < 1`; the large ball has
`ρ_j + t = a`. -/
theorem aux_spec {j : Fin k} (hj : C ≤ 2 * c j) :
    1 / 2 < aPar n k C c ∧ aPar n k C c < 1 ∧
    rho C c j + tInc n k C c = aPar n k C c ∧
    (∀ i, ¬ C ≤ 2 * c i → rPar n k C c i < 1 - aPar n k C c) ∧
    aPar n k C c ^ n + ∑ i : Small k C c, rPar n k C c i ^ n < 1 := by
  have ht := tInc_pos hB
  have htg := tInc_le_gap hB
  have hA := bigA_eq hB hj
  have hj' := (large_iff hB j).1 hj
  have hg := gapPair_pos hB
  have hsm := smallMax_nonneg hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [aPar, hA]; linarith
  · rw [aPar]; unfold gapPair at htg hg; linarith
  · rw [aPar, hA]
  · intro i hi
    have hle : rho C c i ≤ smallMax C c := by
      rw [smallMax, Finset.le_fold_max]
      exact Or.inr ⟨i, mem_univ _, by rw [if_neg hi]⟩
    rw [rPar, aPar]; unfold gapPair at htg hg; linarith
  · have hsum := sum_shift_pow_lt hB
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => C ≤ 2 * c i)] at hsum
    have hL : ∑ i : {i // C ≤ 2 * c i}, (rho C c i + tInc n k C c) ^ n = aPar n k C c ^ n := by
      have : ∑ i : {i // C ≤ 2 * c i}, (rho C c i + tInc n k C c) ^ n =
          (rho C c j + tInc n k C c) ^ n := by
        rw [Fintype.sum_eq_single ⟨j, hj⟩]
        intro i hi
        exact absurd (Subtype.ext (large_unique hB i.2 hj)) hi
      rw [this, aPar, hA]
    rw [hL] at hsum
    exact hsum

end spec

end SymplecticPacking.BranchLargeHigh
