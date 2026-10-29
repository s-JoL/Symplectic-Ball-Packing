import Mathlib

/-!
# Explicit enlargement of capacities

Strict inequalities on the capacities (`ρ_i < B`, `Σ ρ_i^n < V`) leave room for explicit
enlargements. `slackLevel t` (`0 < t ≤ 1`) moves every `ρ_i` up by `t η_i` with
`η_i = min((B - ρ_i)/2, (V - Σ ρ_j^n)/(2nk))`; the enlarged capacities keep both inequalities.
Distinct levels give the nested radii `ρ_i < ρ'_i < ρ''_i < a_i` used by every branch.
-/

noncomputable section

namespace SymplecticPacking.HighDim

/-- `(x + η)^n ≤ x^n + n η` for `0 ≤ x`, `0 ≤ η`, `x + η ≤ 1`. -/
theorem pow_add_le_add_mul {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) (h1 : x + η ≤ 1) (n : ℕ) :
    (x + η) ^ n ≤ x ^ n + n * η := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x ^ n ≤ 1 := pow_le_one₀ hx (by linarith)
    have hxe : 0 ≤ x + η := by linarith
    calc (x + η) ^ (n + 1) = (x + η) ^ n * (x + η) := pow_succ _ _
      _ ≤ (x ^ n + n * η) * (x + η) := mul_le_mul_of_nonneg_right ih hxe
      _ = x ^ (n + 1) + x ^ n * η + n * η * (x + η) := by ring
      _ ≤ x ^ (n + 1) + 1 * η + n * η * 1 := by
          gcongr
      _ = x ^ (n + 1) + ((n + 1 : ℕ) : ℝ) * η := by push_cast; ring

variable {k : ℕ}

/-- Per-ball slack `η_i = min((B − ρ_i)/2, (V − Σ_j ρ_j^n)/(2nk))`. -/
def slack (n : ℕ) (ρ : Fin k → ℝ) (B V : ℝ) (i : Fin k) : ℝ :=
  min ((B - ρ i) / 2) ((V - ∑ j, ρ j ^ n) / (2 * n * k))

/-- The enlarged capacities `ρ_i + t η_i`. -/
def slackLevel (n : ℕ) (ρ : Fin k → ℝ) (B V t : ℝ) (i : Fin k) : ℝ :=
  ρ i + t * slack n ρ B V i

theorem slack_pos {n : ℕ} {ρ : Fin k → ℝ} {B V : ℝ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hB : ∀ i, ρ i < B) (hV : ∑ j, ρ j ^ n < V) (i : Fin k) : 0 < slack n ρ B V i := by
  have hnk : (0 : ℝ) < 2 * n * k := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  exact lt_min (by linarith [hB i]) (div_pos (by linarith) hnk)

theorem lt_slackLevel {n : ℕ} {ρ : Fin k → ℝ} {B V t : ℝ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hB : ∀ i, ρ i < B) (hV : ∑ j, ρ j ^ n < V) (ht : 0 < t) (i : Fin k) :
    ρ i < slackLevel n ρ B V t i := by
  have := slack_pos hn hk hB hV i
  simp only [slackLevel]
  nlinarith

theorem slackLevel_strictMono {n : ℕ} {ρ : Fin k → ℝ} {B V t t' : ℝ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hB : ∀ i, ρ i < B) (hV : ∑ j, ρ j ^ n < V) (htt : t < t') (i : Fin k) :
    slackLevel n ρ B V t i < slackLevel n ρ B V t' i := by
  have := slack_pos hn hk hB hV i
  simp only [slackLevel]
  nlinarith

theorem slackLevel_lt {n : ℕ} {ρ : Fin k → ℝ} {B V t : ℝ}
    (hB : ∀ i, ρ i < B) (ht1 : t ≤ 1) (hη : ∀ i, 0 ≤ slack n ρ B V i) (i : Fin k) :
    slackLevel n ρ B V t i < B := by
  have h1 : slack n ρ B V i ≤ (B - ρ i) / 2 := min_le_left _ _
  have : t * slack n ρ B V i ≤ 1 * slack n ρ B V i :=
    mul_le_mul_of_nonneg_right ht1 (hη i)
  simp only [slackLevel]
  linarith [hB i]

theorem sum_slackLevel_pow_lt {n : ℕ} {ρ : Fin k → ℝ} {B V t : ℝ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hρ : ∀ i, 0 ≤ ρ i) (hB : ∀ i, ρ i < B) (hB1 : B ≤ 1) (hV : ∑ j, ρ j ^ n < V)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, slackLevel n ρ B V t i ^ n < V := by
  have hη := fun i => (slack_pos hn hk hB hV i).le
  have hnk : (0 : ℝ) < 2 * n * k := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  set S := ∑ j, ρ j ^ n
  have hbound : ∀ i, slackLevel n ρ B V t i ^ n ≤ ρ i ^ n + (V - S) / (2 * k) := by
    intro i
    have hte : 0 ≤ t * slack n ρ B V i := mul_nonneg ht0 (hη i)
    have hle1 : ρ i + t * slack n ρ B V i ≤ 1 :=
      (slackLevel_lt hB ht1 hη i).le.trans hB1
    have h2 : slack n ρ B V i ≤ (V - S) / (2 * n * k) := min_le_right _ _
    have h3 : t * slack n ρ B V i ≤ (V - S) / (2 * n * k) :=
      (mul_le_of_le_one_left (hη i) ht1).trans h2
    calc slackLevel n ρ B V t i ^ n ≤ ρ i ^ n + n * (t * slack n ρ B V i) :=
          pow_add_le_add_mul (hρ i) hte hle1 n
      _ ≤ ρ i ^ n + n * ((V - S) / (2 * n * k)) := by gcongr
      _ = ρ i ^ n + (V - S) / (2 * k) := by
          have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                   positivity
          field_simp
  calc ∑ i, slackLevel n ρ B V t i ^ n ≤ ∑ i, (ρ i ^ n + (V - S) / (2 * k)) :=
        Finset.sum_le_sum fun i _ => hbound i
    _ = S + (V - S) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have : (k : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                 positivity
        field_simp
        rfl
    _ < V := by linarith

end SymplecticPacking.HighDim
