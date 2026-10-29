import SymplecticPacking.HighDim.Slack

/-!
# Auxiliary parameters of the small-ball branch (paper lem:qdr-auxiliary)

Input: `n ≥ 3`, normalised capacities `0 < ρ_i < 1/2` with `Σ ρ_i^n < 1` (`ρ_i = c_i / C`).
Explicit choices (small-ball candidate §1):
* nested enlargements `ρ_i < ρ'_i < ρ''_i < a_i < 1/2`, `Σ a_i^n < 1` (`HighDim.slackLevel`
  at levels `1/3, 2/3, 1`);
* `σ = 1 − Σ a_i^n`, `δ = min((1/2 − a_max)/2, σ/(4n(n−1)))`, `h = 1/2 − δ`,
  `b = (h + 1/2)/2`, `τ = (a_max + h)/(2h)`, `β = 2^{n−1}(1 − 2h)`;
* gap parameter `d = min(β, σ/(2 n!))/2`.
Then `a_max < h < b < 1/2`, `0 < τ < 1`, every cap `{|p| ≤ a_i}` lies in `τΔ_h`.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open SymplecticPacking.HighDim

variable {k : ℕ}

/-- Normalised capacities `ρ_i = c_i / C`. -/
def rho (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := c i / C

/-- Enlargement at level `t` with bound `1/2` and volume `1`. -/
def level (n : ℕ) (ρ : Fin k → ℝ) (t : ℝ) : Fin k → ℝ := slackLevel n ρ (1 / 2) 1 t

/-- `ρ'_i` (enlarged closed source). -/
def rho1 (n : ℕ) (ρ : Fin k → ℝ) : Fin k → ℝ := level n ρ (1 / 3)

/-- `ρ''_i` (domain of the embeddings). -/
def rho2 (n : ℕ) (ρ : Fin k → ℝ) : Fin k → ℝ := level n ρ (2 / 3)

/-- `a_i` (cap radii of the model). -/
def capA (n : ℕ) (ρ : Fin k → ℝ) : Fin k → ℝ := level n ρ 1

/-- `a_max`. -/
def aMax (n : ℕ) (ρ : Fin k → ℝ) : ℝ := ⨆ i, capA n ρ i

/-- `σ = 1 − Σ a_i^n`. -/
def sigma (n : ℕ) (ρ : Fin k → ℝ) : ℝ := 1 - ∑ i, capA n ρ i ^ n

/-- `δ = min((1/2 − a_max)/2, σ/(4n(n−1)))`. -/
def dlt (n : ℕ) (ρ : Fin k → ℝ) : ℝ :=
  min ((1 / 2 - aMax n ρ) / 2) (sigma n ρ / (4 * n * (n - 1)))

/-- Fibre height `h = 1/2 − δ`. -/
def hgt (n : ℕ) (ρ : Fin k → ℝ) : ℝ := 1 / 2 - dlt n ρ

/-- Transfer parameter `b = (h + 1/2)/2`. -/
def bT (n : ℕ) (ρ : Fin k → ℝ) : ℝ := (hgt n ρ + 1 / 2) / 2

/-- Dilation factor `τ = (a_max + h)/(2h)`. -/
def tau (n : ℕ) (ρ : Fin k → ℝ) : ℝ := (aMax n ρ + hgt n ρ) / (2 * hgt n ρ)

/-- Outer lower bound `β = 2^{n−1}(1 − 2h)`. -/
def beta (n : ℕ) (ρ : Fin k → ℝ) : ℝ := 2 ^ (n - 1) * (1 - 2 * hgt n ρ)

/-- Gap parameter `d = min(β, σ/(2 n!))/2`. -/
def dgap (n : ℕ) (ρ : Fin k → ℝ) : ℝ := min (beta n ρ) (sigma n ρ / (2 * n.factorial)) / 2

/-- Normalised branch hypotheses. -/
structure Hyp (n : ℕ) (ρ : Fin k → ℝ) : Prop where
  three_le : 3 ≤ n
  one_le : 1 ≤ k
  pos : ∀ i, 0 < ρ i
  half : ∀ i, ρ i < 1 / 2
  vol : ∑ i, ρ i ^ n < 1

theorem hyp_of_input {n : ℕ} {C : ℝ} {c : Fin k → ℝ} (hn : 3 ≤ n) (hk : 1 ≤ k) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) (hsmall : ∀ i, 2 * c i < C) (hvol : ∑ i, c i ^ n < C ^ n) :
    Hyp n (rho C c) := by
  refine ⟨hn, hk, fun i => div_pos (hc i) hC, fun i => ?_, ?_⟩
  · rw [rho, div_lt_iff₀ hC]; linarith [hsmall i]
  · simp only [rho, div_pow, ← Finset.sum_div]
    exact (div_lt_one (pow_pos hC n)).mpr hvol

section
variable {n : ℕ} {ρ : Fin k → ℝ} (H : Hyp n ρ)
include H

theorem one_le_n : 1 ≤ n := le_trans (by norm_num) H.three_le

theorem slack_nonneg (i : Fin k) : 0 ≤ slack n ρ (1 / 2) 1 i :=
  (slack_pos (one_le_n H) H.one_le H.half H.vol i).le

theorem lt_rho1 (i : Fin k) : ρ i < rho1 n ρ i :=
  lt_slackLevel (one_le_n H) H.one_le H.half H.vol (by norm_num) i

theorem rho1_lt_rho2 (i : Fin k) : rho1 n ρ i < rho2 n ρ i :=
  slackLevel_strictMono (one_le_n H) H.one_le H.half H.vol (by norm_num) i

theorem rho2_lt_capA (i : Fin k) : rho2 n ρ i < capA n ρ i :=
  slackLevel_strictMono (one_le_n H) H.one_le H.half H.vol (by norm_num) i

theorem rho2_nonneg (i : Fin k) : 0 ≤ rho2 n ρ i :=
  ((H.pos i).trans ((lt_rho1 H i).trans (rho1_lt_rho2 H i))).le

theorem capA_pos (i : Fin k) : 0 < capA n ρ i :=
  (H.pos i).trans ((lt_rho1 H i).trans ((rho1_lt_rho2 H i).trans (rho2_lt_capA H i)))

theorem capA_lt_half (i : Fin k) : capA n ρ i < 1 / 2 :=
  slackLevel_lt H.half le_rfl (slack_nonneg H) i

theorem sum_capA_lt : ∑ i, capA n ρ i ^ n < 1 :=
  sum_slackLevel_pow_lt (one_le_n H) H.one_le (fun i => (H.pos i).le) H.half (by norm_num)
    H.vol zero_le_one le_rfl

theorem le_aMax (i : Fin k) : capA n ρ i ≤ aMax n ρ :=
  le_ciSup (Set.finite_range _).bddAbove i

theorem aMax_lt_half : aMax n ρ < 1 / 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, H.one_le⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := capA n ρ)
  rw [aMax, ← hi]
  exact capA_lt_half H i

theorem aMax_pos : 0 < aMax n ρ :=
  (capA_pos H ⟨0, H.one_le⟩).trans_le (le_aMax H _)

theorem sigma_pos : 0 < sigma n ρ := by
  have := sum_capA_lt H
  simp only [sigma]
  linarith

theorem delta_pos : 0 < dlt n ρ := by
  have h1 := aMax_lt_half H
  have h2 := sigma_pos H
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast H.three_le
  have h3 : 0 < 4 * (n : ℝ) * (n - 1) := by nlinarith
  exact lt_min (by linarith) (div_pos h2 h3)

theorem aMax_lt_hgt : aMax n ρ < hgt n ρ := by
  have h1 : dlt n ρ ≤ (1 / 2 - aMax n ρ) / 2 := min_le_left _ _
  have h2 := aMax_lt_half H
  simp only [hgt]
  linarith

theorem hgt_lt_half : hgt n ρ < 1 / 2 := by
  simp only [hgt]; linarith [delta_pos H]

theorem hgt_pos : 0 < hgt n ρ := (aMax_pos H).trans (aMax_lt_hgt H)

theorem hgt_lt_bT : hgt n ρ < bT n ρ := by
  simp only [bT]; linarith [hgt_lt_half H]

theorem bT_lt_half : bT n ρ < 1 / 2 := by
  simp only [bT]; linarith [hgt_lt_half H]

theorem tau_pos : 0 < tau n ρ :=
  div_pos (by linarith [aMax_pos H, hgt_pos H]) (by linarith [hgt_pos H])

theorem tau_lt_one : tau n ρ < 1 := by
  rw [tau, div_lt_one (by linarith [hgt_pos H])]
  linarith [aMax_lt_hgt H]

/-- Every cap lies in `τ Δ_h`: `a_i ≤ τ h`. -/
theorem capA_le_tau_hgt (i : Fin k) : capA n ρ i ≤ tau n ρ * hgt n ρ := by
  have hh := hgt_pos H
  rw [tau, div_mul_eq_mul_div, mul_div_assoc, show hgt n ρ / (2 * hgt n ρ) = 1 / 2 by
    field_simp]
  linarith [le_aMax H i, aMax_lt_hgt H]

theorem beta_pos : 0 < beta n ρ := by
  have := hgt_lt_half H
  exact mul_pos (by positivity) (by linarith)

theorem dgap_pos : 0 < dgap n ρ := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact half_pos (lt_min (beta_pos H) (div_pos (sigma_pos H) (by positivity)))

theorem dgap_le : dgap n ρ ≤ sigma n ρ / (4 * n.factorial) := by
  have h1 : min (beta n ρ) (sigma n ρ / (2 * n.factorial)) ≤ sigma n ρ / (2 * n.factorial) :=
    min_le_right _ _
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  simp only [dgap]
  rw [show sigma n ρ / (4 * n.factorial) = sigma n ρ / (2 * n.factorial) / 2 by
    field_simp; ring]
  linarith

theorem dgap_lt_beta : dgap n ρ < beta n ρ := by
  have h1 : min (beta n ρ) (sigma n ρ / (2 * n.factorial)) ≤ beta n ρ := min_le_left _ _
  have := dgap_pos H
  simp only [dgap] at *
  linarith

end

end SymplecticPacking.BranchSmall
