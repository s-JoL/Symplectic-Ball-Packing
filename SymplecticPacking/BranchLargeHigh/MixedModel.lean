import SymplecticPacking.HighDim.Comparator.FixedPoint
import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus
import SymplecticPacking.BranchLargeHigh.Params

/-!
# The mixed-weight model and its comparator input

Paper `def:lrg-mixed-model`, `lem:lrg-mixed-volume`; supplement `lem:two-mixed`
Dimension `n = q + 2 ≥ 4`; the fibre of
`E₀ = O_Γ(1) ⊕ O_Γ(2)^{⊕q}` has moments `p = (u, p_1, …, p_q) ∈ ℝ^{q+1}` (`p₁ = u`,
`p_j = (1-u) v_j`), the polytope is

  `Δ = {p ≥ 0, u ≤ h₁, w + h₂ u ≤ h₂}`,  `w = Σ_{j ≥ 1} p_j`  (OpenAI `largeModelBounds`),

the base area profile is `H_b(p) = 2^q (1 - u - 2w)` (`largeModelDensity`), and the comparison
profile is `P = H_b - Σ_i (r_i - |p|)_+` (`largeModelGap`). `∫_Δ H_b = J(h₁, h₂)`
(`largeModelMean`, `integral_largeModelDensity`) and `J(1-a, 1/2) = (1-a^n)/n!`.

Explicit parameters (no search): `R = max r_i`, `σ = 1 - a^n - Σ r_i^n`,
`δ = min((1-a-R)/2, σ/(2 n! (4 + 2^n)))`, `h₁ = 1 - a - δ`, `h₂ = 1/2 - δ`,
`τ = (R + h₁)/(2h₁)`, `β = 2^q (1-h₁)(1-2h₂)`, `d = min(β, (J - Σ r_i^n/n!)/2)/2`.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Mixed

open Set MeasureTheory
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (largeModelBounds largeModelGap largeModelDensity
  largeModelMean smallModelMean momentSimplex)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)

variable {ι : Type} [Fintype ι]

/-- `R = max_i r_i` (`0` for no ball). -/
def rMax (r : ι → ℝ) : ℝ := Finset.univ.fold max 0 r

/-- Volume slack `σ = 1 - a^n - Σ r_i^n`, `n = q + 2`. -/
def sigma (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ := 1 - a ^ (q + 2) - ∑ i, r i ^ (q + 2)

/-- `δ = min((1-a-R)/2, σ/(2 n! (4 + 2^n)))`. -/
def delta (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ :=
  min ((1 - a - rMax r) / 2) (sigma q a r / (2 * (q + 2).factorial * (4 + 2 ^ (q + 2))))

/-- Fibre height `h₁ = 1 - a - δ`. -/
def h1 (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ := 1 - a - delta q a r

/-- Second-normal height `h₂ = 1/2 - δ`. -/
def h2 (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ := 1 / 2 - delta q a r

/-- The polytope `Δ = {p ≥ 0, u ≤ h₁, w + h₂u ≤ h₂}`. -/
def polytope (q : ℕ) (a : ℝ) (r : ι → ℝ) : Polytope (q + 1) 2 where
  b := largeModelBounds q (h2 q a r)
  ℓ := ![h1 q a r, h2 q a r]

/-- Dilation factor `τ = (R + h₁)/(2h₁)`. -/
def tau (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ := (rMax r + h1 q a r) / (2 * h1 q a r)

/-- Outer lower bound `β = 2^q (1 - h₁)(1 - 2h₂)`. -/
def beta (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ := 2 ^ q * (1 - h1 q a r) * (1 - 2 * h2 q a r)

/-- Gap parameter `d = min(β, (J(h₁,h₂) - Σ r_i^n/n!)/2)/2`. -/
def dgap (q : ℕ) (a : ℝ) (r : ι → ℝ) : ℝ :=
  min (beta q a r)
    ((largeModelMean q (h1 q a r) (h2 q a r) - (∑ i, r i ^ (q + 2)) / ((q + 2).factorial : ℝ)) / 2)
    / 2

/-- The comparator input of the mixed model. -/
def cmpInput (q : ℕ) (a : ℝ) (r : ι → ℝ) : CmpInput (q + 1) 2 where
  Δ := polytope q a r
  P := largeModelGap r
  τ := tau q a r
  β := beta q a r
  d := dgap q a r

/-- Normalised hypotheses of the mixed model (`n = q + 2`). -/
structure Hyp (q : ℕ) (a : ℝ) (r : ι → ℝ) : Prop where
  two_le : 2 ≤ q
  half_lt : 1 / 2 < a
  lt_one : a < 1
  r_pos : ∀ i, 0 < r i
  r_lt : ∀ i, r i < 1 - a
  vol : a ^ (q + 2) + ∑ i, r i ^ (q + 2) < 1

/-- The arithmetic core of `mean_gap`. -/
lemma gap_arith {q : ℕ} {a δ F S σ P : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hFlow : ((q : ℝ) + 2) * (q + 1) ≤ F) (hσ : σ = 1 - a ^ (q + 2) - S)
    (hσδ : 2 * F * (4 + 2 ^ (q + 2)) * δ ≤ σ) (hP_lo : 1 - 4 * (q : ℝ) ^ 2 * δ ^ 2 ≤ P)
    (hP_hi : P ≤ 1 + 2 * q * δ)
    (hpow' : (a + δ) ^ (q + 2) - a ^ (q + 2) ≤ δ * (q + 2) * 2 ^ (q + 2))
    (hmono : a ^ (q + 2) ≤ (a + δ) ^ (q + 2)) (han : a ^ (q + 2) ≤ 1) :
    σ / 2 ≤ P * (1 - (a + δ) ^ (q + 2)) - S := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hapos : 0 ≤ a ^ (q + 2) := pow_nonneg ha0 _
  have hqδ : 0 ≤ 1 + 2 * q * δ := by positivity
  have e1 : (1 - P) * (1 - a ^ (q + 2)) ≤ 4 * q ^ 2 * δ ^ 2 := by
    rcases le_total 0 (1 - P) with h | h
    · have := mul_le_mul_of_nonneg_left (show 1 - a ^ (q + 2) ≤ 1 by linarith) h
      linarith
    · have : 0 ≤ -(1 - P) * (1 - a ^ (q + 2)) := mul_nonneg (by linarith) (by linarith)
      have : 0 ≤ 4 * (q : ℝ) ^ 2 * δ ^ 2 := by positivity
      linarith
  have e2 : P * ((a + δ) ^ (q + 2) - a ^ (q + 2)) ≤
      (1 + 2 * q * δ) * (δ * (q + 2) * 2 ^ (q + 2)) :=
    mul_le_mul hP_hi hpow' (by linarith) hqδ
  have e3 : 4 * (q : ℝ) ^ 2 * δ ^ 2 ≤ 4 * F * δ := by
    have hqF : (q : ℝ) ^ 2 ≤ F := by
      have : ((q : ℝ) + 2) * (q + 1) = q ^ 2 + (3 * q + 2) := by ring
      linarith
    have h4 : δ * (4 * δ) ≤ δ * 1 := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have A := mul_le_mul_of_nonneg_left h4 (sq_nonneg (q : ℝ))
    have B := mul_le_mul_of_nonneg_right hqF hδ.le
    have C : 0 ≤ F * δ := mul_nonneg (le_trans (sq_nonneg _) hqF) hδ.le
    have : 4 * (q : ℝ) ^ 2 * δ ^ 2 = (q : ℝ) ^ 2 * (δ * (4 * δ)) := by ring
    nlinarith
  have e4 : (1 + 2 * q * δ) * (δ * (q + 2) * 2 ^ (q + 2)) ≤ F * 2 ^ (q + 2) * δ := by
    have hq2 : (q : ℝ) * (2 * δ) ≤ q * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hq
    have h1a : (1 + 2 * q * δ) * (q + 2) ≤ (1 + q / 2) * (q + 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h1b : (1 + (q : ℝ) / 2) * (q + 2) ≤ ((q : ℝ) + 2) * (q + 1) := by
      have : ((q : ℝ) + 2) * (q + 1) - (1 + q / 2) * (q + 2) = (q + 2) * (q / 2) := by ring
      have : 0 ≤ ((q : ℝ) + 2) * (q / 2) := by positivity
      linarith
    have h1 : (1 + 2 * q * δ) * (q + 2) ≤ F := by linarith
    have := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ δ * 2 ^ (q + 2) by positivity)
    calc (1 + 2 * q * δ) * (δ * (q + 2) * 2 ^ (q + 2))
        = (1 + 2 * q * δ) * (q + 2) * (δ * 2 ^ (q + 2)) := by ring
      _ ≤ F * (δ * 2 ^ (q + 2)) := this
      _ = F * 2 ^ (q + 2) * δ := by ring
  have hid : P * (1 - (a + δ) ^ (q + 2)) - S - σ / 2 =
      -((1 - P) * (1 - a ^ (q + 2))) - P * ((a + δ) ^ (q + 2) - a ^ (q + 2)) + σ / 2 := by
    rw [hσ]; ring
  have : 2 * F * (4 + 2 ^ (q + 2)) * δ = 2 * (4 * F * δ) + 2 * (F * 2 ^ (q + 2) * δ) := by ring
  linarith

section
variable {q : ℕ} {a : ℝ} {r : ι → ℝ} (H : Hyp q a r)
include H

lemma rMax_nonneg : 0 ≤ rMax r := by
  rw [rMax, Finset.le_fold_max]; exact Or.inl le_rfl

lemma le_rMax (i : ι) : r i ≤ rMax r := by
  rw [rMax, Finset.le_fold_max]; exact Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩

lemma rMax_lt : rMax r < 1 - a := by
  rw [rMax, Finset.fold_max_lt]
  exact ⟨by linarith [H.lt_one], fun i _ => H.r_lt i⟩

lemma sigma_pos : 0 < sigma q a r := by rw [sigma]; linarith [H.vol]

lemma delta_pos : 0 < delta q a r := by
  have := rMax_lt H
  have := sigma_pos H
  unfold delta
  exact lt_min (by linarith) (by positivity)

lemma delta_le : delta q a r ≤ (1 - a - rMax r) / 2 := min_le_left _ _

lemma rMax_lt_h1 : rMax r < h1 q a r := by
  have := delta_le H; have := rMax_lt H; unfold h1; linarith

lemma h1_lt_h2 : h1 q a r < h2 q a r := by
  have := H.half_lt; unfold h1 h2; linarith

lemma h1_lt : h1 q a r < 1 - a := by have := delta_pos H; unfold h1; linarith

lemma h2_lt_half : h2 q a r < 1 / 2 := by have := delta_pos H; unfold h2; linarith

lemma h1_pos : 0 < h1 q a r := lt_of_le_of_lt (rMax_nonneg H) (rMax_lt_h1 H)

lemma tau_pos : 0 < tau q a r := by
  have := h1_pos H; have := rMax_nonneg H; unfold tau; positivity

lemma tau_lt_one : tau q a r < 1 := by
  have := h1_pos H; have := rMax_lt_h1 H
  unfold tau; rw [div_lt_one (by positivity)]; linarith

lemma beta_pos : 0 < beta q a r := by
  have := h1_lt H; have := h2_lt_half H; have := H.lt_one; have := H.half_lt
  unfold beta
  exact mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)

/-- **`lem:lrg-mixed-volume` (quantitative).** The explicit heights keep a positive share of the
volume slack: `J(h₁, h₂) - Σ r_i^n/n! ≥ σ/(2 n!)`. With `P = (1-2δ)^q(1+2qδ)`,
`J(h₁,h₂) = P(1-(a+δ)^n)/n!`; Bernoulli gives `1 - 4q²δ² ≤ P ≤ 1 + 2qδ` and
`(a+δ)^n - a^n ≤ δ n 2^n` (`gap_arith`). -/
lemma mean_gap :
    sigma q a r / (2 * ((q + 2).factorial : ℝ)) ≤
      largeModelMean q (h1 q a r) (h2 q a r) - (∑ i, r i ^ (q + 2)) / ((q + 2).factorial : ℝ) := by
  have hδ := delta_pos H
  have hδR := delta_le H
  have hR0 := rMax_nonneg H
  have hRl := rMax_lt H
  have ha := H.half_lt
  have ha1 := H.lt_one
  have hδσ : delta q a r ≤
      sigma q a r / (2 * (q + 2).factorial * (4 + 2 ^ (q + 2))) := min_le_right _ _
  have hδ4 : delta q a r ≤ 1 / 4 := by linarith
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqf : (1 : ℝ) ≤ (q.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero q)
  have hGq : ((q + 1).factorial : ℝ) = (q + 1) * (q.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hFG : ((q + 2).factorial : ℝ) = (q + 2) * ((q + 1).factorial : ℝ) := by
    rw [show q + 2 = (q + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have hFpos : (0 : ℝ) < ((q + 2).factorial : ℝ) := by positivity
  have hFlow : ((q : ℝ) + 2) * (q + 1) ≤ ((q + 2).factorial : ℝ) := by
    rw [hFG, hGq]
    have := mul_le_mul_of_nonneg_left hqf (show (0 : ℝ) ≤ (q + 2) * (q + 1) by positivity)
    nlinarith
  have hBh : smallModelMean q (h2 q a r) =
      (1 - 2 * delta q a r) ^ q * (1 + 2 * q * delta q a r) / ((q + 1).factorial : ℝ) := by
    unfold smallModelMean h2
    have h2p : (2 : ℝ) ^ q * (1 / 2 - delta q a r) ^ q = (1 - 2 * delta q a r) ^ q := by
      rw [← mul_pow]; congr 1; ring
    rw [h2p, hGq]
    have : (q.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hLM : largeModelMean q (h1 q a r) (h2 q a r) =
      (1 - 2 * delta q a r) ^ q * (1 + 2 * q * delta q a r) *
        (1 - (a + delta q a r) ^ (q + 2)) / ((q + 2).factorial : ℝ) := by
    unfold largeModelMean
    rw [hBh, hFG]
    have h1e : 1 - h1 q a r = a + delta q a r := by unfold h1; ring
    rw [h1e]
    have : ((q + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hB : 1 - q * (2 * delta q a r) ≤ (1 - 2 * delta q a r) ^ q := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * delta q a r) by linarith) q
    simpa [sub_eq_add_neg] using this
  have hP1' : (1 - 2 * delta q a r) ^ q ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hqδ : 0 ≤ 1 + 2 * q * delta q a r := by positivity
  have hP_lo : 1 - 4 * (q : ℝ) ^ 2 * delta q a r ^ 2 ≤
      (1 - 2 * delta q a r) ^ q * (1 + 2 * q * delta q a r) := by
    have := mul_le_mul_of_nonneg_right hB hqδ
    have e : (1 - q * (2 * delta q a r)) * (1 + 2 * q * delta q a r) =
        1 - 4 * (q : ℝ) ^ 2 * delta q a r ^ 2 := by ring
    linarith
  have hP_hi : (1 - 2 * delta q a r) ^ q * (1 + 2 * q * delta q a r) ≤
      1 + 2 * q * delta q a r := mul_le_of_le_one_left hqδ hP1'
  have hpow := BranchLargeHigh.pow_add_le (q + 2) (by linarith : (0 : ℝ) ≤ a) ha1.le hδ.le
    (by linarith)
  have hpow' : (a + delta q a r) ^ (q + 2) - a ^ (q + 2) ≤
      delta q a r * (q + 2) * 2 ^ (q + 2) := by
    push_cast at hpow; linarith
  have hmono : a ^ (q + 2) ≤ (a + delta q a r) ^ (q + 2) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have han : a ^ (q + 2) ≤ 1 := pow_le_one₀ (by linarith) ha1.le
  have hσδ : 2 * ((q + 2).factorial : ℝ) * (4 + 2 ^ (q + 2)) * delta q a r ≤ sigma q a r := by
    have := (le_div_iff₀ (show (0 : ℝ) < 2 * (q + 2).factorial * (4 + 2 ^ (q + 2)) by
      positivity)).1 hδσ
    linarith
  have key := gap_arith hδ hδ4 (by linarith) ha1 hFlow rfl hσδ hP_lo hP_hi hpow' hmono han
  rw [hLM]
  have : sigma q a r / (2 * ((q + 2).factorial : ℝ)) =
      (sigma q a r / 2) / ((q + 2).factorial : ℝ) := by ring
  rw [this, ← sub_div]
  exact div_le_div_of_nonneg_right key hFpos.le

lemma dgap_pos : 0 < dgap q a r := by
  have hb := beta_pos H
  have hm := mean_gap H
  have hs := sigma_pos H
  have : 0 < sigma q a r / (2 * ((q + 2).factorial : ℝ)) := by positivity
  unfold dgap
  exact half_pos (lt_min hb (by linarith))

lemma dgap_lt_beta : dgap q a r < beta q a r := by
  have := dgap_pos H
  have h := min_le_left (beta q a r)
    ((largeModelMean q (h1 q a r) (h2 q a r) - (∑ i, r i ^ (q + 2)) / ((q + 2).factorial : ℝ)) / 2)
  unfold dgap at *
  linarith

/-- The cap `{|p| ≤ R}` lies in `τΔ`. -/
lemma capR_subset :
    momentSimplex (q + 1) (rMax r) ⊆ ((polytope q a r).dilate (tau q a r)).set := by
  -- `|p| ≤ r_i ≤ R < τ h₁ < τ h₂` and `w + h₂ u ≤ |p|` (`h₂ ≤ 1`).
  intro p hp
  have h2le : h2 q a r ≤ 1 := by linarith [h2_lt_half H]
  have hb : ∀ ν j, largeModelBounds q (h2 q a r) ν j ≤ 1 := by
    intro ν j
    fin_cases ν
    · exact Fin.cases (by simp [largeModelBounds]) (fun _ => by simp [largeModelBounds]) j
    · exact Fin.cases (by simpa [largeModelBounds] using h2le)
        (fun _ => by simp [largeModelBounds]) j
  have hrow : ∀ ν, ∑ j, largeModelBounds q (h2 q a r) ν j * p j ≤ rMax r := fun ν =>
    (Finset.sum_le_sum fun j _ => mul_le_of_le_one_left (hp.1 j) (hb ν j)).trans hp.2
  have hh1 := h1_pos H
  have hRτ : rMax r < tau q a r * h1 q a r := by
    unfold tau; rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [rMax_lt_h1 H]
  have hτ := tau_pos H
  have h12 := h1_lt_h2 H
  refine ⟨hp.1, fun ν => ?_⟩
  fin_cases ν
  · have := hrow 0
    simp only [Polytope.dilate, polytope, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith
  · simp only [Polytope.dilate, polytope, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have := hrow 1
    nlinarith

/-- Every cap `{|p| ≤ r_i}` lies in `τΔ`. -/
lemma cap_subset (i : ι) :
    momentSimplex (q + 1) (r i) ⊆ ((polytope q a r).dilate (tau q a r)).set :=
  fun p hp => capR_subset H ⟨hp.1, hp.2.trans (le_rMax H i)⟩

/-- The volume of `Δ` is positive and at most `1` (`Δ ⊆ [0,1]^{q+1}`, and `Δ` contains the
cube `[0, h₁/(2(q+1))]^{q+1}`). -/
lemma volume_bounds :
    0 < (volume (polytope q a r).set).toReal ∧ (volume (polytope q a r).set).toReal ≤ 1 := by
  have hh1 := h1_pos H
  have h12 := h1_lt_h2 H
  have hh2' := h2_lt_half H
  have hh1' := h1_lt H
  have ha := H.half_lt
  have hrow (p : Moments (q + 1)) :
      (∑ j, largeModelBounds q (h2 q a r) 1 j * p j) = h2 q a r * p 0 + ∑ j : Fin q, p j.succ := by
    simp [largeModelBounds, Fin.sum_univ_succ]
  have hrow0 (p : Moments (q + 1)) :
      (∑ j, largeModelBounds q (h2 q a r) 0 j * p j) = p 0 := by
    simp [largeModelBounds, Fin.sum_univ_succ]
  have hfin : volume (polytope q a r).set ≠ ⊤ :=
    (OAI.PackingSufficiencySupport.largeModelRegion_isCompact q (h1 q a r)
      (hh1.trans h12).le).measure_lt_top.ne
  -- upper bound: `Δ ⊆ [0,1]^{q+1}`
  have hsub : (polytope q a r).set ⊆ Icc (0 : Moments (q + 1)) 1 := by
    intro p hp
    have h0 := hp.2 0
    have h1' := hp.2 1
    simp only [polytope, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      hrow0, hrow] at h0 h1'
    refine ⟨fun j => hp.1 j, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Pi.one_apply]; linarith
    · simp only [Pi.one_apply]
      have hle : p j.succ ≤ ∑ i : Fin q, p i.succ :=
        Finset.single_le_sum (f := fun i : Fin q => p i.succ) (fun i _ => hp.1 i.succ)
          (Finset.mem_univ j)
      have := mul_nonneg (hh1.trans h12).le (hp.1 0)
      linarith
  -- lower bound: `[0, ε]^{q+1} ⊆ Δ`, `ε = h₁/(2(q+1))`
  set ε : ℝ := h1 q a r / (2 * (q + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hcube : Icc (0 : Moments (q + 1)) (fun _ => ε) ⊆ (polytope q a r).set := by
    intro p hp
    have hp0 : ∀ j, 0 ≤ p j := fun j => hp.1 j
    have hpε : ∀ j, p j ≤ ε := fun j => hp.2 j
    have hεh : ε * (q + 1) = h1 q a r / 2 := by rw [hε]; field_simp
    refine ⟨hp0, fun ν => ?_⟩
    fin_cases ν
    · simp only [polytope, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hrow0]
      have := hpε 0
      nlinarith
    · simp only [polytope, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, hrow]
      have hs : ∑ j : Fin q, p j.succ ≤ q * ε := by
        have := Finset.sum_le_sum (s := Finset.univ) fun (j : Fin q) _ => hpε j.succ
        simpa using this
      have := hpε 0
      have := mul_le_mul_of_nonneg_left (hpε 0) (hh1.trans h12).le
      nlinarith
  constructor
  · have hmono := measure_mono (μ := volume) hcube
    have hvc : (volume (Icc (0 : Moments (q + 1)) (fun _ => ε))).toReal = ε ^ (q + 1) := by
      erw [Real.volume_Icc_pi_toReal (fun _ => hεpos.le)]; simp
    have := ENNReal.toReal_mono hfin hmono
    rw [hvc] at this
    exact lt_of_lt_of_le (by positivity) this
  · have hmono := measure_mono (μ := volume) hsub
    have hv1 : (volume (Icc (0 : Moments (q + 1)) 1)).toReal = 1 := by
      erw [Real.volume_Icc_pi_toReal (fun _ => zero_le_one)]; simp
    have := ENNReal.toReal_mono (by
      erw [Real.volume_Icc_pi]; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top) hmono
    rwa [hv1] at this

/-- **The comparator hypotheses hold for the mixed model** (`thm:mech-packing` input). -/
theorem cmpInput_spec : (cmpInput q a r).Spec := by
  have hh1 := h1_pos H
  have hh2 : 0 < h2 q a r := hh1.trans (h1_lt_h2 H)
  have hh2' := h2_lt_half H
  have hh1' := h1_lt H
  have ha := H.half_lt
  have hvol := volume_bounds H
  have hmg := mean_gap H
  have hσ := sigma_pos H
  have hS : 0 < sigma q a r / (2 * ((q + 2).factorial : ℝ)) := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, hvol.1, tau_pos H, tau_lt_one H, ?_, dgap_pos H, ?_,
    dgap_lt_beta H⟩
  · exact OAI.PackingSufficiencySupport.largeModelBounds_nonneg q hh2.le
  · intro ν; fin_cases ν
    · simpa [cmpInput, polytope] using hh1
    · simpa [cmpInput, polytope] using hh2
  · exact OAI.PackingSufficiencySupport.largeModelRegion_isCompact q _ hh2.le
  · intro j
    refine Fin.cases ⟨0, by simp [cmpInput, polytope, largeModelBounds]⟩
      (fun j => ⟨1, by simp [cmpInput, polytope, largeModelBounds]⟩) j
  · exact (OAI.PackingSufficiencySupport.continuous_largeModelGap r).continuousOn
  · change ConcaveOn ℝ (polytope q a r).set (largeModelGap r)
    rw [OAI.PackingSufficiencySupport.largeModelGap_eq_cappedAffine]
    exact OAI.PackingSufficiencySupport.concaveOn_cappedAffine _ _ _ _ (fun _ => by norm_num)
      (Polytope.convex_set _)
  · intro p hp hout
    have hs : rMax r < ∑ j, p j := by
      by_contra hle
      push_neg at hle
      exact hout (capR_subset H ⟨hp.1, hle⟩)
    have hzero (i : ι) : max (r i - ∑ j, p j) 0 = 0 :=
      max_eq_right (by linarith [le_rMax H i])
    change beta q a r ≤ largeModelGap r p
    simp only [largeModelGap, hzero, Finset.sum_const_zero, sub_zero]
    exact OAI.PackingSufficiencySupport.largeModelDensity_lower q hh2'.le hp
  · -- `d ≤ (J - S)/4 < (J - S)/vol(Δ) = mean`
    have hint : (∫ p in (polytope q a r).set, largeModelGap r p) =
        largeModelMean q (h1 q a r) (h2 q a r) -
          (∑ i, r i ^ (q + 2)) / ((q + 2).factorial : ℝ) :=
      OAI.PackingSufficiencySupport.integral_largeModelGap r (fun i => (H.r_pos i).le) hh1.le
        (by linarith) hh2.le (by linarith)
        (fun i => (le_rMax H i).trans (rMax_lt_h1 H).le)
        (fun i => (le_rMax H i).trans ((rMax_lt_h1 H).trans (h1_lt_h2 H)).le)
    change dgap q a r < (∫ p in (polytope q a r).set, largeModelGap r p) /
      (volume (polytope q a r).set).toReal
    rw [hint]
    set G := largeModelMean q (h1 q a r) (h2 q a r) -
      (∑ i, r i ^ (q + 2)) / ((q + 2).factorial : ℝ)
    have hG : 0 < G := lt_of_lt_of_le hS hmg
    have hd : dgap q a r ≤ G / 4 := by
      unfold dgap
      have := min_le_right (beta q a r) (G / 2)
      linarith
    have : G ≤ G / (volume (polytope q a r).set).toReal := by
      rw [le_div_iff₀ hvol.1]; nlinarith [hvol.2]
    linarith

end

end SymplecticPacking.BranchLargeHigh.Mixed
