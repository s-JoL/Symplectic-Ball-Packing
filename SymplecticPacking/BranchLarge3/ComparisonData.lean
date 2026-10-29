import SymplecticPacking.BranchLarge3.Params
import OAI.Geometry.BallPacking.Toric.SixModelComparisonData

/-!
# Step S1: the comparison data of the six-dimensional model (explicit)

For radii `r_i > 0` and a rational `a ∈ (1/2, 1)` with `r_i < 1 - a` and `Σ r_i³ < 1 - a³`,
the truncated moment region `Δ = {p ≥ 0 : p₁ ≤ h₁, p₁ + p₂ ≤ h₂}` and the comparison constants
are given by explicit formulas (OpenAI `exists_six_model_comparison_data`, de-existentialised):
with `s = 1 - a`, `b = (2 - a)/3`, `R = max_i r_i`, `V = 1 - a³ - Σ r_i³` and
`m = min (s - R, (2a-1)/6, V/100)`, `M = ⌈1/m⌉ + 1`, `δ = 1/M` (rational, `δ < m`),

  `h₁ = s - δ, e = s - δ/2, d₁ = s + δ/2, h₂ = b - δ, d₂ = b - δ/2`,
  `τ = (R/h₁ + 1)/2`, `ε = 9 (b - h₂) = 9 δ`.

The mean `∫_Δ (H₀ - Σ caps) = sixModelMean s b h₁ h₂ - Σ r_i³/6` is positive because
`sixModelMean s b (s-δ) (b-δ) ≥ (1 - a³)/6 - 15 δ` (`sixModelMean_shift`).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.MomentPolytope
open Finset MeasureTheory
open scoped Pointwise

/-- The comparison data `(h₁, e, d₁, h₂, d₂, τ, ε)`. -/
structure CmpData where
  h₁ : ℚ
  e : ℚ
  d₁ : ℚ
  h₂ : ℚ
  d₂ : ℚ
  τ : ℝ
  ε : ℝ

/-- `R = max (0, max_i r_i)`. -/
def maxRad {N : ℕ} (r : Fin N → ℝ) : ℝ := (univ : Finset (Fin N)).fold max 0 r

lemma le_maxRad {N : ℕ} (r : Fin N → ℝ) (i : Fin N) : r i ≤ maxRad r :=
  (Finset.le_fold_max (b := 0) (s := univ) (f := r) (r i)).2 (Or.inr ⟨i, mem_univ i, le_rfl⟩)

lemma maxRad_lt {N : ℕ} (r : Fin N → ℝ) {x : ℝ} (hx : 0 < x) (h : ∀ i, r i < x) :
    maxRad r < x :=
  (Finset.fold_max_lt (b := 0) (s := univ) (f := r) x).2 ⟨hx, fun i _ => h i⟩

/-- The real margin `m`. -/
def cmpMargin {N : ℕ} (r : Fin N → ℝ) (a : ℚ) : ℝ :=
  min (min ((1 - (a : ℝ)) - maxRad r) ((2 * (a : ℝ) - 1) / 6))
    ((1 - (a : ℝ) ^ 3 - ∑ i, r i ^ 3) / 100)

/-- The denominator `M = ⌈1/m⌉ + 1`. -/
def cmpDen {N : ℕ} (r : Fin N → ℝ) (a : ℚ) : ℕ := ⌈1 / cmpMargin r a⌉₊ + 1

/-- The rational step `δ = 1/M`. -/
def cmpDelta {N : ℕ} (r : Fin N → ℝ) (a : ℚ) : ℚ := 1 / (cmpDen r a : ℚ)

/-- The explicit comparison data. -/
def cmpData {N : ℕ} (r : Fin N → ℝ) (a : ℚ) : CmpData where
  h₁ := (1 - a) - cmpDelta r a
  e := (1 - a) - cmpDelta r a / 2
  d₁ := (1 - a) + cmpDelta r a / 2
  h₂ := (2 - a) / 3 - cmpDelta r a
  d₂ := (2 - a) / 3 - cmpDelta r a / 2
  τ := (maxRad r / (((1 - a) - cmpDelta r a : ℚ) : ℝ) + 1) / 2
  ε := 9 * (cmpDelta r a : ℝ)

/-- The admissibility hypotheses of S1. -/
structure CmpHyp {N : ℕ} (r : Fin N → ℝ) (a : ℚ) : Prop where
  ne : 0 < N
  r_pos : ∀ i, 0 < r i
  a_gt : (1 : ℝ) / 2 < a
  a_lt : (a : ℝ) < 1
  r_lt : ∀ i, r i < 1 - (a : ℝ)
  vol : ∑ i, r i ^ 3 < 1 - (a : ℝ) ^ 3

/-- The truncated six-model mean loses at most `15 δ`. -/
lemma sixModelMean_shift {a δ : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 - a ^ 3) / 6 - 15 * δ ≤
      sixModelMean (1 - a) ((2 - a) / 3) ((1 - a) - δ) ((2 - a) / 3 - δ) := by
  have hlim := sixModelMean_limit_value a
  unfold sixModelMean at hlim ⊢
  have hx0 : 0 ≤ (2 - a) / 3 - (1 - a) := by linarith
  have hx1 : (2 - a) / 3 - (1 - a) ≤ 1 := by linarith
  have hcube := cube_add_le hx0 hx1 hδ0 hδ1
  have hδ2 : ((1 - a) - δ) * δ ^ 2 ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ0]
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  nlinarith [hcube, hδ2, hδ3, hlim]

section spec

variable {N : ℕ} {r : Fin N → ℝ} {a : ℚ}

lemma cmpMargin_pos (h : CmpHyp r a) : 0 < cmpMargin r a := by
  have hR : maxRad r < 1 - (a : ℝ) := maxRad_lt r (by linarith [h.a_lt]) h.r_lt
  refine lt_min (lt_min (by linarith) (by linarith [h.a_gt])) (by linarith [h.vol])

lemma cmpDelta_cast : ((cmpDelta r a : ℚ) : ℝ) = 1 / (cmpDen r a : ℝ) := by
  unfold cmpDelta; push_cast; ring

lemma cmpDelta_pos : (0 : ℝ) < cmpDelta r a := by
  rw [cmpDelta_cast]; unfold cmpDen; positivity

lemma cmpDelta_lt (h : CmpHyp r a) : ((cmpDelta r a : ℚ) : ℝ) < cmpMargin r a := by
  have hm := cmpMargin_pos h
  rw [cmpDelta_cast]
  have hM : 1 / cmpMargin r a < (cmpDen r a : ℝ) := by
    unfold cmpDen; push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hMp : (0 : ℝ) < cmpDen r a := by unfold cmpDen; positivity
  rw [div_lt_iff₀ hMp]
  rw [div_lt_iff₀ hm] at hM
  linarith

theorem cmpData_spec (h : CmpHyp r a) :
    let D := cmpData r a
    (∀ i, r i < D.h₁) ∧ D.h₁ < D.e ∧ (D.e : ℝ) < 1 - a ∧ 1 - (a : ℝ) < D.d₁ ∧ D.d₁ < D.h₂ ∧
      D.h₂ < D.d₂ ∧ (D.d₂ : ℝ) < (2 - a) / 3 ∧ 0 < (D.h₁ : ℝ) ∧ 0 < (D.h₂ : ℝ) ∧
      0 < D.τ ∧ D.τ < 1 ∧ 0 < D.ε ∧
      (∀ i, momentSimplex 2 (r i) ⊆ D.τ • region sixModelBounds ![(D.h₁ : ℝ), D.h₂]) ∧
      ConcaveOn ℝ (region sixModelBounds ![(D.h₁ : ℝ), D.h₂])
        (sixModelGap (1 - a) ((2 - a) / 3) r) ∧
      (0 < ∫ p in region sixModelBounds ![(D.h₁ : ℝ), D.h₂],
        sixModelGap (1 - a) ((2 - a) / 3) r p) ∧
      ∀ p ∈ region sixModelBounds ![(D.h₁ : ℝ), D.h₂],
        p ∉ D.τ • region sixModelBounds ![(D.h₁ : ℝ), D.h₂] →
          D.ε ≤ sixModelGap (1 - a) ((2 - a) / 3) r p := by
  intro D
  have hδ := cmpDelta_lt h
  have hδ0 : (0 : ℝ) < cmpDelta r a := cmpDelta_pos
  have hm1 : cmpMargin r a ≤ (1 - (a : ℝ)) - maxRad r :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : cmpMargin r a ≤ (2 * (a : ℝ) - 1) / 6 := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : cmpMargin r a ≤ (1 - (a : ℝ) ^ 3 - ∑ i, r i ^ 3) / 100 := min_le_right _ _
  have ha := h.a_gt
  have ha1 := h.a_lt
  set δ : ℝ := ((cmpDelta r a : ℚ) : ℝ) with hδdef
  set R := maxRad r with hRdef
  have hR0 : 0 < R := by
    have := le_maxRad r ⟨0, h.ne⟩; have := h.r_pos ⟨0, h.ne⟩; linarith
  have hRi : ∀ i, r i ≤ R := le_maxRad r
  -- the casts of the five rationals
  have eh₁ : ((D.h₁ : ℚ) : ℝ) = (1 - a) - δ := by simp [D, cmpData, hδdef]
  have ee : ((D.e : ℚ) : ℝ) = (1 - a) - δ / 2 := by simp [D, cmpData, hδdef]
  have ed₁ : ((D.d₁ : ℚ) : ℝ) = (1 - a) + δ / 2 := by simp [D, cmpData, hδdef]
  have eh₂ : ((D.h₂ : ℚ) : ℝ) = (2 - a) / 3 - δ := by simp [D, cmpData, hδdef]
  have ed₂ : ((D.d₂ : ℚ) : ℝ) = (2 - a) / 3 - δ / 2 := by simp [D, cmpData, hδdef]
  have eτ : D.τ = (R / ((1 - a) - δ) + 1) / 2 := by
    simp only [D, cmpData, hRdef, hδdef]; push_cast; ring
  have eε : D.ε = 9 * δ := by simp [D, cmpData, hδdef]
  have hh₁R : R < (1 - a) - δ := by linarith
  have hh₁ : (0 : ℝ) < (1 - a) - δ := by linarith
  have hb : (1 - (a : ℝ)) + δ / 2 < (2 - a) / 3 - δ := by linarith
  have hh₂ : (0 : ℝ) < (2 - a) / 3 - δ := by linarith
  have hh₁h₂ : (1 - (a : ℝ)) - δ ≤ (2 - a) / 3 - δ := by linarith
  have hRτ₁ : R < D.τ * ((1 - a) - δ) := by
    rw [eτ]; field_simp; linarith
  have hRτ₂ : R < D.τ * ((2 - a) / 3 - δ) := by
    have hτ0 : 0 < D.τ := by rw [eτ]; positivity
    nlinarith
  have hτ1 : D.τ < 1 := by
    rw [eτ, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    have : R / ((1 - a) - δ) < 1 := (div_lt_one hh₁).2 hh₁R
    linarith
  have hτ0 : 0 < D.τ := by rw [eτ]; positivity
  have hcap (i : Fin N) :
      momentSimplex 2 (r i) ⊆ D.τ • region sixModelBounds ![(D.h₁ : ℝ), D.h₂] := by
    apply cap_into_scaled_region _ _ sixModelBounds_le_one hτ0
    intro ν
    fin_cases ν
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, eh₁]
      exact (hRi i).trans hRτ₁.le
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, eh₂]
      exact (hRi i).trans hRτ₂.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτ0, hτ1, ?_, hcap, ?_, ?_, ?_⟩
  · intro i; rw [eh₁]; exact (hRi i).trans_lt hh₁R
  · have : ((D.h₁ : ℚ) : ℝ) < ((D.e : ℚ) : ℝ) := by rw [eh₁, ee]; linarith
    exact_mod_cast this
  · rw [ee]; linarith
  · rw [ed₁]; linarith
  · have : ((D.d₁ : ℚ) : ℝ) < ((D.h₂ : ℚ) : ℝ) := by rw [ed₁, eh₂]; linarith
    exact_mod_cast this
  · have : ((D.h₂ : ℚ) : ℝ) < ((D.d₂ : ℚ) : ℝ) := by rw [eh₂, ed₂]; linarith
    exact_mod_cast this
  · rw [ed₂]; linarith
  · rw [eh₁]; exact hh₁
  · rw [eh₂]; exact hh₂
  · rw [eε]; linarith
  · rw [sixModelGap_eq_cappedAffine]
    apply concaveOn_cappedAffine _ _ _ _ ?_ (convex_region _ _)
    intro i
    cases i <;> norm_num
  · rw [integral_sixModelGap r (fun i => (h.r_pos i).le) (by rw [eh₁]; exact hh₁.le)
      (by rw [eh₁]; linarith) (by rw [eh₂]; linarith)
      (fun i => by rw [eh₁]; exact ((hRi i).trans hh₁R.le))
      (fun i => by rw [eh₂]; linarith [hRi i])]
    rw [eh₁, eh₂]
    have hshift := sixModelMean_shift ha ha1 hδ0.le (by linarith)
    linarith
  · intro p hp hout
    have hz := sum_caps_zero_outside r (fun _ hp => hp.1) hcap hp hout
    simp only [sixModelGap, hz, sub_zero]
    have := sixModelDensity_lower (s := 1 - (a : ℝ)) (b := (2 - a) / 3)
      (by rw [eh₂]; linarith) hp
    rw [eε]
    rw [eh₂] at this
    linarith

end spec

end SymplecticPacking.BranchLarge3
