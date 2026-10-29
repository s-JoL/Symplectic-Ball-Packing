import Mathlib
import SymplecticPacking.Params
import SymplecticPacking.Inner.Inverse

/-!
# The y-side of the inner map

`sec:pll`, the `y`-side of the inner map: the angular wall `Ṽ` and its signed inverse `Ỹ`
(paper `cons:pll-morse`, `lem:pll-wall`, `lem:pll-mean` (V-c)).

Notation: `e = P.eq_`, `h = P.h`, `S = Real.smoothTransition`, `c_V = 1 - 2 w_V`,
`b₀ = √(2/e)`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology Real
open scoped ContDiff

variable (P : Params)

/-! ### Definitions (`cons:pll-morse`) -/

/-- `w_V = e / (20 h)`. -/
def wV : ℝ := P.eq_ / (20 * P.h)

/-- `c_V = 1 - 2 w_V`. -/
def cV : ℝ := 1 - 2 * wV P

/-- The argument of the step in `st`: `(4y² - c_V²)/(1 - c_V²)`. -/
def argV (y : ℝ) : ℝ := (4 * y ^ 2 - cV P ^ 2) / (1 - cV P ^ 2)

/-- `st(y) = S((4y² - c_V²)/(1 - c_V²))`. -/
def stV (y : ℝ) : ℝ := Real.smoothTransition (argV P y)

/-- `Ṽ(y) = e y²/2 + 2h st(y)`. -/
def Vtilde (y : ℝ) : ℝ := P.eq_ * y ^ 2 / 2 + 2 * P.h * stV P y

/-- `y_c = ½ √(c_V² + (1 - c_V²)/2)`. -/
def yc : ℝ := 1 / 2 * √(cV P ^ 2 + (1 - cV P ^ 2) / 2)

/-- `σ_V(y) = st(y)/y²` (and `σ_V(0) = 0`, which is Lean's `x / 0 = 0`). -/
def sigmaV (y : ℝ) : ℝ := stV P y / y ^ 2

/-- `Σ_V(y) = y √(e/2 + 2h σ_V(y))`. -/
def SigmaV (y : ℝ) : ℝ := y * √(P.eq_ / 2 + 2 * P.h * sigmaV P y)

/-- `Ỹ = Σ_V⁻¹`. -/
def Ytilde : ℝ → ℝ := invR (SigmaV P)

/-- `v_ε = √(e/2) (½ - w_V)`. -/
def vEps : ℝ := √(P.eq_ / 2) * (1 / 2 - wV P)

/-- `μ̃ = ∫_{-1/2}^{1/2} Ṽ`. -/
def muV : ℝ := ∫ y in (-1 / 2 : ℝ)..(1 / 2), Vtilde P y

/-! ### Elementary constants -/

lemma wV_pos : 0 < wV P := div_pos P.eq_pos (by linarith [P.h_pos])

lemma wV_le : wV P ≤ 1 / 2000 := by
  unfold wV
  rw [div_le_iff₀ (by linarith [P.h_pos])]
  linarith [P.eq_le_h]

lemma cV_pos : 0 < cV P := by unfold cV; linarith [wV_le P]

lemma cV_lt_one : cV P < 1 := by unfold cV; linarith [wV_pos P]

lemma one_sub_cV_sq_pos : 0 < 1 - cV P ^ 2 := by
  have := cV_pos P; have := cV_lt_one P; nlinarith

lemma half_sub_wV : 1 / 2 - wV P = cV P / 2 := by unfold cV; ring

/-! ### The step `st` -/

lemma smoothTransition_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  unfold Real.smoothTransition
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have := expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  field_simp
  ring

lemma stV_nonneg (y : ℝ) : 0 ≤ stV P y := Real.smoothTransition.nonneg _

lemma stV_le_one (y : ℝ) : stV P y ≤ 1 := Real.smoothTransition.le_one _

lemma stV_eq_zero {y : ℝ} (hy : |y| ≤ 1 / 2 - wV P) : stV P y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  unfold argV
  rw [div_le_iff₀ (one_sub_cV_sq_pos P), zero_mul]
  rw [half_sub_wV] at hy
  have h0 := abs_nonneg y
  have : |y| ^ 2 ≤ (cV P / 2) ^ 2 := pow_le_pow_left₀ h0 hy 2
  rw [sq_abs] at this
  nlinarith

lemma stV_zero : stV P 0 = 0 := stV_eq_zero P (by simp; linarith [wV_le P])

lemma contDiff_argV : ContDiff ℝ ∞ (argV P) := by unfold argV; fun_prop

lemma contDiff_stV : ContDiff ℝ ∞ (stV P) :=
  Real.smoothTransition.contDiff.comp (contDiff_argV P)

lemma hasDerivAt_stV (y : ℝ) :
    HasDerivAt (stV P) (deriv Real.smoothTransition (argV P y) *
      (4 * (2 * y) / (1 - cV P ^ 2))) y := by
  have ha : HasDerivAt (argV P) (4 * (2 * y) / (1 - cV P ^ 2)) y := by
    unfold argV
    have := ((hasDerivAt_pow 2 y).const_mul 4).sub_const (cV P ^ 2)
    simpa using this.div_const (1 - cV P ^ 2)
  have hS : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (argV P y))
      (argV P y) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _ |>.hasDerivAt
  exact hS.comp y ha

/-! ### `Ṽ` (`lem:pll-wall` (a)–(c)) -/

lemma contDiff_Vtilde : ContDiff ℝ ∞ (Vtilde P) := by
  unfold Vtilde; have := contDiff_stV P; fun_prop

lemma Vtilde_ge (y : ℝ) : P.eq_ * y ^ 2 / 2 ≤ Vtilde P y := by
  unfold Vtilde; have := stV_nonneg P y; have := P.h_pos; nlinarith

lemma Vtilde_nonneg (y : ℝ) : 0 ≤ Vtilde P y :=
  le_trans (by have := P.eq_pos; positivity) (Vtilde_ge P y)

lemma Vtilde_pos {y : ℝ} (hy : y ≠ 0) : 0 < Vtilde P y :=
  lt_of_lt_of_le (by have := P.eq_pos; positivity) (Vtilde_ge P y)

lemma hasDerivAt_Vtilde (y : ℝ) :
    HasDerivAt (Vtilde P) (P.eq_ * y + 2 * P.h * (deriv Real.smoothTransition (argV P y) *
      (4 * (2 * y) / (1 - cV P ^ 2)))) y := by
  unfold Vtilde
  have h1 : HasDerivAt (fun y : ℝ => P.eq_ * y ^ 2 / 2) (P.eq_ * y) y := by
    have := ((hasDerivAt_pow 2 y).const_mul P.eq_).div_const 2
    convert this using 1; push_cast; ring
  exact h1.add ((hasDerivAt_stV P y).const_mul (2 * P.h))

/-- (V-a) `Ṽ'(y) ≥ e y` for `y > 0`. -/
theorem Vtilde_mono {y : ℝ} (hy : 0 < y) : P.eq_ * y ≤ deriv (Vtilde P) y := by
  rw [(hasDerivAt_Vtilde P y).deriv]
  have hS := Real.smoothTransition.monotone.deriv_nonneg (x := argV P y)
  have : 0 ≤ 4 * (2 * y) / (1 - cV P ^ 2) := div_nonneg (by linarith) (one_sub_cV_sq_pos P).le
  have hh := P.h_pos
  have := mul_nonneg hS this
  nlinarith

/-- The mirror statement: `Ṽ'(y) ≤ e y` for `y < 0`. -/
theorem Vtilde_mono_neg {y : ℝ} (hy : y < 0) : deriv (Vtilde P) y ≤ P.eq_ * y := by
  rw [(hasDerivAt_Vtilde P y).deriv]
  have hS := Real.smoothTransition.monotone.deriv_nonneg (x := argV P y)
  have : 4 * (2 * y) / (1 - cV P ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (one_sub_cV_sq_pos P).le
  have hh := P.h_pos
  have := mul_nonpos_of_nonneg_of_nonpos hS this
  nlinarith

/-- (V-d) `½ - w_V < y_c < ½`. -/
theorem yc_bounds : 1 / 2 - wV P < yc P ∧ yc P < 1 / 2 := by
  have h0 := cV_pos P; have h1 := cV_lt_one P
  rw [half_sub_wV]
  unfold yc
  constructor
  · have : cV P < √(cV P ^ 2 + (1 - cV P ^ 2) / 2) :=
      (Real.lt_sqrt h0.le).mpr (by nlinarith)
    linarith
  · have : √(cV P ^ 2 + (1 - cV P ^ 2) / 2) < 1 :=
      (Real.sqrt_lt' one_pos).mpr (by nlinarith)
    linarith

/-- (V-d) `Ṽ(y) ≤ h - 2e` implies `st(y) < ½` and `|y| < y_c`. -/
theorem Vtilde_le_lt_yc {y : ℝ} (hy : Vtilde P y ≤ P.h - 2 * P.eq_) :
    stV P y < 1 / 2 ∧ |y| < yc P := by
  have he := P.eq_pos; have hh := P.h_pos
  have hst : stV P y < 1 / 2 := by
    have := Vtilde_ge P y
    have : 0 ≤ P.eq_ * y ^ 2 / 2 := by positivity
    unfold Vtilde at hy
    nlinarith
  refine ⟨hst, ?_⟩
  have harg : argV P y < 1 / 2 := by
    by_contra hc
    have := Real.smoothTransition.monotone (not_lt.mp hc)
    rw [smoothTransition_half] at this
    exact absurd hst (not_lt.mpr this)
  have hd := one_sub_cV_sq_pos P
  unfold argV at harg
  rw [div_lt_iff₀ hd] at harg
  have hq : 0 ≤ cV P ^ 2 + (1 - cV P ^ 2) / 2 := by positivity
  have hyc : yc P ^ 2 = (cV P ^ 2 + (1 - cV P ^ 2) / 2) / 4 := by
    unfold yc; rw [mul_pow, Real.sq_sqrt hq]; ring
  have hyc0 : 0 ≤ yc P := by unfold yc; positivity
  apply abs_lt_of_sq_lt_sq _ hyc0
  rw [hyc]; linarith

/-! ### (V-c) the mean `μ̃` -/

lemma continuous_stV : Continuous (stV P) := (contDiff_stV P).continuous

lemma integral_stV_le : ∫ y in (-1 / 2 : ℝ)..(1 / 2), stV P y ≤ 2 * wV P := by
  have hw := wV_pos P; have hw' := wV_le P
  have hi : ∀ a b : ℝ, IntervalIntegrable (stV P) MeasureTheory.volume a b :=
    fun a b => (continuous_stV P).intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi (-1 / 2) (-(1 / 2 - wV P)))
    (hi _ (1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 2 - wV P)) (1 / 2 - wV P))
    (hi _ (1 / 2))
  have hmid : ∫ y in (-(1 / 2 - wV P))..(1 / 2 - wV P), stV P y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact stV_eq_zero P (abs_le.mpr ⟨hy.1, hy.2⟩)
  have hleft : ∫ y in (-1 / 2 : ℝ)..(-(1 / 2 - wV P)), stV P y ≤ wV P := by
    have := intervalIntegral.integral_mono_on (by linarith) (hi (-1 / 2) (-(1 / 2 - wV P)))
      (intervalIntegrable_const (c := (1 : ℝ))) (fun y _ => stV_le_one P y)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this; linarith
  have hright : ∫ y in (1 / 2 - wV P)..(1 / 2 : ℝ), stV P y ≤ wV P := by
    have := intervalIntegral.integral_mono_on (by linarith) (hi (1 / 2 - wV P) (1 / 2))
      (intervalIntegrable_const (c := (1 : ℝ))) (fun y _ => stV_le_one P y)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this; linarith
  linarith

/-- (V-c) `μ̃ ≤ e/24 + e/5 = 29e/120`. -/
theorem muV_le : muV P ≤ 29 * P.eq_ / 120 := by
  unfold muV Vtilde
  have hc1 : Continuous fun y : ℝ => P.eq_ * y ^ 2 / 2 := by fun_prop
  have hc2 : Continuous fun y : ℝ => 2 * P.h * stV P y := by
    have := continuous_stV P; fun_prop
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  have hq : ∫ y in (-1 / 2 : ℝ)..(1 / 2), P.eq_ * y ^ 2 / 2 = P.eq_ / 24 := by
    simp only [mul_div_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow]
    ring
  rw [hq]
  have := integral_stV_le P
  have hh := P.h_pos
  have : 2 * P.h * ∫ y in (-1 / 2 : ℝ)..(1 / 2), stV P y ≤ 2 * P.h * (2 * wV P) :=
    mul_le_mul_of_nonneg_left this (by linarith)
  have hw : 2 * P.h * (2 * wV P) = P.eq_ / 5 := by
    unfold wV; field_simp; ring
  linarith

/-! ### `Σ_V` (`lem:pll-wall` (d)) -/

lemma sigmaV_nonneg (y : ℝ) : 0 ≤ sigmaV P y := div_nonneg (stV_nonneg P y) (sq_nonneg y)

lemma sigmaV_eq_zero {y : ℝ} (hy : |y| ≤ 1 / 2 - wV P) : sigmaV P y = 0 := by
  unfold sigmaV; rw [stV_eq_zero P hy, zero_div]

lemma contDiff_sigmaV : ContDiff ℝ ∞ (sigmaV P) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hr : 0 < 1 / 2 - wV P := by linarith [wV_le P]
    have hev : ∀ᶠ z in 𝓝 (0 : ℝ), |z| < 1 / 2 - wV P :=
      (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by simpa using hr))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    exact sigmaV_eq_zero P hz.le
  · exact ((contDiff_stV P).contDiffAt).div (by fun_prop) (pow_ne_zero 2 hy)

lemma gammaV_ge (y : ℝ) : √(P.eq_ / 2) ≤ √(P.eq_ / 2 + 2 * P.h * sigmaV P y) :=
  Real.sqrt_le_sqrt (by have := sigmaV_nonneg P y; have := P.h_pos; nlinarith)

lemma gammaV_arg_pos (y : ℝ) : 0 < P.eq_ / 2 + 2 * P.h * sigmaV P y := by
  have := sigmaV_nonneg P y; have := P.h_pos; have := P.eq_pos; nlinarith

theorem contDiff_SigmaV : ContDiff ℝ ∞ (SigmaV P) := by
  unfold SigmaV
  have hs : ContDiff ℝ ∞ fun y => √(P.eq_ / 2 + 2 * P.h * sigmaV P y) :=
    ContDiff.sqrt (by have := contDiff_sigmaV P; fun_prop) (fun y => (gammaV_arg_pos P y).ne')
  exact contDiff_id.mul hs

/-- `Σ_V² = Ṽ`. -/
theorem SigmaV_sq (y : ℝ) : SigmaV P y ^ 2 = Vtilde P y := by
  unfold SigmaV
  rw [mul_pow, Real.sq_sqrt (gammaV_arg_pos P y).le]
  by_cases hy : y = 0
  · subst hy; unfold Vtilde; rw [stV_zero]; ring
  · unfold Vtilde sigmaV; field_simp

theorem SigmaV_linear {y : ℝ} (hy : |y| ≤ 1 / 2 - wV P) : SigmaV P y = √(P.eq_ / 2) * y := by
  unfold SigmaV; rw [sigmaV_eq_zero P hy]; ring_nf

theorem abs_SigmaV_ge (y : ℝ) : √(P.eq_ / 2) * |y| ≤ |SigmaV P y| := by
  unfold SigmaV
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_left (gammaV_ge P y) (abs_nonneg y)

lemma SigmaV_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ SigmaV P y :=
  mul_nonneg hy (Real.sqrt_nonneg _)

lemma SigmaV_nonpos {y : ℝ} (hy : y ≤ 0) : SigmaV P y ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg hy (Real.sqrt_nonneg _)

/-- `Σ_V = √Ṽ` for `y ≥ 0` (sign of `y`). -/
theorem SigmaV_eq_sqrt {y : ℝ} (hy : 0 ≤ y) : SigmaV P y = √(Vtilde P y) := by
  rw [← SigmaV_sq, Real.sqrt_sq (SigmaV_nonneg P hy)]

/-- `Σ_V = -√Ṽ` for `y ≤ 0`. -/
theorem SigmaV_eq_neg_sqrt {y : ℝ} (hy : y ≤ 0) : SigmaV P y = -√(Vtilde P y) := by
  rw [← SigmaV_sq, Real.sqrt_sq_eq_abs, abs_of_nonpos (SigmaV_nonpos P hy), neg_neg]

theorem SigmaV_deriv_pos (y : ℝ) : 0 < deriv (SigmaV P) y := by
  have he := P.eq_pos
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hV := Vtilde_pos P hy.ne
    have hd : HasDerivAt (fun z => -√(Vtilde P z))
        (-(deriv (Vtilde P) y / (2 * √(Vtilde P y)))) y :=
      (((contDiff_Vtilde P).differentiable (by simp) y).hasDerivAt.sqrt hV.ne').neg
    have hev : SigmaV P =ᶠ[𝓝 y] fun z => -√(Vtilde P z) := by
      filter_upwards [gt_mem_nhds hy] with z hz using SigmaV_eq_neg_sqrt P hz.le
    rw [(hd.congr_of_eventuallyEq hev).deriv]
    have := Vtilde_mono_neg P hy
    have : deriv (Vtilde P) y < 0 := by nlinarith
    have : 0 < √(Vtilde P y) := Real.sqrt_pos.mpr hV
    have : deriv (Vtilde P) y / (2 * √(Vtilde P y)) < 0 := div_neg_of_neg_of_pos ‹_› (by linarith)
    linarith
  · subst hy
    have hr : 0 < 1 / 2 - wV P := by linarith [wV_le P]
    have h0 : |(0 : ℝ)| < 1 / 2 - wV P := by rw [abs_zero]; exact hr
    have hev : SigmaV P =ᶠ[𝓝 0] fun z => √(P.eq_ / 2) * z := by
      filter_upwards [(continuous_abs.tendsto (0 : ℝ)).eventually
        (gt_mem_nhds h0)] with z hz using SigmaV_linear P hz.le
    rw [((hasDerivAt_id (0 : ℝ)).const_mul (√(P.eq_ / 2))).congr_of_eventuallyEq hev |>.deriv]
    simp only [mul_one]
    exact Real.sqrt_pos.mpr (by linarith)
  · have hV := Vtilde_pos P hy.ne'
    have hd : HasDerivAt (fun z => √(Vtilde P z))
        (deriv (Vtilde P) y / (2 * √(Vtilde P y))) y :=
      ((contDiff_Vtilde P).differentiable (by simp) y).hasDerivAt.sqrt hV.ne'
    have hev : SigmaV P =ᶠ[𝓝 y] fun z => √(Vtilde P z) := by
      filter_upwards [lt_mem_nhds hy] with z hz using SigmaV_eq_sqrt P hz.le
    rw [(hd.congr_of_eventuallyEq hev).deriv]
    have := Vtilde_mono P hy
    have : 0 < √(Vtilde P y) := Real.sqrt_pos.mpr hV
    apply div_pos (by nlinarith) (by linarith)

theorem SigmaV_strictMono : StrictMono (SigmaV P) := strictMono_of_deriv_pos (SigmaV_deriv_pos P)

theorem SigmaV_continuous : Continuous (SigmaV P) := (contDiff_SigmaV P).continuous

theorem SigmaV_tendsto_atTop : Tendsto (SigmaV P) atTop atTop := by
  have hc : 0 < √(P.eq_ / 2) := Real.sqrt_pos.mpr (by linarith [P.eq_pos])
  refine tendsto_atTop_mono' _ ?_ (tendsto_id.const_mul_atTop hc)
  filter_upwards [eventually_ge_atTop 0] with y hy
  have := abs_SigmaV_ge P y
  rwa [abs_of_nonneg hy, abs_of_nonneg (SigmaV_nonneg P hy)] at this

theorem SigmaV_tendsto_atBot : Tendsto (SigmaV P) atBot atBot := by
  have hc : 0 < √(P.eq_ / 2) := Real.sqrt_pos.mpr (by linarith [P.eq_pos])
  refine tendsto_atBot_mono' _ ?_ (tendsto_id.const_mul_atBot hc)
  filter_upwards [eventually_le_atBot 0] with y hy
  have := abs_SigmaV_ge P y
  rw [abs_of_nonpos hy, abs_of_nonpos (SigmaV_nonpos P hy)] at this
  simp only [id]; linarith

/-! ### `Ỹ` (`lem:pll-wall` (e)) -/

lemma SigmaV_hasDerivAt (y : ℝ) : HasDerivAt (SigmaV P) (deriv (SigmaV P) y) y :=
  ((contDiff_SigmaV P).differentiable (by simp) y).hasDerivAt

theorem SigmaV_Ytilde (v : ℝ) : SigmaV P (Ytilde P v) = v :=
  apply_invR' (SigmaV_continuous P) (SigmaV_strictMono P) (SigmaV_tendsto_atTop P)
    (SigmaV_tendsto_atBot P) v

theorem Ytilde_SigmaV (y : ℝ) : Ytilde P (SigmaV P y) = y :=
  invR_apply' (SigmaV_strictMono P) y

theorem Vtilde_Ytilde (v : ℝ) : Vtilde P (Ytilde P v) = v ^ 2 := by
  rw [← SigmaV_sq, SigmaV_Ytilde]

theorem Ytilde_strictMono : StrictMono (Ytilde P) :=
  invR_strictMono (SigmaV_continuous P) (SigmaV_strictMono P) (SigmaV_tendsto_atTop P)
    (SigmaV_tendsto_atBot P)

theorem Ytilde_smooth : ContDiff ℝ ∞ (Ytilde P) :=
  invR_contDiff (SigmaV_continuous P) (SigmaV_strictMono P) (SigmaV_tendsto_atTop P)
    (SigmaV_tendsto_atBot P) (SigmaV_hasDerivAt P) (SigmaV_deriv_pos P) (contDiff_SigmaV P)

theorem Ytilde_deriv_pos (v : ℝ) : 0 < deriv (Ytilde P) v :=
  deriv_invR_pos (SigmaV_continuous P) (SigmaV_strictMono P) (SigmaV_tendsto_atTop P)
    (SigmaV_tendsto_atBot P) (SigmaV_hasDerivAt P) (SigmaV_deriv_pos P) v

lemma sqrt_two_div_eq : √(2 / P.eq_) = (√(P.eq_ / 2))⁻¹ := by
  rw [← Real.sqrt_inv, inv_div]

/-- `Ỹ(v) = b₀ v` for `|v| ≤ v_ε`, `b₀ = √(2/e)`. -/
theorem Ytilde_linear {v : ℝ} (hv : |v| ≤ vEps P) : Ytilde P v = √(2 / P.eq_) * v := by
  have hc : 0 < √(P.eq_ / 2) := Real.sqrt_pos.mpr (by linarith [P.eq_pos])
  unfold Ytilde
  rw [invR_linear (SigmaV_strictMono P) hc (fun y hy => SigmaV_linear P hy) hv,
    sqrt_two_div_eq, div_eq_inv_mul]

/-- `|Ỹ(v)| ≤ b₀ |v|`. -/
theorem abs_Ytilde_le (v : ℝ) : |Ytilde P v| ≤ √(2 / P.eq_) * |v| := by
  have hc : 0 < √(P.eq_ / 2) := Real.sqrt_pos.mpr (by linarith [P.eq_pos])
  have := abs_SigmaV_ge P (Ytilde P v)
  rw [SigmaV_Ytilde] at this
  rw [sqrt_two_div_eq, ← div_eq_inv_mul, le_div_iff₀ hc]
  linarith

end SymplecticPacking.Inner
