import Mathlib
import SymplecticPacking.Inner.AreaBound

/-!
# The inner map and the comparison

`sec:pll`, the inner map and the comparison: `def:pll-inner-map`, `prop:pll-inner-map`, `def:pll-chart`, `lem:pll-physical-chart`, `prop:pll-comparison`.

`f = F_mor ∘ T⁻¹ ∘ D` for the Morse density `J = X̃'(u) Ỹ'(v)` (as the constant family
`JmorF P`, evaluated at the parameter `s = 0`), and the physical chart
`C(x, y) = -√((p* + x)/π) e^{2πiy}`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### The Morse density satisfies the normalisation hypotheses -/

/-- The Morse density (as a constant family on `s ∈ (-1, 1)`) is flat: `J = j₀` on `|w| ≤ ρ_T`. -/
theorem JmorF_flat : FlatDensity (JmorF P) (-1) 1 (j0 P) (rhoT P) where
  smooth := JmorF_smooth P
  pos := fun _ _ w => Jmor_pos P w
  flat := fun _ _ _ hw => Jmor_const P hw
  j_pos := j0_pos P
  ρ₀_pos := rhoT_pos P
  tendsto := fun s _ => Acal_tendsto P s

lemma zero_mem_Ioo : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-! ### The inner map (`def:pll-inner-map`) -/

/-- **`def:pll-inner-map`.** `f = F_mor ∘ T⁻¹ ∘ D` for `J = X̃'Ỹ'`. -/
def finner (z : ℂ) : ℂ := Fmor P (TrotInv (JmorF P) 0 (Darea (JmorF P) 0 z))

/-- **`prop:pll-inner-map`.** If `f(z) = x + iy` then `R̃(x) + Ṽ(y) = E(π|z|²)`. -/
theorem finner_level (z : ℂ) :
    Rtilde P (finner P z).re + Vtilde P (finner P z).im = Einv (JmorF P) 0 (π * ‖z‖ ^ 2) := by
  rw [finner, Fmor_level, normalize_circle (JmorF_flat P) zero_mem_Ioo]

/-! ### `f` is linear near the origin (`prop:pll-inner-map`) -/

/-! ### The physical chart (`def:pll-chart`, `lem:pll-physical-chart`) -/

/-- **`def:pll-chart`.** `C(x, y) = -√((p* + x)/π) e^{2πiy}`. -/
def chartC (w : ℂ) : ℂ :=
  -((√((P.pstar + w.re) / π) : ℝ) * Complex.exp ((2 * π * w.im : ℝ) * I))

/-- The chart domain `{p* + x > 0, |y| < 1/2}`. -/
def chartDom : Set ℂ := {w | 0 < P.pstar + w.re ∧ |w.im| < 1 / 2}

/-- **`lem:pll-physical-chart`.** `p(C(x, y)) = π|C(x, y)|² = p* + x`. -/
theorem chartC_moment {w : ℂ} (hw : 0 ≤ P.pstar + w.re) :
    π * ‖chartC P w‖ ^ 2 = P.pstar + w.re := by
  rw [chartC, norm_neg, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg hw Real.pi_pos.le)]
  field_simp

/-- **`lem:pll-physical-chart`.** `det DC = 1` on the chart domain (`C^*(dq∧dp) = dx∧dy`). -/
theorem chartC_det {w : ℂ} (hw : 0 < P.pstar + w.re) :
    LinearMap.det (fderiv ℝ (chartC P) w : ℂ →ₗ[ℝ] ℂ) = 1 := by
  set q : ℝ → ℝ := fun x => (P.pstar + x) / π
  have hq : HasDerivAt q (1 / π) w.re := by
    simpa [q] using ((hasDerivAt_id w.re).const_add P.pstar).div_const π
  have hqpos : 0 < q w.re := div_pos hw Real.pi_pos
  set ρ := √(q w.re)
  have hρ : 0 < ρ := Real.sqrt_pos.2 hqpos
  have hs : HasDerivAt (fun x => √(q x)) (1 / π / (2 * ρ)) w.re := hq.sqrt hqpos.ne'
  have h1 : HasFDerivAt (fun w : ℂ => ((√(q w.re) : ℝ) : ℂ))
      (ofRealCLM.comp ((1 / π / (2 * ρ)) • reCLM)) w := by
    refine (ofRealCLM.hasFDerivAt.comp w (hs.hasFDerivAt.comp w reCLM.hasFDerivAt)).congr_fderiv ?_
    ext1 z; simp; ring
  have hg : HasFDerivAt (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ) * I)
      ((ofRealCLM.comp ((2 * π) • imCLM)).smulRight I) w := by
    have : HasFDerivAt (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ))
        (ofRealCLM.comp ((2 * π) • imCLM)) w :=
      (ofRealCLM.hasFDerivAt.comp w (((2 * π) • imCLM).hasFDerivAt)).congr_fderiv (by ext1 z; simp)
    refine (this.mul_const I).congr_fderiv ?_
    ext1 z; simp; ring
  have h2 := hg.cexp
  have hfun : chartC P = fun w : ℂ =>
      -(((√(q w.re) : ℝ) : ℂ) * Complex.exp (((2 * π * w.im : ℝ) : ℂ) * I)) := rfl
  have h3 : HasFDerivAt (fun w : ℂ =>
      -(((√(q w.re) : ℝ) : ℂ) * Complex.exp (((2 * π * w.im : ℝ) : ℂ) * I))) _ w :=
    (h1.mul h2).neg
  rw [hfun, h3.fderiv, det_eq_re_im]
  set θ := 2 * π * w.im
  have hc := Complex.exp_ofReal_mul_I_re θ
  have hsn := Complex.exp_ofReal_mul_I_im θ
  simp [hc, hsn, -Complex.ofReal_div]
  have hρ2 : ρ * ρ = q w.re := Real.mul_self_sqrt hqpos.le
  have hcs := Real.cos_sq_add_sin_sq θ
  have hpi := Real.pi_pos.ne'
  field_simp
  rw [hcs, mul_one]

/-- **`lem:pll-physical-chart`.** `C` is injective on the chart domain. -/
theorem chartC_injOn : InjOn (chartC P) (chartDom P) := by
  intro w₁ hw₁ w₂ hw₂ h
  have hm1 := chartC_moment P hw₁.1.le
  have hm2 := chartC_moment P hw₂.1.le
  rw [h] at hm1
  have hre : w₁.re = w₂.re := by linarith
  have hρ : 0 < √((P.pstar + w₁.re) / π) := Real.sqrt_pos.2 (div_pos hw₁.1 Real.pi_pos)
  have he : Complex.exp (((2 * π * w₁.im : ℝ) : ℂ) * I) =
      Complex.exp (((2 * π * w₂.im : ℝ) : ℂ) * I) := by
    have h' := h
    simp only [chartC, neg_inj, hre] at h'
    rw [← hre] at h'
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne') h'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hn' : w₁.im = w₂.im + n := by
    have := congrArg Complex.im hn
    simp at this
    have hpi := Real.pi_pos
    nlinarith
  have hlt : |(n : ℝ)| < 1 := by
    have h1 := abs_lt.mp hw₁.2
    have h2 := abs_lt.mp hw₂.2
    rw [abs_lt]; constructor <;> linarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hlt
    rw [abs_lt] at this; omega
  rw [hn0, Int.cast_zero, add_zero] at hn'
  exact Complex.ext hre hn'

/-! ### The comparison (`prop:pll-comparison`) -/

/-- `E(I) ≤ I + d₀` for `I ≥ 0` (from `𝓐(E) ≥ E - d₀`). -/
theorem Einv_le_add_d0 {I : ℝ} (hI : 0 ≤ I) : Einv (JmorF P) 0 I ≤ I + P.d0 := by
  have hJ := JmorF_flat P
  have hge := Acal_ge P 0 (add_nonneg hI P.d0_nonneg)
  rw [add_sub_cancel_right] at hge
  rw [← (Acal_strictMono hJ zero_mem_Ioo).le_iff_le, Acal_Einv hJ zero_mem_Ioo]
  exact hge

/-- **`prop:pll-comparison`, (5).** If `f(z)` has `p* + x ≥ 0` (in particular if it lies in
the chart domain), then `Rcal(p(C f(z))) ≤ I + 2δ' + μ < I + 13e/24`, `I = π|z|²`. -/
theorem comparison_five (z : ℂ) (hdom : 0 ≤ P.pstar + (finner P z).re) :
    P.Rcal (π * ‖chartC P (finner P z)‖ ^ 2) ≤
        π * ‖z‖ ^ 2 + (2 * deltaPrime P + muV P) ∧
      P.Rcal (π * ‖chartC P (finner P z)‖ ^ 2) < π * ‖z‖ ^ 2 + 13 * P.eq_ / 24 := by
  rw [chartC_moment P hdom]
  set x := (finner P z).re
  have hc := (abs_le.mp (Rtilde_Rcal_close P (P.pstar + x))).1
  rw [show P.pstar + x - P.pstar = x by ring] at hc
  have hlev := finner_level P z
  have hV := Vtilde_nonneg P (finner P z).im
  have hE := Einv_le_add_d0 P (I := π * ‖z‖ ^ 2) (by positivity)
  have h1 : P.Rcal (P.pstar + x) ≤ π * ‖z‖ ^ 2 + (2 * deltaPrime P + muV P) := by
    unfold Params.d0 at hE; linarith
  exact ⟨h1, by linarith [P.two_deltaPrime_add_muV_lt]⟩

end SymplecticPacking.Inner
