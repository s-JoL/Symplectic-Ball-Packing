import Mathlib
import SymplecticPacking.Qhat.Bounds

/-!
# The charts `C_λ` and the common inner family

`sec:pln-charts`: the charts `C_λ` (`def:pln-charts`, `lem:pln-chart-lambda`), the clock `λ(s)`
(`def:pln-charts`) and the common inner family `q^in_s = C_{λ(s)} ∘ f_s`
(`prop:pln-inner-family`).

**`C_λ` is defined by a closed formula** equivalent to the paper's integral (7): writing
`w = u + iv`, `θ = 2πλv`, `ρ = √((p* + λu)/π)` and `g(ζ) = (e^ζ - 1)/ζ` (`g = dslope exp 0`),
`C_λ(w) = b - v · 2π r_b i g(iθ) - u · e^{iθ}/(π(r_b + ρ))`
(the angular/radial split of the appendix). `Clam_eq` is the quotient form
`b + (C(λw) - b)/λ` for `λ > 0`, and `Clam_zero_eq` the affine form `b + DC(0) w` at `λ = 0`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### The point `b` and the function `g` -/

/-- `r_b = √(p*/π)`. -/
def rb : ℝ := √(P.pstar / π)

/-- `b = (-r_b, 0) = C(0)`. -/
def bpt : ℂ := -(rb P : ℂ)

lemma pstar_pos : 0 < P.pstar := P.pstar_mem.1

lemma rb_pos : 0 < rb P := Real.sqrt_pos.2 (div_pos (pstar_pos P) Real.pi_pos)

lemma rb_sq : rb P ^ 2 = P.pstar / π :=
  Real.sq_sqrt (div_nonneg (pstar_pos P).le Real.pi_pos.le)

lemma pi_mul_rb : π * rb P = √(π * P.pstar) := by
  have h1 : (0 : ℝ) ≤ π * rb P := by have := rb_pos P; positivity
  rw [← Real.sqrt_sq h1, mul_pow, rb_sq]
  congr 1; field_simp

/-- `g = dslope exp 0`, i.e. `g(ζ) = (e^ζ - 1)/ζ`, `g(0) = 1`. -/
def gexp : ℂ → ℂ := dslope Complex.exp 0

lemma gexp_mul (ζ : ℂ) : ζ * gexp ζ = Complex.exp ζ - 1 := by
  have := sub_smul_dslope Complex.exp 0 ζ
  simpa [gexp] using this

lemma gexp_zero : gexp 0 = 1 := by
  simp [gexp, dslope_same, Complex.deriv_exp]

lemma gexp_contDiff : ContDiff ℝ ∞ gexp := by
  have h : DifferentiableOn ℂ gexp univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr Complex.differentiable_exp.differentiableOn
  exact ((differentiableOn_univ.mp h).contDiff (n := ∞)).restrict_scalars ℝ

lemma norm_gexp_le (θ : ℝ) : ‖gexp ((θ : ℂ) * I)‖ ≤ 1 := by
  rcases eq_or_ne θ 0 with h | h
  · simp [h, gexp_zero]
  have h1 := gexp_mul ((θ : ℂ) * I)
  have h2 : ‖(θ : ℂ) * I‖ * ‖gexp ((θ : ℂ) * I)‖ ≤ ‖(θ : ℂ) * I‖ := by
    rw [← norm_mul, h1, mul_comm (θ : ℂ) I]
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    simpa [Real.norm_eq_abs] using this
  have hpos : 0 < ‖(θ : ℂ) * I‖ := by simp [h]
  nlinarith [norm_nonneg (gexp ((θ : ℂ) * I))]

/-! ### The charts `C_λ` (`def:pln-charts`) -/

/-- Angular factor `2π r_b i g(2πiλv)`. -/
def Hy (lam : ℝ) (w : ℂ) : ℂ :=
  ((2 * π * rb P : ℝ) : ℂ) * I * gexp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- Radial factor `e^{2πiλv}/(π(r_b + √((p* + λu)/π)))`. -/
def Hx (lam : ℝ) (w : ℂ) : ℂ :=
  (((π * (rb P + √((P.pstar + lam * w.re) / π)))⁻¹ : ℝ) : ℂ) *
    Complex.exp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- **`def:pln-charts`.** The rescaled chart
`C_λ(w) = b + ∫₀¹ DC(tλw) w dt`, in the closed form `b - v H_y - u H_x`. -/
def Clam (lam : ℝ) (w : ℂ) : ℂ := bpt P - (w.im : ℂ) * Hy P lam w - (w.re : ℂ) * Hx P lam w

/-- `DC(0) = diag(-1/(2π r_b), -2π r_b)`. -/
def DC0 : ℂ →L[ℝ] ℂ :=
  -(((2 * π * rb P : ℝ) : ℂ) * I) • (ofRealCLM.comp imCLM) -
    (((2 * π * rb P)⁻¹ : ℝ) : ℂ) • (ofRealCLM.comp reCLM)

lemma DC0_apply (w : ℂ) :
    DC0 P w = -(((2 * π * rb P : ℝ) : ℂ) * I) * w.im - (((2 * π * rb P)⁻¹ : ℝ) : ℂ) * w.re := by
  simp [DC0]

lemma DC0_re (w : ℂ) : (DC0 P w).re = -(2 * π * rb P)⁻¹ * w.re := by
  rw [DC0_apply]; simp

lemma DC0_im (w : ℂ) : (DC0 P w).im = -(2 * π * rb P) * w.im := by
  rw [DC0_apply]; simp

lemma DC0_det : LinearMap.det (DC0 P : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [Inner.det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe, DC0_re, DC0_im]
  have := rb_pos P; have := Real.pi_pos
  simp; field_simp

lemma DC0_injective : Function.Injective (DC0 P) :=
  Inner.injective_of_det_ne_zero _ (by rw [DC0_det]; norm_num)

/-- `C_0(w) = b + DC(0) w`. -/
theorem Clam_zero_eq (w : ℂ) : Clam P 0 w = bpt P + DC0 P w := by
  have hrb : √(P.pstar / π) = rb P := rfl
  simp only [Clam, Hy, Hx, DC0_apply, zero_mul, mul_zero, Complex.ofReal_zero, gexp_zero,
    Complex.exp_zero, mul_one, add_zero, hrb]
  have := rb_pos P; have := Real.pi_pos
  rw [show (π * (rb P + rb P))⁻¹ = (2 * π * rb P)⁻¹ by ring_nf]
  ring

lemma smul_re' (lam : ℝ) (w : ℂ) : (lam • w).re = lam * w.re := by simp
lemma smul_im' (lam : ℝ) (w : ℂ) : (lam • w).im = lam * w.im := by simp

/-- **`lem:pln-chart-lambda`.** For `λ > 0`, `C_λ(w) = b + (C(λw) - b)/λ`. -/
theorem Clam_eq {lam : ℝ} (hlam : 0 < lam) {w : ℂ} (hw : 0 ≤ P.pstar + lam * w.re) :
    Clam P lam w = bpt P + (Inner.chartC P (lam • w) - bpt P) / lam := by
  set u := w.re
  set v := w.im
  set ρ := √((P.pstar + lam * u) / π)
  set θ := 2 * π * lam * v
  set E := Complex.exp ((θ : ℂ) * I)
  have hrb := rb_pos P
  have hpi := Real.pi_pos
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (P.pstar + lam * u) / π := Real.sq_sqrt (div_nonneg hw hpi.le)
  have hrbsq := rb_sq P
  -- radial identity `λu/(π(r_b + ρ)) = ρ - r_b`
  have hrad : lam * u * (π * (rb P + ρ))⁻¹ = ρ - rb P := by
    have hden : 0 < π * (rb P + ρ) := by positivity
    rw [← div_eq_mul_inv, div_eq_iff hden.ne']
    have : (ρ - rb P) * (π * (rb P + ρ)) = π * (ρ ^ 2 - rb P ^ 2) := by ring
    rw [this, hρsq, hrbsq]; field_simp; ring
  -- angular identity `λ v · 2π r_b i g(iθ) = r_b (e^{iθ} - 1)`
  have hang : (lam : ℂ) * (v : ℂ) * (((2 * π * rb P : ℝ) : ℂ) * I * gexp ((θ : ℂ) * I)) =
      (rb P : ℂ) * (E - 1) := by
    rw [← gexp_mul]; simp only [θ]; push_cast; ring
  have hC : Inner.chartC P (lam • w) = -((ρ : ℂ) * E) := by
    have h1 : 2 * π * (lam • w).im = θ := by rw [smul_im']; simp only [θ, v]; ring
    have h2 : P.pstar + (lam • w).re = P.pstar + lam * u := by rw [smul_re']
    rw [Inner.chartC, h1, h2]
  have hlam' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  rw [hC, ← sub_eq_iff_eq_add', eq_div_iff hlam']
  have hrad' : (lam : ℂ) * (u : ℂ) * (((π * (rb P + ρ))⁻¹ : ℝ) : ℂ) = (ρ : ℂ) - (rb P : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hrad
    push_cast at this ⊢
    linear_combination this
  simp only [Clam, Hy, Hx, bpt]
  rw [show (2 * π * lam * w.im) = θ from rfl]
  linear_combination (-1 : ℂ) * hang - E * hrad'

/-! ### Smoothness, determinant and injectivity of `C_λ` (`lem:pln-chart-lambda`) -/

lemma Hy_contDiff : ContDiff ℝ ∞ (fun q : ℝ × ℂ => Hy P q.1 q.2) := by
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.im) := imCLM.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (((2 * π * q.1 * q.2.im : ℝ) : ℂ) * I)) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_fst).mul him)).mul contDiff_const
  exact contDiff_const.mul (gexp_contDiff.comp hθ)

lemma Hx_contDiffAt {q : ℝ × ℂ} (hq : 0 < P.pstar + q.1 * q.2.re) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Hx P q.1 q.2) q := by
  have hre : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.re) := reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.im) := imCLM.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (((2 * π * q.1 * q.2.im : ℝ) : ℂ) * I)) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_fst).mul him)).mul contDiff_const
  have hpi := Real.pi_pos
  have harg : 0 < (P.pstar + q.1 * q.2.re) / π := div_pos hq hpi
  have hsq : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => √((P.pstar + q.1 * q.2.re) / π)) q :=
    (Real.contDiffAt_sqrt harg.ne').comp q
      ((contDiff_const.add (contDiff_fst.mul hre)).div_const π).contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => (π * (rb P + √((P.pstar + q.1 * q.2.re) / π)))⁻¹) q :=
    (contDiffAt_const.mul (contDiffAt_const.add hsq)).inv
      (by have := rb_pos P; have := Real.sqrt_nonneg ((P.pstar + q.1 * q.2.re) / π); positivity)
  exact (ofRealCLM.contDiff.contDiffAt.comp q hden).mul
    ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp q hθ.contDiffAt)

/-- `(λ, w) ↦ C_λ(w)` is `C^∞` at every point with `p* + λ Re w > 0`. -/
theorem Clam_contDiffAt {q : ℝ × ℂ} (hq : 0 < P.pstar + q.1 * q.2.re) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Clam P q.1 q.2) q := by
  have hre : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (q.2.re : ℂ)) :=
    ofRealCLM.contDiff.comp (reCLM.contDiff.comp contDiff_snd)
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (q.2.im : ℂ)) :=
    ofRealCLM.contDiff.comp (imCLM.contDiff.comp contDiff_snd)
  unfold Clam
  exact (contDiffAt_const.sub (him.contDiffAt.mul (Hy_contDiff P).contDiffAt)).sub
    (hre.contDiffAt.mul (Hx_contDiffAt P hq))

/-- The domain `{(λ, w) : p* + λ Re w > 0}` (contains `{λ w ∈ 𝒰}`). -/
def ClamDom : Set (ℝ × ℂ) := {q | 0 < P.pstar + q.1 * q.2.re}

/-- **`lem:pln-chart-lambda`.** `(λ, w) ↦ C_λ(w)` is `C^∞` on `{p* + λ Re w > 0}`. -/
theorem Clam_smooth : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => Clam P q.1 q.2) (ClamDom P) :=
  fun _ hq => (Clam_contDiffAt P hq).contDiffWithinAt

lemma Clam_slice_contDiffAt {lam : ℝ} {w : ℂ} (hw : 0 < P.pstar + lam * w.re) :
    ContDiffAt ℝ ∞ (Clam P lam) w :=
  (Clam_contDiffAt P (q := (lam, w)) hw).comp w (contDiffAt_const.prodMk contDiffAt_id)

lemma chartC_differentiableAt {w : ℂ} (hw : 0 < P.pstar + w.re) :
    DifferentiableAt ℝ (Inner.chartC P) w := by
  have harg : 0 < (P.pstar + w.re) / π := div_pos hw Real.pi_pos
  have hre : DifferentiableAt ℝ (fun w : ℂ => (P.pstar + w.re) / π) w := by fun_prop
  have h1 : DifferentiableAt ℝ (fun w : ℂ => √((P.pstar + w.re) / π)) w := hre.sqrt harg.ne'
  have h2 : DifferentiableAt ℝ (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ) * I) w := by fun_prop
  exact ((ofRealCLM.differentiableAt.comp w h1).mul h2.cexp).neg

/-- For `λ > 0`, `DC_λ(w) = DC(λw)`. -/
theorem Clam_fderiv {lam : ℝ} (hlam : 0 < lam) {w : ℂ} (hw : 0 < P.pstar + lam * w.re) :
    fderiv ℝ (Clam P lam) w = fderiv ℝ (Inner.chartC P) (lam • w) := by
  have hO : IsOpen {w' : ℂ | 0 < P.pstar + lam * w'.re} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_const.mul Complex.continuous_re))
  have hev : Clam P lam =ᶠ[𝓝 w] fun w' => bpt P + (Inner.chartC P (lam • w') - bpt P) / lam := by
    filter_upwards [hO.mem_nhds hw] with w' hw'
    exact Clam_eq P hlam hw'.le
  have hD := (chartC_differentiableAt P (w := lam • w) (by rw [smul_re']; exact hw)).hasFDerivAt
  have hcomp : HasFDerivAt (fun w' : ℂ => Inner.chartC P (lam • w'))
      ((fderiv ℝ (Inner.chartC P) (lam • w)).comp (lam • ContinuousLinearMap.id ℝ ℂ)) w :=
    hD.comp w ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul lam)
  have hfull : HasFDerivAt (fun w' => bpt P + (Inner.chartC P (lam • w') - bpt P) / lam)
      (fderiv ℝ (Inner.chartC P) (lam • w)) w := by
    have := ((hcomp.sub_const (bpt P)).mul_const ((lam : ℂ)⁻¹)).const_add (bpt P)
    refine this.congr_fderiv ?_
    ext1 x
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul]
    rw [Complex.real_smul, smul_eq_mul]
    field_simp
  rw [hev.fderiv_eq, hfull.fderiv]

/-- **`lem:pln-chart-lambda`.** `det DC_λ = 1` (for `λ ≥ 0`, `p* + λ Re w > 0`). -/
theorem Clam_det {lam : ℝ} (hlam : 0 ≤ lam) {w : ℂ} (hw : 0 < P.pstar + lam * w.re) :
    LinearMap.det (fderiv ℝ (Clam P lam) w : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    have hfun : Clam P 0 = fun w => bpt P + DC0 P w := funext (Clam_zero_eq P)
    rw [hfun, fderiv_const_add, ContinuousLinearMap.fderiv, DC0_det]
  · rw [Clam_fderiv P h hw]
    exact Inner.chartC_det P (by rw [smul_re']; exact hw)

/-- **`lem:pln-chart-lambda`.** `C_λ` is injective on `λ⁻¹ 𝒰` (on the whole plane if `λ = 0`). -/
theorem Clam_injOn {lam : ℝ} (hlam : 0 ≤ lam) :
    InjOn (Clam P lam) {w | lam • w ∈ Inner.chartDom P} := by
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    intro w₁ _ w₂ _ hw
    rw [Clam_zero_eq, Clam_zero_eq, add_right_inj] at hw
    exact DC0_injective P hw
  · intro w₁ hw₁ w₂ hw₂ hw
    have h1 : 0 ≤ P.pstar + lam * w₁.re := by have := hw₁.1; rw [smul_re'] at this; linarith
    have h2 : 0 ≤ P.pstar + lam * w₂.re := by have := hw₂.1; rw [smul_re'] at this; linarith
    rw [Clam_eq P h h1, Clam_eq P h h2, add_right_inj] at hw
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
    have hC : Inner.chartC P (lam • w₁) = Inner.chartC P (lam • w₂) := by
      have := (div_left_inj' hl).mp hw
      exact sub_left_inj.mp this
    have := Inner.chartC_injOn P hw₁ hw₂ hC
    exact smul_right_injective ℂ h.ne' this

/-! ### The clock (`def:pln-charts`) -/

/-- `λ₀ = min(1/2, p*/(2X̄), 1/(4Ȳ))`. -/
def lambda0 : ℝ := min (min (1 / 2) (P.pstar / (2 * Xbar P))) (1 / (4 * Ybar P))

/-- `λ(s) = λ₀ S(2s) + (1 - λ₀) S((s - 1 + δ_s)/δ_s)`. -/
def lam (s : ℝ) : ℝ :=
  lambda0 P * Real.smoothTransition (2 * s) +
    (1 - lambda0 P) * Real.smoothTransition ((s - 1 + delta_s P) / delta_s P)

lemma lambda0_pos : 0 < lambda0 P :=
  lt_min (lt_min (by norm_num) (div_pos (pstar_pos P) (by linarith [Xbar_pos P])))
    (div_pos one_pos (by linarith [Ybar_pos P]))

lemma lambda0_le_half : lambda0 P ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)

lemma lambda0_mul_Xbar : lambda0 P * Xbar P ≤ P.pstar / 2 := by
  have hX := Xbar_pos P
  have : lambda0 P ≤ P.pstar / (2 * Xbar P) := (min_le_left _ _).trans (min_le_right _ _)
  rw [le_div_iff₀ (by linarith)] at this; linarith

lemma lambda0_mul_Ybar : lambda0 P * Ybar P ≤ 1 / 4 := by
  have : lambda0 P ≤ 1 / (4 * Ybar P) := min_le_right _ _
  have hY := Ybar_pos P
  rw [le_div_iff₀ (by linarith)] at this; linarith

lemma lam_contDiff : ContDiff ℝ ∞ (lam P) := by
  unfold lam
  exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const |>.add contDiff_const).div_const _)))

lemma lam_nonneg (s : ℝ) : 0 ≤ lam P s := by
  have := lambda0_pos P; have := lambda0_le_half P
  have := Real.smoothTransition.nonneg (2 * s)
  have := Real.smoothTransition.nonneg ((s - 1 + delta_s P) / delta_s P)
  unfold lam; nlinarith

lemma lam_le_one (s : ℝ) : lam P s ≤ 1 := by
  have := lambda0_pos P; have := lambda0_le_half P
  have := Real.smoothTransition.le_one (2 * s)
  have := Real.smoothTransition.le_one ((s - 1 + delta_s P) / delta_s P)
  unfold lam; nlinarith

/-- Early range: `λ(s) = λ₀ S(2s) ≤ λ₀` for `s ≤ 1 - δ_s`. -/
lemma lam_early {s : ℝ} (hs : s ≤ 1 - delta_s P) : lam P s ≤ lambda0 P := by
  have hδ := (delta_s_pos P).1
  have h0 : Real.smoothTransition ((s - 1 + delta_s P) / delta_s P) = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have := Real.smoothTransition.le_one (2 * s)
  have := lambda0_pos P
  unfold lam; rw [h0]; nlinarith

lemma lam_zero : lam P 0 = 0 := by
  have hδ := delta_s_pos P
  unfold lam
  rw [mul_zero, Real.smoothTransition.zero_of_nonpos le_rfl,
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.1.le)]
  ring

lemma lam_one : lam P 1 = 1 := by
  have hδ := (delta_s_pos P).1
  unfold lam
  rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2 * 1),
    Real.smoothTransition.one_of_one_le (by rw [show (1 - 1 + delta_s P) / delta_s P = 1 by
      field_simp; ring])]
  ring

/-! ### Radial range constants (`def:pll-path-constants`) -/

/-- `P_min = min(p*, ΔP)/2`. -/
def Pmin : ℝ := min P.pstar (DeltaP P) / 2

/-- `P_max = max(3p*/2, h)`. -/
def Pmax : ℝ := max (3 * P.pstar / 2) P.h

lemma Pmin_pos : 0 < Pmin P := by
  have := lt_min (pstar_pos P) (DeltaP_pos P); unfold Pmin; linarith

/-! ### The common inner family (`prop:pln-inner-family`) -/

/-- The common source disk `D(p†) = {π|z|² < p†}`. -/
def srcDisk : Set ℂ := {z | π * ‖z‖ ^ 2 < pdag P}

/-- **`prop:pln-inner-family`.** `q^in_s = C_{λ(s)} ∘ f_s`. -/
def qinner (s : ℝ) (z : ℂ) : ℂ := Clam P (lam P s) (fs P s z)

/-- **`prop:pln-inner-family`, radial range.** For `s, t ∈ [0, 1]` and `z ∈ D̄(p†)` the point
`tλ(s)f_s(z)` has radial coordinate `p* + tλ(s)X_s(u) ∈ [P_min, P_max]` and angle
`|tλ(s)Y_s(v)| < 1/2`. -/
theorem qinner_radial {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Pmin P ≤ P.pstar + t * lam P s * (fs P s z).re ∧
      P.pstar + t * lam P s * (fs P s z).re ≤ Pmax P ∧
      |t * lam P s * (fs P s z).im| < 1 / 2 := by
  set x := (fs P s z).re
  set y := (fs P s z).im
  set τ := t * lam P s
  have hl0 := lam_nonneg P s
  have hl1 := lam_le_one P s
  have hτ0 : 0 ≤ τ := mul_nonneg ht.1 hl0
  have hτ1 : τ ≤ 1 := by nlinarith [ht.1, ht.2]
  have hp := pstar_pos P
  have hPmin1 : Pmin P ≤ P.pstar / 2 := by
    have := min_le_left P.pstar (DeltaP P); unfold Pmin; linarith
  have hPmin2 : Pmin P ≤ DeltaP P / 2 := by
    have := min_le_right P.pstar (DeltaP P); unfold Pmin; linarith
  have hPmax1 : 3 * P.pstar / 2 ≤ Pmax P := le_max_left _ _
  have hPmax2 : P.h ≤ Pmax P := le_max_right _ _
  have hτy : |τ * y| = τ * |y| := by rw [abs_mul, abs_of_nonneg hτ0]
  have hτx : |τ * x| = τ * |x| := by rw [abs_mul, abs_of_nonneg hτ0]
  rcases le_or_gt s (1 - delta_s P) with hearly | hlate
  · -- early range: `λ ≤ λ₀`
    have hlam := lam_early P hearly
    have hX := Xs_le_Xbar P hs hz
    have hY := Ys_le_Ybar P hs hz
    have hτl : τ ≤ lambda0 P := by
      have := mul_le_mul ht.2 hlam hl0 zero_le_one; simp only [τ]; linarith
    have h1 : τ * |x| ≤ P.pstar / 2 :=
      (mul_le_mul hτl hX (abs_nonneg _) (lambda0_pos P).le).trans (lambda0_mul_Xbar P)
    have h2 : τ * |y| ≤ 1 / 4 :=
      (mul_le_mul hτl hY (abs_nonneg _) (lambda0_pos P).le).trans (lambda0_mul_Ybar P)
    have hx := abs_le.mp (show |τ * x| ≤ P.pstar / 2 by rw [hτx]; exact h1)
    refine ⟨by linarith [hx.1], by linarith [hx.2], ?_⟩
    rw [hτy]; linarith
  · -- late range
    obtain ⟨-, hm1, hm2, hm3⟩ := late_margin P hs hlate.le hz
    have hDy := Deltay_pos P
    have hq1 : Pmin P ≤ P.pstar + x := by linarith
    have hq2 : P.pstar + x ≤ Pmax P := by have := DeltaP_pos P; linarith
    have hconv : P.pstar + τ * x = (1 - τ) * P.pstar + τ * (P.pstar + x) := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hconv]; nlinarith
    · rw [hconv]; nlinarith
    · rw [hτy]
      have : τ * |y| ≤ |y| := by nlinarith [abs_nonneg y]
      linarith

/-- `λ(s) f_s(z)` lies in the chart domain `𝒰`. -/
theorem qinner_dom {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    lam P s • fs P s z ∈ Inner.chartDom P ∧ 0 < P.pstar + lam P s * (fs P s z).re := by
  have h := qinner_radial P hs hz (t := 1) ⟨zero_le_one, le_rfl⟩
  simp only [one_mul] at h
  have hP := Pmin_pos P
  refine ⟨⟨by rw [smul_re']; linarith [h.1], by rw [smul_im']; exact h.2.2⟩, by linarith [h.1]⟩

lemma lam_fs_mem_ClamDom {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    (lam P s, fs P s z) ∈ ClamDom P := (qinner_dom P hs hz).2

/-- **`prop:pln-inner-family`.** `(s, z) ↦ q^in_s(z)` is `C^∞` on `[0, 1] × D(p†)`. -/
theorem qinner_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => qinner P p.1 p.2) (Icc 0 1 ×ˢ srcDisk P) := by
  have hin : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (lam P p.1, fs P p.1 p.2)) (Icc 0 1 ×ˢ srcDisk P) :=
    ((lam_contDiff P).comp contDiff_fst).contDiffOn.prodMk
      ((fs_smooth P).mono (prod_mono subset_rfl (subset_univ _)))
  exact (Clam_smooth P).comp hin fun p hp => lam_fs_mem_ClamDom P hp.1 (le_of_lt hp.2)

/-- **`prop:pln-inner-family`.** Each `q^in_s` is symplectic on `D̄(p†)`. -/
theorem qinner_symplectic {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    LinearMap.det (fderiv ℝ (qinner P s) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hdom := (qinner_dom P hs hz).2
  have hC := (Clam_slice_contDiffAt P hdom).differentiableAt (by simp)
  have hf := (fs_contDiff P hs).differentiable (by simp) z
  have hc : qinner P s = Clam P (lam P s) ∘ fs P s := rfl
  rw [hc, fderiv_comp z hC hf, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    Clam_det P (lam_nonneg P s) hdom, fs_symplectic P hs, one_mul]

/-- **`prop:pln-inner-family`.** Each `q^in_s` is injective on `D(p†)`. -/
theorem qinner_injOn {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : InjOn (qinner P s) (srcDisk P) := by
  intro z₁ hz₁ z₂ hz₂ h
  have h1 := (qinner_dom P hs (le_of_lt hz₁)).1
  have h2 := (qinner_dom P hs (le_of_lt hz₂)).1
  exact fs_injective P hs (Clam_injOn P (lam_nonneg P s) h1 h2 h)

/-- `𝐀₀ = DC(0) 𝐋`. -/
def A0 : ℂ →L[ℝ] ℂ := (DC0 P).comp (Lclm P)

/-- `𝐀₀ = diag(-c_x/(2π r_b), -2π r_b c_y)`. -/
def A11 : ℝ := -(Inner.cx P / (2 * π * rb P))
def A22 : ℝ := -(2 * π * rb P * Inner.cy P)

lemma Lmap_re (z : ℂ) : (Lmap P z).re = Inner.cx P * z.re := by simp [Lmap]
lemma Lmap_im (z : ℂ) : (Lmap P z).im = Inner.cy P * z.im := by simp [Lmap]

lemma A0_apply (z : ℂ) : A0 P z = ((A11 P * z.re : ℝ) : ℂ) + ((A22 P * z.im : ℝ) : ℂ) * I := by
  apply Complex.ext
  · rw [A0, ContinuousLinearMap.comp_apply, Lclm_apply, DC0_re, Lmap_re]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    unfold A11; ring
  · rw [A0, ContinuousLinearMap.comp_apply, Lclm_apply, DC0_im, Lmap_im]
    simp only [add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_add]
    unfold A22; ring

lemma A11_neg : A11 P < 0 := by
  have := rb_pos P; have := Real.pi_pos
  have : 0 < Inner.cx P := div_pos (Inner.a0_pos P) (Real.sqrt_pos.2 (Inner.j0_pos P))
  unfold A11; have : 0 < Inner.cx P / (2 * π * rb P) := by positivity
  linarith

lemma A22_neg : A22 P < 0 := by
  have := rb_pos P; have := Real.pi_pos
  have : 0 < Inner.cy P := div_pos (Inner.b0_pos P) (Real.sqrt_pos.2 (Inner.j0_pos P))
  unfold A22; have : 0 < 2 * π * rb P * Inner.cy P := by positivity
  linarith

lemma A11_mul_A22 : A11 P * A22 P = 1 := by
  have := rb_pos P; have := Real.pi_pos
  have h := Inner.cx_mul_cy P
  unfold A11 A22
  field_simp
  linarith

/-- **`prop:pln-inner-family`.** `q^in_0(z) = b + 𝐀₀ z`. -/
theorem qinner_zero (z : ℂ) : qinner P 0 z = bpt P + A0 P z := by
  rw [qinner, lam_zero, fs_eq_L_at_zero, Clam_zero_eq, A0, ContinuousLinearMap.comp_apply,
    Lclm_apply]

/-- **`prop:pln-inner-family`.** `q^in_1 = C ∘ f` on `D̄(p†)`. -/
theorem qinner_one {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    qinner P 1 z = Inner.chartC P (Inner.finner P z) := by
  have hdom := (qinner_dom P ⟨zero_le_one, le_rfl⟩ hz).2
  rw [lam_one, one_mul, fs_eq_finner] at hdom
  rw [qinner, lam_one, fs_eq_finner, Clam_eq P one_pos (w := Inner.finner P z)
    (by rw [one_mul]; exact hdom.le), one_smul, Complex.ofReal_one, div_one]
  ring

end SymplecticPacking.Qhat
