import SymplecticPacking.HighDim.Comparator.PlanarClock
import SymplecticPacking.Branch2.Planar.Endpoint

/-!
# Rescaled polar charts with an arbitrary positive centre

The closed chart formula used by the planar generator has determinant one and
is injective on its angular strip. These statements use no special packing parameters.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen.Chart
open Set Filter Topology Complex
open Qhat (gexp gexp_mul gexp_zero gexp_contDiff)
open scoped ContDiff Real
def rb (p : ℝ) : ℝ := Real.sqrt (p / Real.pi)
def bpt (p : ℝ) : ℂ := -(rb p : ℂ)
def chartDom (p : ℝ) : Set ℂ := {w | 0 < p + w.re ∧ |w.im| < 1 / 2}

variable (p : ℝ) (hp : 0 < p)

lemma rb_pos (hp : 0 < p) : 0 < rb p := Real.sqrt_pos.mpr (div_pos hp Real.pi_pos)
lemma rb_sq (hp : 0 < p) : rb p ^ 2 = p / Real.pi := Real.sq_sqrt (div_pos hp Real.pi_pos).le
/-- Angular factor `2π r_b i g(2πiλv)`. -/
def Hy (lam : ℝ) (w : ℂ) : ℂ :=
  ((2 * π * rb p : ℝ) : ℂ) * I * gexp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- Radial factor `e^{2πiλv}/(π(r_b + √((p* + λu)/π)))`. -/
def Hx (lam : ℝ) (w : ℂ) : ℂ :=
  (((π * (rb p + √((p + lam * w.re) / π)))⁻¹ : ℝ) : ℂ) *
    Complex.exp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- **`def:pln-charts`.** The rescaled chart
`C_λ(w) = b + ∫₀¹ DC(tλw) w dt`, in the closed form `b - v H_y - u H_x`. -/
def Clam (lam : ℝ) (w : ℂ) : ℂ := bpt p - (w.im : ℂ) * Hy p lam w - (w.re : ℂ) * Hx p lam w

/-- `DC(0) = diag(-1/(2π r_b), -2π r_b)`. -/
def DC0 : ℂ →L[ℝ] ℂ :=
  -(((2 * π * rb p : ℝ) : ℂ) * I) • (ofRealCLM.comp imCLM) -
    (((2 * π * rb p)⁻¹ : ℝ) : ℂ) • (ofRealCLM.comp reCLM)

lemma DC0_apply (w : ℂ) :
    DC0 p w = -(((2 * π * rb p : ℝ) : ℂ) * I) * w.im - (((2 * π * rb p)⁻¹ : ℝ) : ℂ) * w.re := by
  simp [DC0]

lemma DC0_re (w : ℂ) : (DC0 p w).re = -(2 * π * rb p)⁻¹ * w.re := by
  rw [DC0_apply]; simp

lemma DC0_im (w : ℂ) : (DC0 p w).im = -(2 * π * rb p) * w.im := by
  rw [DC0_apply]; simp

lemma DC0_det (hp : 0 < p) : LinearMap.det (DC0 p : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [Inner.det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe, DC0_re, DC0_im]
  have := rb_pos p hp; have := Real.pi_pos
  simp; field_simp

lemma DC0_injective (hp : 0 < p) : Function.Injective (DC0 p) :=
  Inner.injective_of_det_ne_zero _ (by rw [DC0_det p hp]; norm_num)

/-- `C_0(w) = b + DC(0) w`. -/
theorem Clam_zero_eq (hp : 0 < p) (w : ℂ) : Clam p 0 w = bpt p + DC0 p w := by
  have hrb : √(p / π) = rb p := rfl
  simp only [Clam, Hy, Hx, DC0_apply, zero_mul, mul_zero, Complex.ofReal_zero, gexp_zero,
    Complex.exp_zero, mul_one, add_zero, hrb]
  have := rb_pos p hp; have := Real.pi_pos
  rw [show (π * (rb p + rb p))⁻¹ = (2 * π * rb p)⁻¹ by ring_nf]
  ring

lemma smul_re' (lam : ℝ) (w : ℂ) : (lam • w).re = lam * w.re := by simp
lemma smul_im' (lam : ℝ) (w : ℂ) : (lam • w).im = lam * w.im := by simp

/-- **`lem:pln-chart-lambda`.** For `λ > 0`, `C_λ(w) = b + (C(λw) - b)/λ`. -/
theorem Clam_eq (hp : 0 < p) {lam : ℝ} (hlam : 0 < lam) {w : ℂ} (hw : 0 ≤ p + lam * w.re) :
    Clam p lam w = bpt p + (Branch2.Planar.chart p (lam • w) - bpt p) / lam := by
  set u := w.re
  set v := w.im
  set ρ := √((p + lam * u) / π)
  set θ := 2 * π * lam * v
  set E := Complex.exp ((θ : ℂ) * I)
  have hrb := rb_pos p hp
  have hpi := Real.pi_pos
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (p + lam * u) / π := Real.sq_sqrt (div_nonneg hw hpi.le)
  have hrbsq := rb_sq p hp
  -- radial identity `λu/(π(r_b + ρ)) = ρ - r_b`
  have hrad : lam * u * (π * (rb p + ρ))⁻¹ = ρ - rb p := by
    have hden : 0 < π * (rb p + ρ) := by positivity
    rw [← div_eq_mul_inv, div_eq_iff hden.ne']
    have : (ρ - rb p) * (π * (rb p + ρ)) = π * (ρ ^ 2 - rb p ^ 2) := by ring
    rw [this, hρsq, hrbsq]; field_simp; ring
  -- angular identity `λ v · 2π r_b i g(iθ) = r_b (e^{iθ} - 1)`
  have hang : (lam : ℂ) * (v : ℂ) * (((2 * π * rb p : ℝ) : ℂ) * I * gexp ((θ : ℂ) * I)) =
      (rb p : ℂ) * (E - 1) := by
    rw [← gexp_mul]; simp only [θ]; push_cast; ring
  have hC : Branch2.Planar.chart p (lam • w) = -((ρ : ℂ) * E) := by
    have h1 : 2 * π * (lam • w).im = θ := by rw [smul_im']; simp only [θ, v]; ring
    have h2 : p + (lam • w).re = p + lam * u := by rw [smul_re']
    rw [Branch2.Planar.chart, h1, h2]
  have hlam' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  rw [hC, ← sub_eq_iff_eq_add', eq_div_iff hlam']
  have hrad' : (lam : ℂ) * (u : ℂ) * (((π * (rb p + ρ))⁻¹ : ℝ) : ℂ) = (ρ : ℂ) - (rb p : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hrad
    push_cast at this ⊢
    linear_combination this
  simp only [Clam, Hy, Hx, bpt]
  rw [show (2 * π * lam * w.im) = θ from rfl]
  linear_combination (-1 : ℂ) * hang - E * hrad'

/-! ### Smoothness, determinant and injectivity of `C_λ` (`lem:pln-chart-lambda`) -/

lemma Hy_contDiff : ContDiff ℝ ∞ (fun q : ℝ × ℂ => Hy p q.1 q.2) := by
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.im) := imCLM.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (((2 * π * q.1 * q.2.im : ℝ) : ℂ) * I)) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_fst).mul him)).mul contDiff_const
  exact contDiff_const.mul (gexp_contDiff.comp hθ)

lemma Hx_contDiffAt (hp : 0 < p) {q : ℝ × ℂ} (hq : 0 < p + q.1 * q.2.re) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Hx p q.1 q.2) q := by
  have hre : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.re) := reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => q.2.im) := imCLM.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (((2 * π * q.1 * q.2.im : ℝ) : ℂ) * I)) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_fst).mul him)).mul contDiff_const
  have hpi := Real.pi_pos
  have harg : 0 < (p + q.1 * q.2.re) / π := div_pos hq hpi
  have hsq : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => √((p + q.1 * q.2.re) / π)) q :=
    (Real.contDiffAt_sqrt harg.ne').comp q
      ((contDiff_const.add (contDiff_fst.mul hre)).div_const π).contDiffAt
  have hden : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => (π * (rb p + √((p + q.1 * q.2.re) / π)))⁻¹) q :=
    (contDiffAt_const.mul (contDiffAt_const.add hsq)).inv
      (by have := rb_pos p hp; have := Real.sqrt_nonneg ((p + q.1 * q.2.re) / π); positivity)
  exact (ofRealCLM.contDiff.contDiffAt.comp q hden).mul
    ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp q hθ.contDiffAt)

/-- `(λ, w) ↦ C_λ(w)` is `C^∞` at every point with `p* + λ Re w > 0`. -/
theorem Clam_contDiffAt (hp : 0 < p) {q : ℝ × ℂ} (hq : 0 < p + q.1 * q.2.re) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Clam p q.1 q.2) q := by
  have hre : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (q.2.re : ℂ)) :=
    ofRealCLM.contDiff.comp (reCLM.contDiff.comp contDiff_snd)
  have him : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (q.2.im : ℂ)) :=
    ofRealCLM.contDiff.comp (imCLM.contDiff.comp contDiff_snd)
  unfold Clam
  exact (contDiffAt_const.sub (him.contDiffAt.mul (Hy_contDiff p).contDiffAt)).sub
    (hre.contDiffAt.mul (Hx_contDiffAt p hp hq))

/-- The domain `{(λ, w) : p* + λ Re w > 0}` (contains `{λ w ∈ 𝒰}`). -/
def ClamDom : Set (ℝ × ℂ) := {q | 0 < p + q.1 * q.2.re}

/-- **`lem:pln-chart-lambda`.** `(λ, w) ↦ C_λ(w)` is `C^∞` on `{p* + λ Re w > 0}`. -/
theorem Clam_smooth (hp : 0 < p) : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => Clam p q.1 q.2) (ClamDom p) :=
  fun _ hq => (Clam_contDiffAt p hp hq).contDiffWithinAt

lemma Clam_slice_contDiffAt (hp : 0 < p) {lam : ℝ} {w : ℂ} (hw : 0 < p + lam * w.re) :
    ContDiffAt ℝ ∞ (Clam p lam) w :=
  (Clam_contDiffAt p hp (q := (lam, w)) hw).comp w (contDiffAt_const.prodMk contDiffAt_id)

lemma chartC_differentiableAt {w : ℂ} (hw : 0 < p + w.re) :
    DifferentiableAt ℝ (Branch2.Planar.chart p) w := by
  have harg : 0 < (p + w.re) / π := div_pos hw Real.pi_pos
  have hre : DifferentiableAt ℝ (fun w : ℂ => (p + w.re) / π) w := by fun_prop
  have h1 : DifferentiableAt ℝ (fun w : ℂ => √((p + w.re) / π)) w := hre.sqrt harg.ne'
  have h2 : DifferentiableAt ℝ (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ) * I) w := by fun_prop
  exact ((ofRealCLM.differentiableAt.comp w h1).mul h2.cexp).neg

/-- For `λ > 0`, `DC_λ(w) = DC(λw)`. -/
theorem Clam_fderiv (hp : 0 < p) {lam : ℝ} (hlam : 0 < lam) {w : ℂ} (hw : 0 < p + lam * w.re) :
    fderiv ℝ (Clam p lam) w = fderiv ℝ (Branch2.Planar.chart p) (lam • w) := by
  have hO : IsOpen {w' : ℂ | 0 < p + lam * w'.re} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_const.mul Complex.continuous_re))
  have hev : Clam p lam =ᶠ[𝓝 w] fun w' => bpt p + (Branch2.Planar.chart p (lam • w') - bpt p) / lam := by
    filter_upwards [hO.mem_nhds hw] with w' hw'
    exact Clam_eq p hp hlam hw'.le
  have hD := (chartC_differentiableAt p (w := lam • w) (by rw [smul_re']; exact hw)).hasFDerivAt
  have hcomp : HasFDerivAt (fun w' : ℂ => Branch2.Planar.chart p (lam • w'))
      ((fderiv ℝ (Branch2.Planar.chart p) (lam • w)).comp (lam • ContinuousLinearMap.id ℝ ℂ)) w :=
    hD.comp w ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul lam)
  have hfull : HasFDerivAt (fun w' => bpt p + (Branch2.Planar.chart p (lam • w') - bpt p) / lam)
      (fderiv ℝ (Branch2.Planar.chart p) (lam • w)) w := by
    have := ((hcomp.sub_const (bpt p)).mul_const ((lam : ℂ)⁻¹)).const_add (bpt p)
    refine this.congr_fderiv ?_
    ext1 x
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul]
    rw [Complex.real_smul, smul_eq_mul]
    field_simp
  rw [hev.fderiv_eq, hfull.fderiv]

/-- **`lem:pln-chart-lambda`.** `det DC_λ = 1` (for `λ ≥ 0`, `p* + λ Re w > 0`). -/
theorem Clam_det (hp : 0 < p) {lam : ℝ} (hlam : 0 ≤ lam) {w : ℂ} (hw : 0 < p + lam * w.re) :
    LinearMap.det (fderiv ℝ (Clam p lam) w : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    have hfun : Clam p 0 = fun w => bpt p + DC0 p w := funext (Clam_zero_eq p hp)
    rw [hfun, fderiv_const_add, ContinuousLinearMap.fderiv, DC0_det p hp]
  · rw [Clam_fderiv p hp h hw]
    exact Branch2.Planar.chart_det (by rw [smul_re']; exact hw)

/-- **`lem:pln-chart-lambda`.** `C_λ` is injective on `λ⁻¹ 𝒰` (on the whole plane if `λ = 0`). -/
theorem Clam_injOn (hp : 0 < p) {lam : ℝ} (hlam : 0 ≤ lam) :
    InjOn (Clam p lam) {w | lam • w ∈ chartDom p} := by
  rcases eq_or_lt_of_le hlam with h | h
  · subst h
    intro w₁ _ w₂ _ hw
    rw [Clam_zero_eq p hp, Clam_zero_eq p hp, add_right_inj] at hw
    exact DC0_injective p hp hw
  · intro w₁ hw₁ w₂ hw₂ hw
    have h1 : 0 ≤ p + lam * w₁.re := by have := hw₁.1; rw [smul_re'] at this; linarith
    have h2 : 0 ≤ p + lam * w₂.re := by have := hw₂.1; rw [smul_re'] at this; linarith
    rw [Clam_eq p hp h h1, Clam_eq p hp h h2, add_right_inj] at hw
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
    have hC : Branch2.Planar.chart p (lam • w₁) = Branch2.Planar.chart p (lam • w₂) := by
      have := (div_left_inj' hl).mp hw
      exact sub_left_inj.mp this
    have := Branch2.Planar.chart_injOn hw₁ hw₂ hC
    exact smul_right_injective ℂ h.ne' this

/-- A global norm bound for the closed rescaled chart formula. -/
theorem Clam_norm_sub (hp : 0 < p) (lam : ℝ) (w : ℂ) :
    ‖Clam p lam w - bpt p‖ ≤ ((Real.pi * rb p)⁻¹ + 2 * Real.pi * rb p) * ‖w‖ := by
  have hr := rb_pos p hp
  have hb : 0 < Real.pi * rb p := mul_pos Real.pi_pos hr
  have hHy : ‖Hy p lam w‖ ≤ 2 * Real.pi * rb p := by
    unfold Hy
    rw [norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (Qhat.norm_gexp_le _)
  have hHx : ‖Hx p lam w‖ ≤ (Real.pi * rb p)⁻¹ := by
    have hρ := Real.sqrt_nonneg ((p + lam * w.re) / Real.pi)
    have hd : 0 < Real.pi * (rb p + Real.sqrt ((p + lam * w.re) / Real.pi)) := by positivity
    unfold Hx
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simpa only [one_div] using one_div_le_one_div_of_le hb
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hρ) Real.pi_pos.le)
  have hh : Clam p lam w - bpt p = -(w.im : ℂ) * Hy p lam w - (w.re : ℂ) * Hx p lam w := by
    unfold Clam
    ring
  rw [hh]
  calc
    _ ≤ ‖-(w.im : ℂ) * Hy p lam w‖ + ‖(w.re : ℂ) * Hx p lam w‖ := norm_sub_le _ _
    _ = |w.im| * ‖Hy p lam w‖ + |w.re| * ‖Hx p lam w‖ := by
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖w‖ * (2 * Real.pi * rb p) + ‖w‖ * (Real.pi * rb p)⁻¹ :=
      add_le_add (mul_le_mul (Complex.abs_im_le_norm w) hHy (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Complex.abs_re_le_norm w) hHx (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end SymplecticPacking.HighDim.PlanarGen.Chart
