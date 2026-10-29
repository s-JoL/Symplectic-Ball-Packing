import Mathlib
import SymplecticPacking.Inner.Xtilde
import SymplecticPacking.Inner.Vtilde
import SymplecticPacking.Inner.Normalize

/-!
# The Morse density and the comparison constants

`sec:pll`, `lem:pll-morse-density` (algebraic part) and the comparison constants
(`def:pll-comparison-constants`, `lem:pll-mean`): the Morse map `F_mor(u + iv) = X̃(u) + i Ỹ(v)`, its Jacobian
density `J = X̃'(u) Ỹ'(v)`, the constants `b₀, j₀, c_x, c_y, ρ_T`, and `d₀, p₊, E_c`.
-/

noncomputable section

namespace SymplecticPacking

/-! ### Comparison constants (`def:pll-comparison-constants`, `lem:pll-mean`) -/

namespace Params

variable (P : Params)

/-- `d₀ = δ' + μ`. -/
def d0 : ℝ := Inner.deltaPrime P + Inner.muV P

/-- `p₊ = h - 15e/4`. -/
def pplus : ℝ := P.h - 15 * P.eq_ / 4

/-- `E_c = h - 2e`. -/
def Ec : ℝ := P.h - 2 * P.eq_

lemma deltaPrime_eq : Inner.deltaPrime P = P.eq_ / 8 + P.eq_ / 196608 := rfl

lemma muV_nonneg : 0 ≤ Inner.muV P := by
  unfold Inner.muV
  exact intervalIntegral.integral_nonneg (by norm_num) fun y _ => Inner.Vtilde_nonneg P y

lemma deltaPrime_pos : 0 < Inner.deltaPrime P := by
  rw [deltaPrime_eq]; have := P.eq_pos; positivity

lemma d0_nonneg : 0 ≤ P.d0 := by
  unfold d0; linarith [P.deltaPrime_pos, P.muV_nonneg]

/-- `d₀ < 5e/12`. -/
theorem d0_lt : P.d0 < 5 * P.eq_ / 12 := by
  have := Inner.muV_le P; have := P.eq_pos
  unfold d0; rw [deltaPrime_eq]; linarith

/-- `2δ' + μ < 13e/24`. -/
theorem two_deltaPrime_add_muV_lt : 2 * Inner.deltaPrime P + Inner.muV P < 13 * P.eq_ / 24 := by
  have := Inner.muV_le P; have := P.eq_pos
  rw [deltaPrime_eq]; linarith

/-- `p₊ > 0`. -/
theorem pplus_pos : 0 < P.pplus := by
  have := P.eq_le_h; have := P.h_pos; have := P.eq_pos
  unfold pplus; linarith

/-- `E_c - d₀ > p₊`. -/
theorem pplus_lt_Ec_sub_d0 : P.pplus < P.Ec - P.d0 := by
  have := P.d0_lt; have := P.eq_pos
  unfold pplus Ec; linarith

end Params

namespace Inner

open Filter Topology Set Complex
open scoped ContDiff

variable (P : Params)

/-! ### Constants of the linear part (`def:pll-curvatures`) -/

/-- `b₀ = √(2/e)`. -/
def b0 : ℝ := √(2 / P.eq_)

/-- `j₀ = a₀ b₀`. -/
def j0 : ℝ := a0 P * b0 P

/-- `c_x = a₀/√j₀`. -/
def cx : ℝ := a0 P / √(j0 P)

/-- `c_y = b₀/√j₀`. -/
def cy : ℝ := b0 P / √(j0 P)

/-- `ρ_T = min(u_ε, v_ε)`. -/
def rhoT : ℝ := min (uEps P) (vEps P)

lemma a0_pos : 0 < a0 P := Real.sqrt_pos.2 (div_pos two_pos P.alpha0_pos)

lemma b0_pos : 0 < b0 P := Real.sqrt_pos.2 (div_pos two_pos P.eq_pos)

lemma j0_pos : 0 < j0 P := mul_pos (a0_pos P) (b0_pos P)

lemma uEps_pos : 0 < uEps P := mul_pos (sqrt_alpha0_half_pos P) (epsR_pos P)

lemma vEps_pos : 0 < vEps P :=
  mul_pos (Real.sqrt_pos.2 (div_pos P.eq_pos two_pos)) (by linarith [wV_le P])

lemma rhoT_pos : 0 < rhoT P := lt_min (uEps_pos P) (vEps_pos P)

/-- `c_x c_y = 1`. -/
theorem cx_mul_cy : cx P * cy P = 1 := by
  have h := j0_pos P
  unfold cx cy
  rw [div_mul_div_comm, Real.mul_self_sqrt h.le]
  exact div_self h.ne'

/-! ### The Morse map and its density -/

/-- `F_mor(u + iv) = X̃(u) + i Ỹ(v)`. -/
def Fmor (w : ℂ) : ℂ := (Xtilde P w.re : ℂ) + (Ytilde P w.im : ℂ) * I

/-- `J(u + iv) = X̃'(u) Ỹ'(v)`. -/
def Jmor (w : ℂ) : ℝ := deriv (Xtilde P) w.re * deriv (Ytilde P) w.im

/-- The density `J` as a (constant) one-parameter family, for the normalisation API. -/
def JmorF : ℝ → ℂ → ℝ := fun _ => Jmor P

@[simp] lemma Fmor_re (w : ℂ) : (Fmor P w).re = Xtilde P w.re := by simp [Fmor]

@[simp] lemma Fmor_im (w : ℂ) : (Fmor P w).im = Ytilde P w.im := by simp [Fmor]

lemma Ytilde_deriv_linear {v : ℝ} (hv : |v| < vEps P) : deriv (Ytilde P) v = b0 P := by
  have hev : Ytilde P =ᶠ[𝓝 v] fun v => √(2 / P.eq_) * v := by
    have : Ioo (-vEps P) (vEps P) ∈ 𝓝 v := isOpen_Ioo.mem_nhds (abs_lt.mp hv)
    filter_upwards [this] with x hx
    exact Ytilde_linear P (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  rw [hev.deriv_eq]
  simp [b0]

/-- The derivative identities extend to the closed intervals by continuity. -/
lemma deriv_eq_of_closed {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {c a : ℝ} (ha : 0 < a)
    (h : ∀ x, |x| < a → deriv f x = c) {x : ℝ} (hx : |x| ≤ a) : deriv f x = c := by
  have hcont : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hcl : IsClosed {x | deriv f x = c} := isClosed_eq hcont continuous_const
  have hsub : Ioo (-a) a ⊆ {x | deriv f x = c} := fun x hx => h x (abs_lt.mpr hx)
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by linarith)] at this
  exact this (abs_le.mp hx)

lemma Xtilde_deriv_closed {u : ℝ} (hu : |u| ≤ uEps P) : deriv (Xtilde P) u = a0 P :=
  deriv_eq_of_closed (Xtilde_smooth P) (uEps_pos P) (fun _ h => Xtilde_deriv_linear P h) hu

lemma Ytilde_deriv_closed {v : ℝ} (hv : |v| ≤ vEps P) : deriv (Ytilde P) v = b0 P :=
  deriv_eq_of_closed (Ytilde_smooth P) (vEps_pos P) (fun _ h => Ytilde_deriv_linear P h) hv

/-- **`lem:pll-morse-density`.** `J(w) = j₀` for `|w| ≤ ρ_T`. -/
theorem Jmor_const {w : ℂ} (hw : ‖w‖ ≤ rhoT P) : Jmor P w = j0 P := by
  have hu : |w.re| ≤ uEps P := (abs_re_le_norm w).trans (hw.trans (min_le_left _ _))
  have hv : |w.im| ≤ vEps P := (abs_im_le_norm w).trans (hw.trans (min_le_right _ _))
  rw [Jmor, Xtilde_deriv_closed P hu, Ytilde_deriv_closed P hv, j0]

theorem Jmor_pos (w : ℂ) : 0 < Jmor P w :=
  mul_pos (Xtilde_deriv_pos P _) (Ytilde_deriv_pos P _)

lemma contDiff_deriv_Xtilde : ContDiff ℝ ∞ (deriv (Xtilde P)) :=
  (contDiff_infty_iff_deriv.mp (Xtilde_smooth P)).2

lemma contDiff_deriv_Ytilde : ContDiff ℝ ∞ (deriv (Ytilde P)) :=
  (contDiff_infty_iff_deriv.mp (Ytilde_smooth P)).2

theorem Jmor_smooth : ContDiff ℝ ∞ (Jmor P) := by
  unfold Jmor
  exact ((contDiff_deriv_Xtilde P).comp reCLM.contDiff).mul
    ((contDiff_deriv_Ytilde P).comp imCLM.contDiff)

theorem JmorF_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => JmorF P p.1 p.2) :=
  (Jmor_smooth P).comp contDiff_snd

/-- **`lem:pll-morse-density`.** `R̃(X̃(u)) + Ṽ(Ỹ(v)) = u² + v² = |w|²`. -/
theorem Fmor_level (w : ℂ) :
    Rtilde P (Fmor P w).re + Vtilde P (Fmor P w).im = ‖w‖ ^ 2 := by
  rw [Fmor_re, Fmor_im, Rtilde_Xtilde, Vtilde_Ytilde, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  ring

end Inner

end SymplecticPacking
