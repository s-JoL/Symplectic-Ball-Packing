import SymplecticPacking.Bundle.Fermat
import SymplecticPacking.Complex.ArgPrinciple

/-!
# The Jacobi theta function of the hexagonal lattice

`sec:fer-torus` (`def:fer-theta`, `lem:fer-theta`): the Jacobi theta function `θ₁(ζ | τ)` for the
hexagonal lattice, its zeros, `℘ = -(log θ₁)'' + c₀`, and the pole-free theta lift `Zraw`.

Normalisation (differs from the paper, which rescales the lattice by `L = Γ(1/3)³/(2π)`):
* the lattice is `hexPair.lattice = ℤ + ℤ ζ₆ = ℤ + ℤ τ` with `τ = e^{2πi/3} = ζ₆ - 1`
  (the paper's `τ`; Lean's lattice is the paper's `Λ / L`);
* `ζ = π z` (i.e. `L = 1`), so `a_ϑ = π²`, `b_ϑ = π³`;
* the map is normalised by `cF, dF` (`cF³ = 1/g₃`, `dF² = 1/(3 g₃)`) instead of `g₃ = 1`, so
  `Zraw = ![2 cF π² P, -θ³ - dF π³ Q, -θ³ + dF π³ Q] = θ³ • torusLift`.
* torus coordinates: `z = u + τ v`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open _root_.Complex PeriodPair Set Filter Topology
open scoped Real

/-! ## The modulus `τ = e^{2πi/3}` -/

/-- `τ = ζ₆ - 1 = e^{2πi/3} = -1/2 + i√3/2`. -/
def tau : ℂ := zeta6 - 1

lemma tau_re : tau.re = -1 / 2 := by simp [tau, zeta6]; norm_num

lemma tau_im : tau.im = Real.sqrt 3 / 2 := by simp [tau, zeta6]

lemma tau_im_pos : 0 < tau.im := by rw [tau_im]; positivity

lemma tau_mem_lattice : tau ∈ hexPair.lattice := by
  have h1 : (1 : ℂ) ∈ hexPair.lattice := hexPair.ω₁_mem_lattice
  have h2 : zeta6 ∈ hexPair.lattice := hexPair.ω₂_mem_lattice
  exact Submodule.sub_mem _ h2 h1

lemma one_mem_lattice : (1 : ℂ) ∈ hexPair.lattice := hexPair.ω₁_mem_lattice

/-- `ℤ + ℤ τ = hexPair.lattice`. -/
lemma mem_lattice_iff (z : ℂ) : z ∈ hexPair.lattice ↔ ∃ m n : ℤ, z = m + n * tau := by
  constructor
  · intro hz
    rw [PeriodPair.lattice, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    refine ⟨a + b, b, ?_⟩
    simp only [hexPair, zsmul_eq_mul, tau]; push_cast; ring
  · rintro ⟨m, n, rfl⟩
    exact Submodule.add_mem _ (by simpa using Submodule.smul_mem _ m one_mem_lattice)
      (by simpa using Submodule.smul_mem _ n tau_mem_lattice)

/-- Periodicity under the generators `1, τ` implies periodicity under the lattice. -/
lemma periodic_lattice {X : Type*} {F : ℂ → X} (h1 : ∀ z, F (z + 1) = F z)
    (hτ : ∀ z, F (z + tau) = F z) {l : ℂ} (hl : l ∈ hexPair.lattice) (z : ℂ) :
    F (z + l) = F z := by
  obtain ⟨m, n, rfl⟩ := (mem_lattice_iff l).mp hl
  have p1 : Function.Periodic F 1 := h1
  have p2 : Function.Periodic F tau := hτ
  have := (p1.int_mul m).add_period (p2.int_mul n)
  simpa using this z

/-! ## The Jacobi theta function `θ₁` -/

/-- `θ₁(ζ | τ) = 2 ∑_{n ≥ 0} (-1)ⁿ e^{iπτ(n+1/2)²} sin((2n+1)ζ)`, written via Mathlib's
`jacobiTheta₂`: `θ₁(ζ) = -i e^{iπτ/4 + iζ} Θ(ζ/π + 1/2 + τ/2, τ)`. -/
def jacobiTheta1 (ζ : ℂ) : ℂ :=
  -I * cexp (π * I * tau / 4 + I * ζ) * jacobiTheta₂ (ζ / π + 1 / 2 + tau / 2) tau

/-- The automorphy factor `e(ζ) = -e^{-iπτ} e^{-2iζ}` of `θ₁` under `ζ ↦ ζ + πτ`. -/
def thetaFactor (ζ : ℂ) : ℂ := -cexp (-(π * I * tau) - 2 * I * ζ)

lemma thetaFactor_ne_zero (ζ : ℂ) : thetaFactor ζ ≠ 0 := by
  simp [thetaFactor, Complex.exp_ne_zero]

lemma pi_ne_zero' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

theorem differentiable_jacobiTheta1 : Differentiable ℂ jacobiTheta1 := by
  intro ζ
  unfold jacobiTheta1
  have h : DifferentiableAt ℂ (fun ζ : ℂ => jacobiTheta₂ (ζ / π + 1 / 2 + tau / 2) tau) ζ :=
    (differentiableAt_jacobiTheta₂_fst _ tau_im_pos).comp ζ (by fun_prop)
  fun_prop

theorem jacobiTheta1_add_pi (ζ : ℂ) : jacobiTheta1 (ζ + π) = -jacobiTheta1 ζ := by
  unfold jacobiTheta1
  have e1 : (ζ + π) / π + 1 / 2 + tau / 2 = (ζ / π + 1 / 2 + tau / 2) + 1 := by
    field_simp [pi_ne_zero']; ring
  rw [e1, jacobiTheta₂_add_left]
  have e2 : π * I * tau / 4 + I * (ζ + π) = (π * I * tau / 4 + I * ζ) + π * I := by ring
  rw [e2, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem jacobiTheta1_add_pi_tau (ζ : ℂ) :
    jacobiTheta1 (ζ + π * tau) = thetaFactor ζ * jacobiTheta1 ζ := by
  unfold jacobiTheta1 thetaFactor
  have e1 : (ζ + π * tau) / π + 1 / 2 + tau / 2 = (ζ / π + 1 / 2 + tau / 2) + tau := by
    field_simp [pi_ne_zero']; ring
  rw [e1, jacobiTheta₂_add_left']
  have : cexp (π * I * tau / 4 + I * (ζ + π * tau)) *
      cexp (-π * I * (tau + 2 * (ζ / π + 1 / 2 + tau / 2))) =
      -cexp (-(π * I * tau) - 2 * I * ζ) * cexp (π * I * tau / 4 + I * ζ) := by
    rw [← Complex.exp_add, neg_mul (cexp _), ← Complex.exp_add]
    have : π * I * tau / 4 + I * (ζ + π * tau) + -π * I * (tau + 2 * (ζ / π + 1 / 2 + tau / 2))
        = (-(π * I * tau) - 2 * I * ζ + (π * I * tau / 4 + I * ζ)) + (-1 : ℤ) * (π * I) := by
      field_simp [pi_ne_zero']; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  linear_combination (-I * jacobiTheta₂ (ζ / π + 1 / 2 + tau / 2) tau) * this

theorem jacobiTheta1_neg (ζ : ℂ) : jacobiTheta1 (-ζ) = -jacobiTheta1 ζ := by
  unfold jacobiTheta1
  set w := ζ / π + 1 / 2 + tau / 2
  have e1 : -ζ / π + 1 / 2 + tau / 2 = -((w - tau) + -1) := by
    simp only [w]; field_simp [pi_ne_zero']; ring
  rw [e1, jacobiTheta₂_neg_left]
  have e2 : jacobiTheta₂ (w - tau + -1) tau = jacobiTheta₂ (w - tau) tau := by
    rw [← jacobiTheta₂_add_left (w - tau + -1)]; ring_nf
  rw [e2]
  have e3 := jacobiTheta₂_add_left' (w - tau) tau
  rw [sub_add_cancel] at e3
  -- `Θ(w - τ) = e^{iπ(2w - τ)} Θ(w)`
  have e4 : jacobiTheta₂ (w - tau) tau = cexp (π * I * (2 * w - tau)) * jacobiTheta₂ w tau := by
    rw [e3, ← mul_assoc, ← Complex.exp_add]
    have : π * I * (2 * w - tau) + -π * I * (tau + 2 * (w - tau)) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  rw [e4]
  have e5 : cexp (π * I * tau / 4 + I * -ζ) * cexp (π * I * (2 * w - tau)) =
      -cexp (π * I * tau / 4 + I * ζ) := by
    rw [← Complex.exp_add]
    have : π * I * tau / 4 + I * -ζ + π * I * (2 * w - tau) =
        (π * I * tau / 4 + I * ζ) + π * I := by
      simp only [w]; field_simp [pi_ne_zero']; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  linear_combination (-I * jacobiTheta₂ w tau) * e5

theorem jacobiTheta1_zero : jacobiTheta1 0 = 0 := by
  have := jacobiTheta1_neg 0
  rw [neg_zero] at this
  linear_combination this / 2

/-- `θ₁` is not identically zero: at `ζ₀ = -π(1+τ)/2` it is a nonzero multiple of the
one-variable theta value `ϑ(τ) = Θ(0, τ)`, and `‖ϑ(τ) - 1‖ < 1`. -/
def zetaNZ : ℂ := -(π * (1 + tau) / 2)

lemma jacobiTheta_tau_ne_zero : jacobiTheta tau ≠ 0 := by
  have hb := norm_jacobiTheta_sub_one_le tau_im_pos
  set x := Real.exp (-π * tau.im)
  have hx0 : 0 < x := Real.exp_pos _
  have hx : x < 1 / 3 := by
    have h1 : (2.5 : ℝ) < π * tau.im := by
      rw [tau_im]
      have hs : (1.7 : ℝ) < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      nlinarith [Real.pi_gt_three]
    have h2 : (3 : ℝ) < Real.exp (π * tau.im) := by
      have := Real.add_one_le_exp (π * tau.im); linarith
    have h3 : x * Real.exp (π * tau.im) = 1 := by
      simp only [x]; rw [← Real.exp_add]; simp
    nlinarith
  intro h
  rw [h, zero_sub, norm_neg, norm_one] at hb
  have : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  linarith

theorem jacobiTheta1_zetaNZ : jacobiTheta1 zetaNZ ≠ 0 := by
  unfold jacobiTheta1 zetaNZ
  have : -(π * (1 + tau) / 2) / π + 1 / 2 + tau / 2 = 0 := by field_simp [pi_ne_zero']; ring
  rw [this, ← jacobiTheta_eq_jacobiTheta₂]
  exact mul_ne_zero (mul_ne_zero (by simp) (Complex.exp_ne_zero _)) jacobiTheta_tau_ne_zero

/-! ## Derivatives and their quasi-periodicity -/

/-- `θ₁'`. -/
def dTheta1 : ℂ → ℂ := deriv jacobiTheta1
/-- `θ₁''`. -/
def d2Theta1 : ℂ → ℂ := deriv dTheta1
/-- `θ₁'''`. -/
def d3Theta1 : ℂ → ℂ := deriv d2Theta1

lemma differentiable_dTheta1 : Differentiable ℂ dTheta1 := differentiable_jacobiTheta1.deriv
lemma differentiable_d2Theta1 : Differentiable ℂ d2Theta1 := differentiable_dTheta1.deriv
lemma differentiable_d3Theta1 : Differentiable ℂ d3Theta1 := differentiable_d2Theta1.deriv

/-- If `f (ζ + c) = -f ζ` for all `ζ`, the same holds for `f'`. -/
lemma deriv_antiperiodic {f : ℂ → ℂ} {c : ℂ} (h : ∀ ζ, f (ζ + c) = -f ζ) (ζ : ℂ) :
    deriv f (ζ + c) = -deriv f ζ := by
  have e : (fun ζ => f (ζ + c)) = fun ζ => -f ζ := funext h
  have := congrArg (fun F => deriv F ζ) e
  simp only [deriv_comp_add_const, deriv.fun_neg] at this
  exact this

lemma hasDerivAt_thetaFactor (ζ : ℂ) :
    HasDerivAt thetaFactor (-2 * I * thetaFactor ζ) ζ := by
  unfold thetaFactor
  have h : HasDerivAt (fun ζ : ℂ => -(π * I * tau) - 2 * I * ζ) (-2 * I) ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul (2 * I)).const_sub (-(π * I * tau))
  have := (h.cexp).neg
  convert this using 1; ring

/-- If `f (ζ + c) = e(ζ) g(ζ)` for all `ζ` (with `e = thetaFactor`), then
`f'(ζ + c) = e(ζ) (g'(ζ) - 2i g(ζ))`. -/
lemma deriv_quasiperiodic {f g : ℂ → ℂ} {c : ℂ} (hg : Differentiable ℂ g)
    (h : ∀ ζ, f (ζ + c) = thetaFactor ζ * g ζ) (ζ : ℂ) :
    deriv f (ζ + c) = thetaFactor ζ * (deriv g ζ - 2 * I * g ζ) := by
  have e : (fun ζ => f (ζ + c)) = fun ζ => thetaFactor ζ * g ζ := funext h
  have := congrArg (fun F => deriv F ζ) e
  simp only [deriv_comp_add_const] at this
  have hd : HasDerivAt (fun y => thetaFactor y * g y)
      (-2 * I * thetaFactor ζ * g ζ + thetaFactor ζ * deriv g ζ) ζ :=
    (hasDerivAt_thetaFactor ζ).mul (hg ζ).hasDerivAt
  rw [this, hd.deriv]
  ring

theorem dTheta1_add_pi (ζ : ℂ) : dTheta1 (ζ + π) = -dTheta1 ζ :=
  deriv_antiperiodic jacobiTheta1_add_pi ζ
theorem d2Theta1_add_pi (ζ : ℂ) : d2Theta1 (ζ + π) = -d2Theta1 ζ :=
  deriv_antiperiodic dTheta1_add_pi ζ
theorem d3Theta1_add_pi (ζ : ℂ) : d3Theta1 (ζ + π) = -d3Theta1 ζ :=
  deriv_antiperiodic d2Theta1_add_pi ζ

theorem dTheta1_add_pi_tau (ζ : ℂ) :
    dTheta1 (ζ + π * tau) = thetaFactor ζ * (dTheta1 ζ - 2 * I * jacobiTheta1 ζ) :=
  deriv_quasiperiodic differentiable_jacobiTheta1 jacobiTheta1_add_pi_tau ζ

theorem d2Theta1_add_pi_tau (ζ : ℂ) :
    d2Theta1 (ζ + π * tau) = thetaFactor ζ *
      (d2Theta1 ζ - 4 * I * dTheta1 ζ - 4 * jacobiTheta1 ζ) := by
  have hg : Differentiable ℂ (fun ζ => dTheta1 ζ - 2 * I * jacobiTheta1 ζ) :=
    differentiable_dTheta1.sub (differentiable_jacobiTheta1.const_mul _)
  have hd : HasDerivAt (fun ζ => dTheta1 ζ - 2 * I * jacobiTheta1 ζ)
      (d2Theta1 ζ - 2 * I * dTheta1 ζ) ζ :=
    (differentiable_dTheta1 ζ).hasDerivAt.sub
      ((differentiable_jacobiTheta1 ζ).hasDerivAt.const_mul _)
  rw [d2Theta1, deriv_quasiperiodic hg dTheta1_add_pi_tau ζ, hd.deriv]
  rw [← d2Theta1]
  ring_nf; rw [I_sq]; ring

theorem d3Theta1_add_pi_tau (ζ : ℂ) :
    d3Theta1 (ζ + π * tau) = thetaFactor ζ *
      (d3Theta1 ζ - 6 * I * d2Theta1 ζ - 12 * dTheta1 ζ + 8 * I * jacobiTheta1 ζ) := by
  have hg : Differentiable ℂ
      (fun ζ => d2Theta1 ζ - 4 * I * dTheta1 ζ - 4 * jacobiTheta1 ζ) :=
    (differentiable_d2Theta1.sub (differentiable_dTheta1.const_mul _)).sub
      (differentiable_jacobiTheta1.const_mul _)
  have hd : HasDerivAt (fun ζ => d2Theta1 ζ - 4 * I * dTheta1 ζ - 4 * jacobiTheta1 ζ)
      (d3Theta1 ζ - 4 * I * d2Theta1 ζ - 4 * dTheta1 ζ) ζ :=
    ((differentiable_d2Theta1 ζ).hasDerivAt.sub
      ((differentiable_dTheta1 ζ).hasDerivAt.const_mul _)).sub
      ((differentiable_jacobiTheta1 ζ).hasDerivAt.const_mul _)
  rw [d3Theta1, deriv_quasiperiodic hg d2Theta1_add_pi_tau ζ, hd.deriv]
  rw [← d3Theta1]
  ring_nf; rw [I_sq]; ring

theorem dTheta1_neg (ζ : ℂ) : dTheta1 (-ζ) = dTheta1 ζ := by
  have e : (fun ζ => jacobiTheta1 (-ζ)) = fun ζ => -jacobiTheta1 ζ := funext jacobiTheta1_neg
  have := congrArg (fun F => deriv F ζ) e
  simp only [deriv_comp_neg, deriv.fun_neg] at this
  simpa [dTheta1] using this

theorem d2Theta1_zero : d2Theta1 0 = 0 := by
  have e : (fun ζ => dTheta1 (-ζ)) = fun ζ => dTheta1 ζ := funext dTheta1_neg
  have := congrArg (fun F => deriv F 0) e
  simp only [deriv_comp_neg] at this
  have h : -d2Theta1 0 = d2Theta1 0 := by simpa [d2Theta1] using this
  linear_combination -h / 2

/-! ## The logarithmic derivative and its contour integral -/

/-- The logarithmic derivative `θ₁'/θ₁` (junk value `0` at zeros of `θ₁`). -/
def logDerivTheta1 (ζ : ℂ) : ℂ := deriv jacobiTheta1 ζ / jacobiTheta1 ζ

lemma logDerivTheta1_add_pi (ζ : ℂ) : logDerivTheta1 (ζ + π) = logDerivTheta1 ζ := by
  unfold logDerivTheta1
  rw [show deriv jacobiTheta1 (ζ + π) = dTheta1 (ζ + π) from rfl, dTheta1_add_pi,
    jacobiTheta1_add_pi, neg_div_neg_eq]; rfl

lemma logDerivTheta1_add_pi_tau {ζ : ℂ} (h : jacobiTheta1 ζ ≠ 0) :
    logDerivTheta1 (ζ + π * tau) = logDerivTheta1 ζ - 2 * I := by
  unfold logDerivTheta1
  rw [show deriv jacobiTheta1 (ζ + π * tau) = dTheta1 (ζ + π * tau) from rfl,
    dTheta1_add_pi_tau, jacobiTheta1_add_pi_tau]
  have := thetaFactor_ne_zero ζ
  rw [show deriv jacobiTheta1 ζ = dTheta1 ζ from rfl]
  field_simp

lemma continuousAt_logDerivTheta1 {ζ : ℂ} (h : jacobiTheta1 ζ ≠ 0) :
    ContinuousAt logDerivTheta1 ζ :=
  (differentiable_dTheta1 ζ).continuousAt.div (differentiable_jacobiTheta1 ζ).continuousAt h

open SymplecticPacking.Complex in
open MeasureTheory intervalIntegral in
/-- **The contour integral of `θ₁'/θ₁`** over the boundary of a period parallelogram
`a + [0,1]π + [0,1]πτ` (avoiding the zeros) is `2πi`: opposite edges cancel up to the
constant `-2i` coming from the factor `e^{-2iζ}`. -/
theorem contour_logDerivTheta1 {a : ℂ}
    (hbd : ∀ z ∈ paraBoundary a π (π * tau), jacobiTheta1 z ≠ 0) :
    paraContour a π (π * tau) logDerivTheta1 = 2 * π * I := by
  set φ : ℝ → ℂ := fun t => logDerivTheta1 (a + t * π) with hφ
  set ψ : ℝ → ℂ := fun t => logDerivTheta1 (a + t * (π * tau)) with hψ
  have bot : ∀ t ∈ Icc (0 : ℝ) 1, a + t * π ∈ paraBoundary a π (π * tau) := fun t ht =>
    ⟨t, ht, 0, left_mem_Icc.mpr zero_le_one, Or.inr (Or.inr (Or.inl rfl)), by simp⟩
  have hφc : ContinuousOn φ (Icc 0 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_logDerivTheta1 (hbd _ (bot t ht))).comp
      (f := fun t : ℝ => a + (t : ℂ) * π) (by fun_prop)
  have hφi : IntervalIntegrable φ volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; rwa [uIcc_of_le zero_le_one]
  have rev : ∀ F : ℝ → ℂ, ∫ t in (0 : ℝ)..1, F (1 - t) = ∫ t in (0 : ℝ)..1, F t := by
    intro F; rw [intervalIntegral.integral_comp_sub_left]; simp
  have h1 : segInt logDerivTheta1 a (a + π) = (∫ t in (0 : ℝ)..1, φ t) * π := by
    unfold segInt; simp only [add_sub_cancel_left]
    rw [intervalIntegral.integral_mul_const]
  have h2 : segInt logDerivTheta1 (a + π) (a + π + π * tau) =
      (∫ t in (0 : ℝ)..1, ψ t) * (π * tau) := by
    unfold segInt; simp only [add_sub_cancel_left]
    rw [← intervalIntegral.integral_mul_const]
    congr 1; funext t
    simp only [hψ]
    rw [show a + π + (t : ℂ) * (π * tau) = (a + t * (π * tau)) + π by ring,
      logDerivTheta1_add_pi]
  have h3 : segInt logDerivTheta1 (a + π + π * tau) (a + π * tau) =
      ((∫ t in (0 : ℝ)..1, φ t) - 2 * I) * (-π) := by
    unfold segInt
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => (φ (1 - t) - 2 * I) * (-π))]
    · rw [rev (fun t => (φ t - 2 * I) * (-π)), intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub hφi intervalIntegrable_const]
      simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have ht' : (1 - t) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simp only [hφ]
      rw [← logDerivTheta1_add_pi_tau (hbd _ (bot _ ht'))]
      congr 1
      · congr 1; push_cast; ring
      · ring
  have h4 : segInt logDerivTheta1 (a + π * tau) a = (∫ t in (0 : ℝ)..1, ψ t) * (-(π * tau)) := by
    unfold segInt
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => ψ (1 - t) * (-(π * tau)))]
    · rw [rev (fun t => ψ t * (-(π * tau))), intervalIntegral.integral_mul_const]
    · intro t _
      simp only [hψ]
      congr 1
      · congr 1; push_cast; ring
      · ring
  unfold paraContour
  rw [h1, h2, h3, h4]
  ring

/-! ## Zeros of `θ₁` -/

lemma analyticOrderAt_jacobiTheta1_ne_top (u : ℂ) : analyticOrderAt jacobiTheta1 u ≠ ⊤ := by
  have hfa : AnalyticOnNhd ℂ jacobiTheta1 univ := fun z _ =>
    differentiable_jacobiTheta1.analyticAt z
  apply hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ zetaNZ)
    (mem_univ u)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr jacobiTheta1_zetaNZ)]
  exact ENat.zero_ne_top

lemma analyticOrderNatAt_jacobiTheta1_pos {b : ℂ} (hb : jacobiTheta1 b = 0) :
    0 < analyticOrderNatAt jacobiTheta1 b := by
  have hord := analyticOrderAt_jacobiTheta1_ne_top b
  have hpos : analyticOrderAt jacobiTheta1 b ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]; push Not
    exact ⟨differentiable_jacobiTheta1.analyticAt b, hb⟩
  rw [Nat.pos_iff_ne_zero]
  intro h0; apply hpos; rw [← Nat.cast_analyticOrderNatAt hord, h0]; rfl

lemma deriv_ne_zero_of_order_one {b : ℂ} (h1 : analyticOrderNatAt jacobiTheta1 b = 1) :
    dTheta1 b ≠ 0 := by
  intro hd
  have hord := analyticOrderAt_jacobiTheta1_ne_top b
  have hb : jacobiTheta1 b = 0 := by
    by_contra hne
    have : analyticOrderAt jacobiTheta1 b = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hne)
    rw [← Nat.cast_analyticOrderNatAt hord, h1] at this
    simp at this
  have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt jacobiTheta1 b := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (differentiable_jacobiTheta1.analyticAt b)]
    intro i hi
    interval_cases i
    · simpa using hb
    · simpa [iteratedDeriv_one, dTheta1] using hd
  rw [← Nat.cast_analyticOrderNatAt hord, h1] at h2
  exact absurd (by exact_mod_cast h2 : (2 : ℕ) ≤ 1) (by norm_num)

/-- The zeros of `θ₁` in a ball form a finite set. -/
lemma finite_zeros_ball (c : ℂ) (r : ℝ) :
    {z ∈ Metric.ball c r | jacobiTheta1 z = 0}.Finite := by
  have hf := differentiable_jacobiTheta1
  set U := Metric.ball c r
  have hmero : MeromorphicOn jacobiTheta1 U := fun z _ => (hf.analyticAt z).meromorphicAt
  have hfin : (MeromorphicOn.divisor jacobiTheta1 U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite (fun z _ => (hf.analyticAt z).meromorphicAt)
  apply hfin.subset
  rintro b ⟨hbU, hb0⟩
  have hord := analyticOrderAt_jacobiTheta1_ne_top b
  rw [Function.mem_support, MeromorphicOn.divisor_apply hmero hbU,
    (hf.analyticAt b).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hord]
  have := (analyticOrderNatAt_jacobiTheta1_pos hb0).ne'
  simpa using this

/-- Real coordinates with respect to the basis `(π, πτ)`. -/
def coordY (z : ℂ) : ℝ := z.im / (π * tau.im)
/-- Real coordinates with respect to the basis `(π, πτ)`. -/
def coordX (z : ℂ) : ℝ := (z.re - coordY z * π * tau.re) / π

lemma coord_mk (x y : ℝ) :
    coordX (x * π + y * (π * tau)) = x ∧ coordY (x * π + y * (π * tau)) = y := by
  have hπ := Real.pi_pos
  have ht := tau_im_pos
  have hY : coordY (x * π + y * (π * tau)) = y := by
    unfold coordY
    simp only [add_im, mul_re, mul_im, ofReal_re, ofReal_im]
    field_simp; ring
  refine ⟨?_, hY⟩
  unfold coordX; rw [hY]
  simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im]
  field_simp; ring

lemma coord_decomp (z : ℂ) : z = coordX z * π + coordY z * (π * tau) := by
  have hπ := Real.pi_pos
  have ht := tau_im_pos
  apply Complex.ext <;>
    simp only [coordX, coordY, add_re, add_im, mul_re, mul_im,
      ofReal_re, ofReal_im] <;> field_simp <;> ring

/-- For every `p` there is a translate of the period parallelogram, containing `p` in its
interior, whose boundary avoids the zeros of `θ₁`. -/
theorem exists_good_parallelogram (p : ℂ) : ∃ s₀ ∈ Ioo (0 : ℝ) 1,
    ∀ z ∈ SymplecticPacking.Complex.paraBoundary (p - s₀ * (π + π * tau)) π (π * tau),
      jacobiTheta1 z ≠ 0 := by
  set R : ℝ := π + π * ‖tau‖ + 1
  have hZ := finite_zeros_ball p R
  set B : Set ℝ := ⋃ z ∈ {z ∈ Metric.ball p R | jacobiTheta1 z = 0},
    ({-coordX (z - p), 1 - coordX (z - p), -coordY (z - p), 1 - coordY (z - p)} : Set ℝ)
  have hB : B.Finite := hZ.biUnion fun _ _ => toFinite _
  obtain ⟨s₀, hs₀, hs₀B⟩ := ((Set.Ioo_infinite (zero_lt_one' ℝ)).sdiff hB).nonempty
  refine ⟨s₀, hs₀, ?_⟩
  rintro z ⟨s, hs, t, ht, hst, rfl⟩ h0
  apply hs₀B
  have hzp : p - s₀ * (π + π * tau) + s * π + t * (π * tau) - p =
      ((s - s₀ : ℝ) : ℂ) * π + ((t - s₀ : ℝ) : ℂ) * (π * tau) := by push_cast; ring
  have hmem : p - s₀ * (π + π * tau) + s * π + t * (π * tau) ∈
      {z ∈ Metric.ball p R | jacobiTheta1 z = 0} := by
    refine ⟨?_, h0⟩
    rw [Metric.mem_ball, dist_eq_norm, hzp]
    have h1 : |s - s₀| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, hs₀.2], by linarith [hs.2, hs₀.1]⟩
    have h2 : |t - s₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, hs₀.2], by linarith [ht.2, hs₀.1]⟩
    calc ‖((s - s₀ : ℝ) : ℂ) * π + ((t - s₀ : ℝ) : ℂ) * (π * tau)‖
        ≤ ‖((s - s₀ : ℝ) : ℂ) * π‖ + ‖((t - s₀ : ℝ) : ℂ) * (π * tau)‖ := norm_add_le _ _
      _ = |s - s₀| * π + |t - s₀| * (π * ‖tau‖) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
      _ ≤ 1 * π + 1 * (π * ‖tau‖) := by
          gcongr
      _ < R := by simp only [R]; linarith
  simp only [B, mem_iUnion]
  refine ⟨_, hmem, ?_⟩
  obtain ⟨cx, cy⟩ := coord_mk (s - s₀) (t - s₀)
  rw [hzp, cx, cy]
  simp only [mem_insert_iff, mem_singleton_iff]
  rcases hst with h | h | h | h <;> subst h
  · left; ring
  · right; left; ring
  · right; right; left; ring
  · right; right; right; ring

open SymplecticPacking.Complex in
/-- In a period parallelogram whose boundary avoids the zeros, `θ₁` has exactly one zero
counted with multiplicity. -/
theorem count_zeros_jacobiTheta1 {a : ℂ}
    (hbd : ∀ z ∈ paraBoundary a π (π * tau), jacobiTheta1 z ≠ 0) :
    ∑ᶠ b ∈ paraInterior a π (π * tau), (analyticOrderNatAt jacobiTheta1 b : ℂ) = 1 := by
  have hω : 0 < ((π * tau) / (π : ℂ)).im := by
    rw [mul_div_cancel_left₀ _ pi_ne_zero']; exact tau_im_pos
  rw [← argument_principle hω differentiable_jacobiTheta1 hbd]
  have : paraContour a π (π * tau) (fun z => deriv jacobiTheta1 z / jacobiTheta1 z) =
      2 * π * I := contour_logDerivTheta1 hbd
  rw [this, inv_mul_cancel₀ two_pi_I_ne_zero]

open SymplecticPacking.Complex in
/-- Consequently a zero in the interior is simple and is the only zero in the interior. -/
theorem unique_zero_jacobiTheta1 {a p : ℂ}
    (hbd : ∀ z ∈ paraBoundary a π (π * tau), jacobiTheta1 z ≠ 0)
    (hp : p ∈ paraInterior a π (π * tau)) (hp0 : jacobiTheta1 p = 0) :
    analyticOrderNatAt jacobiTheta1 p = 1 ∧
      ∀ b ∈ paraInterior a π (π * tau), jacobiTheta1 b = 0 → b = p := by
  classical
  set I' := paraInterior a π (π * tau)
  set S := {b ∈ I' | jacobiTheta1 b = 0}
  have hS : S.Finite := finite_zeros_paraInterior differentiable_jacobiTheta1 hbd
  set ord := fun b => analyticOrderNatAt jacobiTheta1 b
  have hsupp : ∀ b, ord b ≠ 0 → jacobiTheta1 b = 0 := by
    intro b hb
    by_contra hne
    apply hb
    have : analyticOrderAt jacobiTheta1 b = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hne)
    simp [ord, analyticOrderNatAt, this]
  have hsum : ∑ b ∈ hS.toFinset, ord b = 1 := by
    have h := count_zeros_jacobiTheta1 hbd
    rw [finsum_mem_eq_sum_of_inter_support_eq (s := I') (t := hS.toFinset)] at h
    · exact_mod_cast h
    · ext b
      simp only [mem_inter_iff, Function.mem_support, Finite.coe_toFinset, S, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, hne⟩; exact ⟨⟨hb, hsupp b (by exact_mod_cast hne)⟩, hne⟩
      · rintro ⟨⟨hb, -⟩, hne⟩; exact ⟨hb, hne⟩
  have hpS : p ∈ hS.toFinset := by simp [S, hp, hp0]
  have hpos : ∀ b ∈ hS.toFinset, 0 < ord b := by
    intro b hb
    simp only [Finite.mem_toFinset, S, mem_ofPred_eq] at hb
    exact analyticOrderNatAt_jacobiTheta1_pos hb.2
  have hp1 : ord p ≤ 1 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hpS
  refine ⟨le_antisymm hp1 (hpos p hpS), ?_⟩
  intro b hb hb0
  by_contra hne
  have hbS : b ∈ hS.toFinset := by simp [S, hb, hb0]
  have h2 : ∑ x ∈ {p, b}, ord x ≤ ∑ x ∈ hS.toFinset, ord x :=
    Finset.sum_le_sum_of_subset (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
  rw [Finset.sum_pair (Ne.symm hne), hsum] at h2
  have := hpos p hpS
  have := hpos b hbS
  omega

/-- **All zeros of `θ₁` are simple.** -/
theorem dTheta1_ne_zero_of_eq_zero {p : ℂ} (hp0 : jacobiTheta1 p = 0) : dTheta1 p ≠ 0 := by
  obtain ⟨s₀, hs₀, hbd⟩ := exists_good_parallelogram p
  have hp : p ∈ SymplecticPacking.Complex.paraInterior (p - s₀ * (π + π * tau)) π (π * tau) :=
    ⟨s₀, hs₀, s₀, hs₀, by ring⟩
  exact deriv_ne_zero_of_order_one (unique_zero_jacobiTheta1 hbd hp hp0).1

/-- `θ₁'(0) ≠ 0`. -/
theorem dTheta1_zero_ne_zero : dTheta1 0 ≠ 0 := dTheta1_ne_zero_of_eq_zero jacobiTheta1_zero

/-- The zero set of `z ↦ θ₁(πz)` is invariant under the lattice. -/
lemma jacobiTheta1_pi_mul_add_lattice {l : ℂ} (hl : l ∈ hexPair.lattice) (z : ℂ) :
    (jacobiTheta1 (π * (z + l)) = 0) = (jacobiTheta1 (π * z) = 0) := by
  refine periodic_lattice (F := fun z => jacobiTheta1 (π * z) = 0) ?_ ?_ hl z
  · intro z
    simp only [mul_add, mul_one, jacobiTheta1_add_pi, neg_eq_zero]
  · intro z
    simp only [mul_add, jacobiTheta1_add_pi_tau, mul_eq_zero, thetaFactor_ne_zero, false_or]

/-- **Zeros of `θ₁`**: `θ₁(πz) = 0 ↔ z ∈ ℤ + ℤτ`. -/
theorem jacobiTheta1_pi_mul_eq_zero_iff (z : ℂ) :
    jacobiTheta1 (π * z) = 0 ↔ z ∈ hexPair.lattice := by
  constructor
  · intro hz
    obtain ⟨s₀, hs₀, hbd⟩ := exists_good_parallelogram 0
    set a := (0 : ℂ) - s₀ * (π + π * tau)
    have h0I : (0 : ℂ) ∈ SymplecticPacking.Complex.paraInterior a π (π * tau) :=
      ⟨s₀, hs₀, s₀, hs₀, by simp only [a]; ring⟩
    have huniq := (unique_zero_jacobiTheta1 hbd h0I jacobiTheta1_zero).2
    set ζ₀ := π * z
    set m := ⌊coordX ζ₀ + s₀⌋
    set n := ⌊coordY ζ₀ + s₀⌋
    have hl : -((m : ℂ) + n * tau) ∈ hexPair.lattice :=
      Submodule.neg_mem _ ((mem_lattice_iff _).mpr ⟨m, n, rfl⟩)
    have hz1 : jacobiTheta1 (π * (z + -((m : ℂ) + n * tau))) = 0 := by
      rw [jacobiTheta1_pi_mul_add_lattice hl]; exact hz
    have hdec : π * (z + -((m : ℂ) + n * tau)) =
        a + (Int.fract (coordX ζ₀ + s₀) : ℝ) * π + (Int.fract (coordY ζ₀ + s₀) : ℝ) * (π * tau) := by
      rw [Int.fract, Int.fract]
      have := coord_decomp ζ₀
      simp only [a]; push_cast
      simp only [ζ₀] at this
      linear_combination this
    have hset : π * (z + -((m : ℂ) + n * tau)) ∈
        SymplecticPacking.Complex.paraSet a π (π * tau) := by
      rw [hdec]
      exact ⟨_, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, _,
        ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩
    have hint := SymplecticPacking.Complex.mem_paraInterior_of_not_boundary hset
      (fun hb => hbd _ hb hz1)
    have h00 := huniq _ hint hz1
    rw [mul_eq_zero] at h00
    rcases h00 with h | h
    · exact absurd h pi_ne_zero'
    · rw [add_neg_eq_zero] at h
      rw [h]; exact (mem_lattice_iff _).mpr ⟨m, n, rfl⟩
  · intro hz
    have := jacobiTheta1_pi_mul_add_lattice hz 0
    rw [zero_add, mul_zero] at this
    rw [this]; exact jacobiTheta1_zero

/-! ## `℘ = -π² (θ₁'/θ₁)'(πz) + c₀` -/

/-- `r_ϑ = θ₁'''(0) / (3 θ₁'(0))`. -/
def rTheta : ℂ := d3Theta1 0 / (3 * dTheta1 0)

/-- The constant `c₀ = π² r_ϑ` (the paper's `a_ϑ r_ϑ` with `L = 1`). -/
def wpConst : ℂ := π ^ 2 * rTheta

/-- `N = θ₁'² - θ₁ θ₁'' = -θ₁² (θ₁'/θ₁)'`. -/
def NTheta (ζ : ℂ) : ℂ := dTheta1 ζ ^ 2 - jacobiTheta1 ζ * d2Theta1 ζ

lemma differentiable_NTheta : Differentiable ℂ NTheta := by
  unfold NTheta
  have := differentiable_dTheta1; have := differentiable_d2Theta1
  have := differentiable_jacobiTheta1
  fun_prop

lemma NTheta_add_pi (ζ : ℂ) : NTheta (ζ + π) = NTheta ζ := by
  simp only [NTheta, dTheta1_add_pi, jacobiTheta1_add_pi, d2Theta1_add_pi]; ring

lemma NTheta_add_pi_tau (ζ : ℂ) : NTheta (ζ + π * tau) = thetaFactor ζ ^ 2 * NTheta ζ := by
  simp only [NTheta, dTheta1_add_pi_tau, jacobiTheta1_add_pi_tau, d2Theta1_add_pi_tau]
  ring_nf; rw [I_sq]; ring

/-- `z ↦ N(πz)/θ₁(πz)²` (junk `0` on the lattice). -/
def wpTheta (z : ℂ) : ℂ := NTheta (π * z) / jacobiTheta1 (π * z) ^ 2

lemma wpTheta_add_one (z : ℂ) : wpTheta (z + 1) = wpTheta z := by
  simp only [wpTheta, mul_add, mul_one, NTheta_add_pi, jacobiTheta1_add_pi, neg_sq]

lemma wpTheta_add_tau (z : ℂ) : wpTheta (z + tau) = wpTheta z := by
  simp only [wpTheta, mul_add, NTheta_add_pi_tau, jacobiTheta1_add_pi_tau, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (thetaFactor_ne_zero _))

/-! ### Local structure at `0`: `θ₁(ζ) = ζ g(ζ)` -/

/-- `g = θ₁(ζ)/ζ`, extended by `θ₁'(0)`. -/
def gTheta : ℂ → ℂ := dslope jacobiTheta1 0

lemma differentiable_gTheta : Differentiable ℂ gTheta := by
  have := (Complex.differentiableOn_dslope (f := jacobiTheta1) (s := univ) (c := 0)
    Filter.univ_mem).mpr differentiable_jacobiTheta1.differentiableOn
  exact fun z => (this z (mem_univ z)).differentiableAt (Filter.univ_mem)

lemma jacobiTheta1_eq_mul_gTheta : jacobiTheta1 = fun ζ => ζ * gTheta ζ := by
  funext ζ
  have := sub_smul_dslope jacobiTheta1 0 ζ
  rw [jacobiTheta1_zero, sub_zero, sub_zero, smul_eq_mul] at this
  exact this.symm

lemma gTheta_zero : gTheta 0 = dTheta1 0 := dslope_same _ _

lemma differentiable_dgTheta : Differentiable ℂ (deriv gTheta) := differentiable_gTheta.deriv
lemma differentiable_d2gTheta : Differentiable ℂ (deriv (deriv gTheta)) :=
  differentiable_dgTheta.deriv

lemma dTheta1_eq_g : dTheta1 = fun ζ => gTheta ζ + ζ * deriv gTheta ζ := by
  funext ζ
  have h : HasDerivAt (fun ζ => ζ * gTheta ζ) (1 * gTheta ζ + ζ * deriv gTheta ζ) ζ :=
    (hasDerivAt_id ζ).mul (differentiable_gTheta ζ).hasDerivAt
  rw [dTheta1, jacobiTheta1_eq_mul_gTheta, h.deriv, one_mul]

lemma d2Theta1_eq_g : d2Theta1 = fun ζ => 2 * deriv gTheta ζ + ζ * deriv (deriv gTheta) ζ := by
  funext ζ
  have h : HasDerivAt (fun ζ => gTheta ζ + ζ * deriv gTheta ζ)
      (deriv gTheta ζ + (1 * deriv gTheta ζ + ζ * deriv (deriv gTheta) ζ)) ζ :=
    (differentiable_gTheta ζ).hasDerivAt.add
      ((hasDerivAt_id ζ).mul (differentiable_dgTheta ζ).hasDerivAt)
  rw [d2Theta1, dTheta1_eq_g, h.deriv]; ring

lemma d3Theta1_eq_g : d3Theta1 = fun ζ =>
    3 * deriv (deriv gTheta) ζ + ζ * deriv (deriv (deriv gTheta)) ζ := by
  funext ζ
  have h : HasDerivAt (fun ζ => 2 * deriv gTheta ζ + ζ * deriv (deriv gTheta) ζ)
      (2 * deriv (deriv gTheta) ζ +
        (1 * deriv (deriv gTheta) ζ + ζ * deriv (deriv (deriv gTheta)) ζ)) ζ :=
    ((differentiable_dgTheta ζ).hasDerivAt.const_mul 2).add
      ((hasDerivAt_id ζ).mul (differentiable_d2gTheta ζ).hasDerivAt)
  rw [d3Theta1, d2Theta1_eq_g, h.deriv]; ring

lemma gTheta_zero_ne : gTheta 0 ≠ 0 := gTheta_zero ▸ dTheta1_zero_ne_zero

lemma dgTheta_zero : deriv gTheta 0 = 0 := by
  have := congrFun d2Theta1_eq_g 0
  rw [d2Theta1_zero] at this; simpa using this.symm

lemma d2gTheta_zero : deriv (deriv gTheta) 0 = d3Theta1 0 / 3 := by
  have := congrFun d3Theta1_eq_g 0
  simp at this; rw [this]; ring

/-- `G = (g'' g - g'²)/g² = (g'/g)'`. -/
def GTheta (ζ : ℂ) : ℂ :=
  (deriv (deriv gTheta) ζ * gTheta ζ - deriv gTheta ζ ^ 2) / gTheta ζ ^ 2

lemma GTheta_zero : GTheta 0 = rTheta := by
  rw [GTheta, dgTheta_zero, d2gTheta_zero, rTheta, ← gTheta_zero]
  have := gTheta_zero_ne
  field_simp
  ring

lemma NTheta_div_eq {ζ : ℂ} (hζ : ζ ≠ 0) (hg : gTheta ζ ≠ 0) :
    NTheta ζ / jacobiTheta1 ζ ^ 2 = 1 / ζ ^ 2 - GTheta ζ := by
  rw [NTheta, GTheta, congrFun dTheta1_eq_g ζ, congrFun d2Theta1_eq_g ζ,
    congrFun jacobiTheta1_eq_mul_gTheta ζ]
  field_simp
  ring

/-- The difference `℘(z) - π² N(πz)/θ₁(πz)²`, extended by `c₀` on the lattice. -/
def wpDiff (z : ℂ) : ℂ := by
  classical
  exact if z ∈ hexPair.lattice then wpConst else ℘[hexPair] z - π ^ 2 * wpTheta z

lemma wpDiff_add_lattice {l : ℂ} (hl : l ∈ hexPair.lattice) (z : ℂ) :
    wpDiff (z + l) = wpDiff z := by
  have hmem : (z + l ∈ hexPair.lattice) ↔ z ∈ hexPair.lattice :=
    hexPair.lattice.toAddSubgroup.add_mem_cancel_right hl
  have hwp : ℘[hexPair] (z + l) = ℘[hexPair] z := hexPair.weierstrassP_add_coe z ⟨l, hl⟩
  have hth : wpTheta (z + l) = wpTheta z := periodic_lattice wpTheta_add_one wpTheta_add_tau hl z
  unfold wpDiff
  by_cases hz : z ∈ hexPair.lattice
  · simp only [hz, hmem.mpr hz, ite_true]
  · simp only [hz, mt hmem.mp hz, ite_false, hwp, hth]

lemma analyticAt_wpDiff_zero : AnalyticAt ℂ wpDiff 0 := by
  have hgc : ContinuousAt (fun z : ℂ => gTheta (π * z)) 0 :=
    (differentiable_gTheta.comp (differentiable_id.const_mul _)).continuous.continuousAt
  have hg0 : ∀ᶠ z in 𝓝 (0 : ℂ), gTheta (π * z) ≠ 0 := by
    apply hgc.eventually_ne; simpa using gTheta_zero_ne
  have hG : AnalyticAt ℂ (fun z => GTheta (π * z)) 0 := by
    have ha : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → AnalyticAt ℂ (fun z => f (π * z)) 0 :=
      fun hf => (hf.comp (differentiable_id.const_mul _)).analyticAt 0
    unfold GTheta
    apply AnalyticAt.div
    · exact ((ha differentiable_d2gTheta).mul (ha differentiable_gTheta)).sub
        ((ha differentiable_dgTheta).pow 2)
    · exact (ha differentiable_gTheta).pow 2
    · simpa using pow_ne_zero 2 gTheta_zero_ne
  have hE : AnalyticAt ℂ (hexPair.weierstrassPExcept 0) 0 :=
    hexPair.analyticAt_weierstrassPExcept 0
  have hc : AnalyticAt ℂ (fun _ : ℂ => (π : ℂ) ^ 2) 0 := analyticAt_const
  refine (hE.add (hc.mul hG)).congr ?_
  filter_upwards [eventually_lattice_eq_zero, hg0] with z hzL hgz
  by_cases hz : z = 0
  · subst hz
    simp only [wpDiff, Submodule.zero_mem, ite_true, Pi.add_apply, Pi.mul_apply, wpExcept_zero,
      mul_zero, GTheta_zero, zero_add, wpConst]
  · have hzL' : z ∉ hexPair.lattice := fun h => hz (hzL h)
    simp only [wpDiff, hzL', ite_false, wpTheta, Pi.add_apply, Pi.mul_apply]
    have hπz : (π : ℂ) * z ≠ 0 := mul_ne_zero pi_ne_zero' hz
    rw [NTheta_div_eq hπz hgz, wp_eq_except]
    field_simp
    ring

lemma analyticAt_wpDiff (z : ℂ) : AnalyticAt ℂ wpDiff z := by
  by_cases hz : z ∈ hexPair.lattice
  · have h0 := analyticAt_wpDiff_zero
    have hcomp : AnalyticAt ℂ (fun w => wpDiff (w - z)) z := by
      have : AnalyticAt ℂ (fun w : ℂ => w - z) z := by fun_prop
      exact h0.comp_of_eq this (by simp)
    refine hcomp.congr (Eventually.of_forall fun w => ?_)
    have := wpDiff_add_lattice (Submodule.neg_mem _ hz) w
    simpa [sub_eq_add_neg] using this
  · have hθ : ∀ w, w ∉ hexPair.lattice → jacobiTheta1 (π * w) ≠ 0 := fun w hw h =>
      hw ((jacobiTheta1_pi_mul_eq_zero_iff w).mp h)
    have hwp : AnalyticAt ℂ ℘[hexPair] z := wp_analyticOnNhd z hz
    have ha : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → AnalyticAt ℂ (fun w => f (π * w)) z :=
      fun hf => (hf.comp (differentiable_id.const_mul _)).analyticAt z
    have hq : AnalyticAt ℂ wpTheta z :=
      (ha differentiable_NTheta).div ((ha differentiable_jacobiTheta1).pow 2)
        (pow_ne_zero 2 (hθ z hz))
    have hc : AnalyticAt ℂ (fun _ : ℂ => (π : ℂ) ^ 2) z := analyticAt_const
    refine (hwp.sub (hc.mul hq)).congr ?_
    filter_upwards [hex_isOpen_compl.mem_nhds hz] with w hw
    have hw' : w ∉ hexPair.lattice := hw
    simp [wpDiff, hw']

theorem wpDiff_eq_const (z : ℂ) : wpDiff z = wpConst := by
  have hd : Differentiable ℂ wpDiff := fun z => (analyticAt_wpDiff z).differentiableAt
  have := hd.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic hexPair.lattice _
    hd.continuous fun z w hw => wpDiff_add_lattice hw z).isBounded z 0
  rw [this]; simp [wpDiff]

/-- **`℘ = π² (θ₁'² - θ₁θ₁'')/θ₁² (πz) + c₀`** off the lattice. -/
theorem wp_eq_theta {z : ℂ} (hz : z ∉ hexPair.lattice) :
    ℘[hexPair] z = π ^ 2 * (NTheta (π * z) / jacobiTheta1 (π * z) ^ 2) + wpConst := by
  have := wpDiff_eq_const z
  simp only [wpDiff, hz, ite_false, wpTheta] at this
  linear_combination this

/-- `Q = -θ₁'''θ₁² + 3θ₁'θ₁''θ₁ - 2θ₁'³`. -/
def QTheta (ζ : ℂ) : ℂ :=
  -d3Theta1 ζ * jacobiTheta1 ζ ^ 2 + 3 * dTheta1 ζ * d2Theta1 ζ * jacobiTheta1 ζ -
    2 * dTheta1 ζ ^ 3

/-- **`℘'(z) = π³ Q(πz)/θ₁(πz)³`** off the lattice. -/
theorem dwp_eq_theta {z : ℂ} (hz : z ∉ hexPair.lattice) :
    ℘'[hexPair] z = π ^ 3 * (QTheta (π * z) / jacobiTheta1 (π * z) ^ 3) := by
  have hθ : jacobiTheta1 (π * z) ≠ 0 := fun h => hz ((jacobiTheta1_pi_mul_eq_zero_iff z).mp h)
  have hev : ℘[hexPair] =ᶠ[𝓝 z]
      fun w => π ^ 2 * (NTheta (π * w) / jacobiTheta1 (π * w) ^ 2) + wpConst := by
    filter_upwards [hex_isOpen_compl.mem_nhds hz] with w hw using wp_eq_theta hw
  have hlin : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hN : HasDerivAt (fun w => NTheta (π * w))
      ((2 * dTheta1 (π * z) * d2Theta1 (π * z) -
        (dTheta1 (π * z) * d2Theta1 (π * z) + jacobiTheta1 (π * z) * d3Theta1 (π * z))) * π) z := by
    have h1 : HasDerivAt NTheta
        (2 * dTheta1 (π * z) * d2Theta1 (π * z) -
          (dTheta1 (π * z) * d2Theta1 (π * z) + jacobiTheta1 (π * z) * d3Theta1 (π * z)))
        (π * z) := by
      have := ((differentiable_dTheta1 (π * z)).hasDerivAt.pow 2).sub
        ((differentiable_jacobiTheta1 (π * z)).hasDerivAt.mul
          (differentiable_d2Theta1 (π * z)).hasDerivAt)
      have e : NTheta = dTheta1 ^ 2 - jacobiTheta1 * d2Theta1 := by
        funext ζ; simp [NTheta]
      rw [e]
      convert this using 1
      rw [show deriv dTheta1 = d2Theta1 from rfl, show deriv d2Theta1 = d3Theta1 from rfl,
        show deriv jacobiTheta1 = dTheta1 from rfl]
      norm_num
    exact h1.comp z hlin
  have hT : HasDerivAt (fun w => jacobiTheta1 (π * w) ^ 2)
      (2 * jacobiTheta1 (π * z) * (dTheta1 (π * z) * π)) z := by
    have : HasDerivAt (fun w => jacobiTheta1 (π * w) ^ 2)
        ((2 : ℕ) * jacobiTheta1 (π * z) ^ (2 - 1) * (deriv jacobiTheta1 (π * z) * π)) z :=
      ((differentiable_jacobiTheta1 (π * z)).hasDerivAt.comp z hlin).pow 2
    convert this using 1
    rw [show deriv jacobiTheta1 = dTheta1 from rfl]
    norm_num
  have hall : HasDerivAt
      (fun w => π ^ 2 * (NTheta (π * w) / jacobiTheta1 (π * w) ^ 2) + wpConst) _ z :=
    ((hN.div hT (pow_ne_zero 2 hθ)).const_mul ((π : ℂ) ^ 2)).add_const wpConst
  rw [← deriv_weierstrassP, hev.deriv_eq, hall.deriv, QTheta, NTheta]
  field_simp
  ring

/-! ## The theta lift `Zraw` -/

/-- `P = θ₁'² θ₁ - θ₁'' θ₁² + r_ϑ θ₁³`. -/
def PTheta (ζ : ℂ) : ℂ :=
  dTheta1 ζ ^ 2 * jacobiTheta1 ζ - d2Theta1 ζ * jacobiTheta1 ζ ^ 2 + rTheta * jacobiTheta1 ζ ^ 3

/-- **The theta lift** (Lean normalisation, `ζ = πz`):
`Zraw = (2 cF π² P, -θ³ - dF π³ Q, -θ³ + dF π³ Q)`. -/
def Zraw (z : ℂ) : Fin 3 → ℂ :=
  ![2 * cF * π ^ 2 * PTheta (π * z),
    -jacobiTheta1 (π * z) ^ 3 - dF * π ^ 3 * QTheta (π * z),
    -jacobiTheta1 (π * z) ^ 3 + dF * π ^ 3 * QTheta (π * z)]

/-- **`Zraw = θ³ · torusLift`** wherever `θ₁(πz) ≠ 0` (i.e. `z ∉ ℤ + ℤτ`). -/
theorem Zraw_eq {z : ℂ} (hθ : jacobiTheta1 (π * z) ≠ 0) :
    Zraw z = jacobiTheta1 (π * z) ^ 3 • torusLift z := by
  have hz : z ∉ hexPair.lattice := fun h => hθ ((jacobiTheta1_pi_mul_eq_zero_iff z).mpr h)
  have hP := wp_eq_theta hz
  have hQ := dwp_eq_theta hz
  ext i
  fin_cases i <;> simp only [Zraw, torusLift, Pi.smul_apply, smul_eq_mul] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    simp only [hP, hQ, PTheta, NTheta, wpConst] <;> field_simp <;> ring

/-- **`Zraw` has no zero.** -/
theorem Zraw_ne_zero (z : ℂ) : Zraw z ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Zraw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h1 h2
  by_cases hθ : jacobiTheta1 (π * z) = 0
  · have hd := dTheta1_ne_zero_of_eq_zero hθ
    rw [QTheta, hθ] at h1
    have : dF * π ^ 3 * (2 * dTheta1 (π * z) ^ 3) = 0 := by linear_combination h1
    simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      dF_ne_zero, pi_ne_zero', hd, or_self] at this
  · have : 2 * jacobiTheta1 (π * z) ^ 3 = 0 := by linear_combination -h1 - h2
    simp [hθ] at this

lemma PTheta_add_pi (ζ : ℂ) : PTheta (ζ + π) = -PTheta ζ := by
  simp only [PTheta, dTheta1_add_pi, jacobiTheta1_add_pi, d2Theta1_add_pi]; ring

lemma QTheta_add_pi (ζ : ℂ) : QTheta (ζ + π) = -QTheta ζ := by
  simp only [QTheta, dTheta1_add_pi, jacobiTheta1_add_pi, d2Theta1_add_pi, d3Theta1_add_pi]; ring

lemma PTheta_add_pi_tau (ζ : ℂ) : PTheta (ζ + π * tau) = thetaFactor ζ ^ 3 * PTheta ζ := by
  simp only [PTheta, dTheta1_add_pi_tau, jacobiTheta1_add_pi_tau, d2Theta1_add_pi_tau]
  linear_combination (thetaFactor ζ ^ 3 * 4 * jacobiTheta1 ζ ^ 3) * I_sq

lemma QTheta_add_pi_tau (ζ : ℂ) : QTheta (ζ + π * tau) = thetaFactor ζ ^ 3 * QTheta ζ := by
  simp only [QTheta, dTheta1_add_pi_tau, jacobiTheta1_add_pi_tau, d2Theta1_add_pi_tau,
    d3Theta1_add_pi_tau]
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  linear_combination (16 * thetaFactor ζ ^ 3 * jacobiTheta1 ζ ^ 3) * h3

/-- **Automorphy under `z ↦ z + 1`**: factor `-1`. -/
theorem Zraw_add_one (z : ℂ) : Zraw (z + 1) = (-1 : ℂ) • Zraw z := by
  have e : (π : ℂ) * (z + 1) = π * z + π := by ring
  ext i
  fin_cases i <;>
    simp [Zraw, e, PTheta_add_pi, QTheta_add_pi, jacobiTheta1_add_pi] <;> ring

/-- **Automorphy under `z ↦ z + τ`**: factor `e(πz)³ = (-e^{-iπτ} e^{-2iπz})³`. -/
theorem Zraw_add_tau (z : ℂ) : Zraw (z + tau) = thetaFactor (π * z) ^ 3 • Zraw z := by
  have e : (π : ℂ) * (z + tau) = π * z + π * tau := by ring
  ext i
  fin_cases i <;>
    simp [Zraw, e, PTheta_add_pi_tau, QTheta_add_pi_tau, jacobiTheta1_add_pi_tau] <;> ring

/-- The automorphy factors are nowhere zero. -/
theorem Zraw_automorphy (z : ℂ) :
    Zraw (z + 1) = (-1 : ℂ) • Zraw z ∧ Zraw (z + tau) = thetaFactor (π * z) ^ 3 • Zraw z ∧
      thetaFactor (π * z) ^ 3 ≠ 0 :=
  ⟨Zraw_add_one z, Zraw_add_tau z, pow_ne_zero 3 (thetaFactor_ne_zero _)⟩

theorem differentiable_Zraw : Differentiable ℂ Zraw := by
  have h1 := differentiable_jacobiTheta1; have h2 := differentiable_dTheta1
  have h3 := differentiable_d2Theta1; have h4 := differentiable_d3Theta1
  have hl : Differentiable ℂ (fun z : ℂ => (π : ℂ) * z) := differentiable_id.const_mul _
  have hP : Differentiable ℂ (fun z => PTheta (π * z)) := by
    unfold PTheta
    exact (((h2.comp hl).pow 2).mul (h1.comp hl)).sub ((h3.comp hl).mul ((h1.comp hl).pow 2))
      |>.add (((h1.comp hl).pow 3).const_mul _)
  have hQ : Differentiable ℂ (fun z => QTheta (π * z)) := by
    unfold QTheta
    exact ((((h4.comp hl).neg).mul ((h1.comp hl).pow 2)).add
      ((((h2.comp hl).const_mul 3).mul (h3.comp hl)).mul (h1.comp hl))).sub
      (((h2.comp hl).pow 3).const_mul 2)
  rw [differentiable_pi]
  intro i
  fin_cases i <;> simp only [Zraw, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact hP.const_mul _
  · exact ((h1.comp hl).pow 3).neg.sub (hQ.const_mul _)
  · exact ((h1.comp hl).pow 3).neg.add (hQ.const_mul _)

/-! ## The unit lift `Zunit` -/

/-- Torus coordinates `z = u + τ v`. -/
def torusZ (u v : ℝ) : ℂ := u + v * tau

/-- Squared Euclidean norm on `ℂ³`. -/
def normSq3 (Z : Fin 3 → ℂ) : ℝ := ∑ i, ‖Z i‖ ^ 2

lemma normSq3_pos {Z : Fin 3 → ℂ} (h : Z ≠ 0) : 0 < normSq3 Z := by
  obtain ⟨i, hi⟩ : ∃ i, Z i ≠ 0 := by
    by_contra hc; push Not at hc; exact h (funext hc)
  have : 0 < ‖Z i‖ ^ 2 := by positivity
  exact lt_of_lt_of_le this
    (Finset.single_le_sum (f := fun i => ‖Z i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))

/-- **The unit lift** `Z = Zraw / ‖Zraw‖` (Euclidean norm on `ℂ³`) in torus coordinates. -/
def Zunit (u v : ℝ) : Fin 3 → ℂ :=
  ((Real.sqrt (normSq3 (Zraw (torusZ u v))))⁻¹ : ℂ) • Zraw (torusZ u v)

theorem normSq3_Zunit (u v : ℝ) : normSq3 (Zunit u v) = 1 := by
  have hpos := normSq3_pos (Zraw_ne_zero (torusZ u v))
  set s := normSq3 (Zraw (torusZ u v))
  have hs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
  unfold Zunit
  have : normSq3 (((Real.sqrt s)⁻¹ : ℂ) • Zraw (torusZ u v)) = (Real.sqrt s)⁻¹ ^ 2 * s := by
    simp only [normSq3, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    congr 1
    rw [← ofReal_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [this, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

open scoped ContDiff in
/-- **`Zunit` is smooth** as a function of `(u, v) ∈ ℝ²`. -/
theorem contDiff_Zunit : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Zunit p.1 p.2) := by
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Zraw (torusZ p.1 p.2)) := by
    have h1 : ContDiff ℝ ∞ Zraw := (differentiable_Zraw.contDiff (n := ∞)).restrict_scalars ℝ
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => torusZ p.1 p.2) := by
      unfold torusZ
      exact (ofRealCLM.contDiff.comp contDiff_fst).add
        ((ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
    exact h1.comp h2
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => normSq3 (Zraw (torusZ p.1 p.2))) := by
    unfold normSq3
    refine ContDiff.sum fun i _ => ?_
    exact (contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ ℂ i).comp hZ)
  have hne : ∀ p : ℝ × ℝ, normSq3 (Zraw (torusZ p.1 p.2)) ≠ 0 := fun p =>
    (normSq3_pos (Zraw_ne_zero _)).ne'
  have hsq := hs.sqrt hne
  have hinv := hsq.inv fun p => (Real.sqrt_pos.mpr (normSq3_pos (Zraw_ne_zero _))).ne'
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (((Real.sqrt (normSq3 (Zraw (torusZ p.1 p.2))))⁻¹ : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp hinv
  have := hc.smul hZ
  convert this using 2 with p
  simp [Zunit]

end SymplecticPacking.Bundle
