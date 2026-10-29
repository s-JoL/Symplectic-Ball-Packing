import SymplecticPacking.Bundle.EtaSigma

/-!
# Positivity of the pulled-back Fubini–Study form

`sec:fer` (`lem:fer-kappa`, used in `lem:fer-positivity`): the pulled-back Fubini–Study form
`σ = Zunit^* ω_FS` is strictly positive on the torus, `σ(∂_u, ∂_v) > 0`.

Proof. With `z = u + τ v`, `f = Zraw z`, `f' = Zraw'(z)` (complex derivative) and `Zunit = f/‖f‖`,
the chain rule gives (`sigmaC_eq`)
  `σ = Im τ · (‖f‖²‖f'‖² − |⟨f, f'⟩|²) / (π ‖f‖⁴)`.
By the Lagrange identity (`lagrange3`) the bracket is the sum of `|f_i f'_j − f_j f'_i|²`, so it
suffices that `f, f'` are linearly independent:
* at a lattice point (`θ₁(πz) = 0`): `f₀ = 0`, `f₀' = 2 cF π³ θ₁'³ ≠ 0`, `f₁ = 2 dF π³ θ₁'³ ≠ 0`;
* off the lattice, `f = θ³ (2cF℘, −1 − dF℘', −1 + dF℘')`, and the vanishing of all minors forces
  `℘' = ℘'' = 0`, contradicting `deriv_dwp_ne_zero`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open _root_.Complex ComplexConjugate Filter Topology PeriodPair
open scoped Real

/-! ### Algebra -/

/-- Lagrange's identity on `ℂ³`. -/
lemma lagrange3 (f g : Fin 3 → ℂ) :
    normSq3 f * normSq3 g - ((herm3 f g).re ^ 2 + (herm3 f g).im ^ 2) =
      ‖f 0 * g 1 - f 1 * g 0‖ ^ 2 + ‖f 0 * g 2 - f 2 * g 0‖ ^ 2 +
        ‖f 1 * g 2 - f 2 * g 1‖ ^ 2 := by
  simp only [normSq3, herm3, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply,
    mul_re, mul_im, sub_re, sub_im, add_re, add_im, conj_re, conj_im]
  ring

lemma herm3_expand_im (f g : Fin 3 → ℂ) (n a b : ℝ) (τ : ℂ) :
    (herm3 ((n : ℂ) • g + (a : ℂ) • f) ((n : ℂ) • (τ • g) + (b : ℂ) • f)).im =
      n ^ 2 * τ.im * normSq3 g - n * b * (herm3 f g).im +
        a * n * (τ.re * (herm3 f g).im + τ.im * (herm3 f g).re) := by
  simp only [herm3, normSq3, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, conj_ofReal, add_im, mul_im, mul_re, ofReal_re, ofReal_im, conj_re,
    conj_im, add_re, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma herm3_smul_re (f g : Fin 3 → ℂ) (τ : ℂ) :
    (herm3 f (τ • g)).re = τ.re * (herm3 f g).re - τ.im * (herm3 f g).im := by
  simp only [herm3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, add_re, add_im, mul_re,
    mul_im, conj_re, conj_im]
  ring

/-! ### Derivative of the normalisation -/

lemma hasDerivAt_normSq3 {F : ℝ → Fin 3 → ℂ} {F' : Fin 3 → ℂ} {s : ℝ}
    (hF : HasDerivAt F F' s) :
    HasDerivAt (fun t => normSq3 (F t)) (2 * (herm3 (F s) F').re) s := by
  have h : ∀ i, HasDerivAt (fun t => ‖F t i‖ ^ 2) (2 * (conj (F s i) * F' i).re) s := by
    intro i
    have := (hasDerivAt_pi.1 hF i).norm_sq
    rw [Complex.inner, mul_comm (F' i)] at this
    exact this
  have := ((h 0).add (h 1)).add (h 2)
  convert this using 1
  · funext t; simp [normSq3, Fin.sum_univ_three]
  · simp only [herm3, Fin.sum_univ_three, add_re]; ring

lemma hasDerivAt_normalize {F : ℝ → Fin 3 → ℂ} {F' : Fin 3 → ℂ} {s : ℝ}
    (hF : HasDerivAt F F' s) (h0 : F s ≠ 0) :
    HasDerivAt (fun t => (((Real.sqrt (normSq3 (F t)))⁻¹ : ℝ) : ℂ) • F t)
      ((((Real.sqrt (normSq3 (F s)))⁻¹ : ℝ) : ℂ) • F' +
        ((-(2 * (herm3 (F s) F').re / (2 * Real.sqrt (normSq3 (F s)))) /
          Real.sqrt (normSq3 (F s)) ^ 2 : ℝ) : ℂ) • F s) s := by
  have hpos := normSq3_pos h0
  have hq := (hasDerivAt_normSq3 hF).sqrt hpos.ne'
  have hqi := hq.inv (Real.sqrt_pos.mpr hpos).ne'
  exact hqi.ofReal_comp.smul hF

/-! ### The formula for `σ` -/

lemma Zunit_eq_fun (u v : ℝ) :
    Zunit u v = (((Real.sqrt (normSq3 (Zraw (torusZ u v))))⁻¹ : ℝ) : ℂ) •
      Zraw (torusZ u v) := by
  simp [Zunit, ofReal_inv]

theorem sigmaC_eq (u v : ℝ) :
    sigmaC u v = tau.im * (normSq3 (Zraw (torusZ u v)) * normSq3 (deriv Zraw (torusZ u v)) -
      ((herm3 (Zraw (torusZ u v)) (deriv Zraw (torusZ u v))).re ^ 2 +
        (herm3 (Zraw (torusZ u v)) (deriv Zraw (torusZ u v))).im ^ 2)) /
      (π * normSq3 (Zraw (torusZ u v)) ^ 2) := by
  set f := Zraw (torusZ u v) with hf
  set g := deriv Zraw (torusZ u v) with hg
  have hZ : HasDerivAt Zraw g (torusZ u v) := (differentiable_Zraw _).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => torusZ s v) 1 u := by
    have := ((hasDerivAt_id u).ofReal_comp).add_const ((v : ℂ) * tau)
    simpa [torusZ] using this
  have h2 : HasDerivAt (fun t : ℝ => torusZ u t) tau v := by
    have := (((hasDerivAt_id v).ofReal_comp).mul_const tau).const_add (u : ℂ)
    simpa [torusZ] using this
  have hu1 : HasDerivAt (fun s => Zraw (torusZ s v)) g u := by
    have := hZ.scomp u h1; rw [one_smul] at this; exact this
  have hv1 : HasDerivAt (fun t => Zraw (torusZ u t)) (tau • g) v := hZ.scomp v h2
  have hu := hasDerivAt_normalize hu1 (Zraw_ne_zero _)
  have hv := hasDerivAt_normalize hv1 (Zraw_ne_zero _)
  have eu : dZu u v = deriv (fun s => (((Real.sqrt (normSq3 (Zraw (torusZ s v))))⁻¹ : ℝ)
      : ℂ) • Zraw (torusZ s v)) u := by
    rw [dZu]; congr 1; funext s; exact Zunit_eq_fun s v
  have ev : dZv u v = deriv (fun t => (((Real.sqrt (normSq3 (Zraw (torusZ u t))))⁻¹ : ℝ)
      : ℂ) • Zraw (torusZ u t)) v := by
    rw [dZv]; congr 1; funext t; exact Zunit_eq_fun u t
  rw [sigmaC, eu, ev, hu.deriv, hv.deriv]
  simp only [← hf]
  rw [herm3_expand_im, herm3_smul_re]
  have hpos := normSq3_pos (Zraw_ne_zero (torusZ u v))
  rw [← hf] at hpos
  set S := normSq3 f
  set q := Real.sqrt S with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hpos
  have hq2 : q ^ 2 = S := Real.sq_sqrt hpos.le
  rw [← hq2]
  field_simp
  ring

/-! ### Linear independence of `f` and `f'` -/

lemma minor01_ne_zero_of_theta {z : ℂ} (hθ : jacobiTheta1 (π * z) = 0) :
    Zraw z 0 * deriv Zraw z 1 - Zraw z 1 * deriv Zraw z 0 ≠ 0 := by
  have hd := dTheta1_ne_zero_of_eq_zero hθ
  set ζ : ℂ := (π : ℂ) * z with hζ
  have h0 : HasDerivAt jacobiTheta1 (dTheta1 ζ) ζ :=
    differentiable_jacobiTheta1.differentiableAt.hasDerivAt
  have h1 : HasDerivAt dTheta1 (d2Theta1 ζ) ζ :=
    differentiable_dTheta1.differentiableAt.hasDerivAt
  have h2 : HasDerivAt d2Theta1 (d3Theta1 ζ) ζ :=
    differentiable_d2Theta1.differentiableAt.hasDerivAt
  have hP := (((h1.pow 2).mul h0).sub (h2.mul (h0.pow 2))).add ((h0.pow 3).const_mul rTheta)
  have hl : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hc := ((hP.comp z hl).const_mul (2 * cF * (π : ℂ) ^ 2))
  have hZ0 := hasDerivAt_pi.1 (differentiable_Zraw z).hasDerivAt 0
  have he : (fun w => Zraw w 0) = fun w => 2 * cF * (π : ℂ) ^ 2 *
      ((fun x => dTheta1 x ^ 2 * jacobiTheta1 x - d2Theta1 x * jacobiTheta1 x ^ 2 +
        rTheta * jacobiTheta1 x ^ 3) ∘ fun w : ℂ => (π : ℂ) * w) w := by
    funext w; simp [Zraw, PTheta]
  rw [he] at hZ0
  rw [hZ0.unique hc]
  have v0 : Zraw z 0 = 0 := by simp [Zraw, PTheta, ← hζ, hθ]
  have v1 : Zraw z 1 = 2 * dF * π ^ 3 * dTheta1 ζ ^ 3 := by
    simp [Zraw, QTheta, ← hζ, hθ]; ring
  rw [v0, v1, hθ]
  intro h
  apply hd
  simp only [Pi.pow_apply, hθ] at h
  have : 4 * dF * cF * (π : ℂ) ^ 6 * dTheta1 ζ ^ 6 = 0 := by linear_combination -h
  simpa [cF_ne_zero, dF_ne_zero, pi_ne_zero'] using this

lemma minors_ne_zero_off {z : ℂ} (hθ : jacobiTheta1 (π * z) ≠ 0) :
    ¬ (Zraw z 0 * deriv Zraw z 1 - Zraw z 1 * deriv Zraw z 0 = 0 ∧
       Zraw z 0 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 0 = 0 ∧
       Zraw z 1 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 1 = 0) := by
  rintro ⟨h01, h02, h12⟩
  have hz : z ∉ hexPair.lattice := fun h => hθ ((jacobiTheta1_pi_mul_eq_zero_iff z).mpr h)
  have hl : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have h0 : HasDerivAt jacobiTheta1 (dTheta1 (π * z)) (π * z) :=
    differentiable_jacobiTheta1.differentiableAt.hasDerivAt
  have hT := (h0.comp z hl).pow 3
  have hwp : HasDerivAt ℘[hexPair] (℘'[hexPair] z) z := by
    have := (wp_analyticOnNhd z hz).differentiableAt.hasDerivAt
    rwa [hexPair.deriv_weierstrassP] at this
  have hdwp : HasDerivAt ℘'[hexPair] (deriv ℘'[hexPair] z) z :=
    (dwp_analyticOnNhd z hz).differentiableAt.hasDerivAt
  have hev : ∀ᶠ w in 𝓝 z, jacobiTheta1 (π * w) ≠ 0 :=
    ((differentiable_jacobiTheta1.continuous.comp
      (continuous_const.mul continuous_id)).continuousAt).eventually_ne hθ
  have hD : ∀ i, HasDerivAt (fun w => Zraw w i) (deriv Zraw z i) z := fun i =>
    hasDerivAt_pi.1 (differentiable_Zraw z).hasDerivAt i
  have d0 := (hD 0).unique ((hT.mul (hwp.const_mul (2 * cF))).congr_of_eventuallyEq
    (by filter_upwards [hev] with w hw; rw [Zraw_eq hw]; simp [torusLift]))
  have d1 := (hD 1).unique ((hT.mul ((hdwp.const_mul dF).const_add 1).neg).congr_of_eventuallyEq
    (by filter_upwards [hev] with w hw; rw [Zraw_eq hw]; simp [torusLift]))
  have d2 := (hD 2).unique ((hT.mul ((hdwp.const_mul dF).const_sub 1).neg).congr_of_eventuallyEq
    (by filter_upwards [hev] with w hw; rw [Zraw_eq hw]; simp [torusLift]))
  simp only [Pi.pow_apply, Function.comp_apply, Pi.neg_apply] at d0 d1 d2
  have hv := Zraw_eq hθ
  have v0 : Zraw z 0 = jacobiTheta1 (π * z) ^ 3 * (2 * cF * ℘[hexPair] z) := by
    rw [hv]; simp [torusLift]
  have v1 : Zraw z 1 = jacobiTheta1 (π * z) ^ 3 * -(1 + dF * ℘'[hexPair] z) := by
    rw [hv]; simp [torusLift]
  have v2 : Zraw z 2 = jacobiTheta1 (π * z) ^ 3 * -(1 - dF * ℘'[hexPair] z) := by
    rw [hv]; simp [torusLift]
  rw [v0, v1, d0, d1] at h01
  rw [v0, v2, d0, d2] at h02
  rw [v1, v2, d1, d2] at h12
  set T := jacobiTheta1 (π * z)
  have hT6 : T ^ 6 ≠ 0 := pow_ne_zero 6 hθ
  have e12 : T ^ 6 * (-2 * dF * deriv ℘'[hexPair] z) = 0 := by linear_combination h12
  have e1 : T ^ 6 * (4 * cF * ℘'[hexPair] z) = 0 := by linear_combination h01 + h02
  have w2 : deriv ℘'[hexPair] z = 0 := by
    simpa [hT6, dF_ne_zero] using e12
  have w1 : ℘'[hexPair] z = 0 := by
    simpa [hT6, cF_ne_zero] using e1
  exact deriv_dwp_ne_zero hz w1 w2

/-- **`σ > 0`**: the pulled-back Fubini–Study form is a positive multiple of `du ∧ dv`. -/
theorem sigmaC_pos (u v : ℝ) : 0 < sigmaC u v := by
  rw [sigmaC_eq, lagrange3]
  set z := torusZ u v
  have hpos := normSq3_pos (Zraw_ne_zero z)
  have hsum : 0 < ‖Zraw z 0 * deriv Zraw z 1 - Zraw z 1 * deriv Zraw z 0‖ ^ 2 +
      ‖Zraw z 0 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 0‖ ^ 2 +
      ‖Zraw z 1 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 1‖ ^ 2 := by
    by_cases hθ : jacobiTheta1 (π * z) = 0
    · have := minor01_ne_zero_of_theta hθ
      have : 0 < ‖Zraw z 0 * deriv Zraw z 1 - Zraw z 1 * deriv Zraw z 0‖ ^ 2 := by positivity
      positivity
    · by_contra hc
      apply minors_ne_zero_off hθ
      push Not at hc
      have a := sq_nonneg ‖Zraw z 0 * deriv Zraw z 1 - Zraw z 1 * deriv Zraw z 0‖
      have b := sq_nonneg ‖Zraw z 0 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 0‖
      have c := sq_nonneg ‖Zraw z 1 * deriv Zraw z 2 - Zraw z 2 * deriv Zraw z 1‖
      refine ⟨?_, ?_, ?_⟩ <;> rw [← norm_eq_zero] <;> nlinarith
  have := tau_im_pos
  positivity

end SymplecticPacking.Bundle
