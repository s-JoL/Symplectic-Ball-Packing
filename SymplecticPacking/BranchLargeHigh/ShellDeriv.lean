import SymplecticPacking.BranchLargeHigh.Shell

/-!
# The slit-shell map pulls `ω₀` back to the coupled form

Supplement `lem:two-slit`. The derivative of the
slit-shell map is computed along lines `t ↦ y + t v`. Writing every coordinate as
`e · Y_j` with the common phase `e = e^{iθ}`, `θ = -2πT`, one has

  `Σ_j Im(conj(D(eY_j)v) D(eY_j)w) = Σ_j Im(conj(DY_j v) DY_j w)
      - θ_v Σ_j Re(conj Y_j DY_j w) + θ_w Σ_j Re(conj Y_j DY_j v)`

(`im_conj_phase`), `Σ_j Re(conj Y_j DY_j v) = -x_v/(2π)` because `π|Y|² = 1 - x`, and
`x_v T_w - x_w T_v = ω_fib(v, w)` because the strip map has Jacobian `1`.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Set ComplexConjugate
open scoped ContDiff

variable {m : ℕ}

/-! ### Complex algebra -/

lemma im_conj_phase (E0 Y Yv Yw : ℂ) (θv θw : ℝ) (hE : Complex.normSq E0 = 1) :
    (conj (E0 * ((θv : ℂ) * Complex.I * Y + Yv)) * (E0 * ((θw : ℂ) * Complex.I * Y + Yw))).im =
      (conj Yv * Yw).im - θv * (conj Y * Yw).re + θw * (conj Y * Yv).re := by
  have h1 : conj (E0 * ((θv : ℂ) * Complex.I * Y + Yv)) * (E0 * ((θw : ℂ) * Complex.I * Y + Yw)) =
      (conj E0 * E0) * (conj ((θv : ℂ) * Complex.I * Y + Yv) * ((θw : ℂ) * Complex.I * Y + Yw)) := by
    rw [map_mul]; ring
  rw [h1, ← Complex.normSq_eq_conj_mul_self, hE, Complex.ofReal_one, one_mul]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im, map_add, map_mul, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im]
  ring

/-! ### One-variable derivative helpers -/

lemma hasDerivAt_re' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).re) f'.re t := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  exact this

lemma hasDerivAt_im' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).im) f'.im t := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  exact this

lemma hasDerivAt_normSq' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Complex.normSq (f s)) (2 * ((f t).re * f'.re + (f t).im * f'.im)) t := by
  have := ((hasDerivAt_re' h).mul (hasDerivAt_re' h)).add ((hasDerivAt_im' h).mul (hasDerivAt_im' h))
  simp only [Complex.normSq_apply]
  convert this using 1; ring

lemma hasDerivAt_line (y v : E (m + 1)) (j : Fin (m + 1)) :
    HasDerivAt (fun t : ℝ => zc (y + t • v) j) (zc v j) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have := (zcCLM j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  exact this

/-! ### Directional derivatives of the ingredients -/

/-- `du_y(v)` -/
lemma hasDerivAt_fib (y v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => fibMoment (y + t • v)) (dFib y v) 0 := by
  have := (hasDerivAt_normSq' (hasDerivAt_line y v 0)).const_mul Real.pi
  simp only [zero_smul, add_zero] at this
  convert this using 1
  · rfl
  · simp only [dFib]; ring

/-- The derivative of the base moment, `dμ_y(v) = 2π Σ ⟨ξ, ξ_v⟩`. -/
def dBase (y v : E (m + 1)) : ℝ :=
  2 * Real.pi * ∑ i : Fin m,
    ((zc y i.succ).re * (zc v i.succ).re + (zc y i.succ).im * (zc v i.succ).im)

lemma hasDerivAt_base (y v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => baseMoment (y + t • v)) (dBase y v) 0 := by
  have := (HasDerivAt.sum (u := Finset.univ) fun (i : Fin m) _ =>
    hasDerivAt_normSq' (hasDerivAt_line y v i.succ)).const_mul Real.pi
  simp only [zero_smul, add_zero] at this
  unfold baseMoment
  convert this using 1
  · funext t; simp
  · rw [dBase, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

section
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

/-- The derivative of the strip point. -/
lemma hasDerivAt_strip (y v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => stripPt δ (y + t • v))
      (fderiv ℝ (Strip.psiStrip δ) (zc y 0) (zc v 0)) 0 := by
  have hd : DifferentiableAt ℝ (Strip.psiStrip δ) (zc y 0) :=
    (Strip.psiStrip_smooth hδ).differentiable (by simp) _
  have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line y v 0) (by simp)
  exact this

/-- The phase. -/
lemma hasDerivAt_phase (y v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => phase δ (y + t • v))
      (phase δ y * (((-(2 * Real.pi *
        (fderiv ℝ (Strip.psiStrip δ) (zc y 0) (zc v 0)).im) : ℝ) : ℂ) * Complex.I)) 0 := by
  have hT := hasDerivAt_im' (hasDerivAt_strip hδ y v)
  have h1 := ((hT.const_mul (2 * Real.pi)).neg.ofReal_comp.mul_const Complex.I).cexp
  unfold phase Ts
  convert h1 using 1
  simp only [Pi.neg_apply, zero_smul, add_zero]

/-- The radicand. -/
lemma hasDerivAt_radicand (y v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => radicand δ (y + t • v))
      ((-(fderiv ℝ (Strip.psiStrip δ) (zc y 0) (zc v 0)).re + dFib y v * baseMoment y -
        (1 - fibMoment y) * dBase y v) / Real.pi) 0 := by
  have hx := hasDerivAt_re' (hasDerivAt_strip hδ y v)
  have h1 := (((hx.const_sub 1).sub
    (((hasDerivAt_fib y v).const_sub 1).mul (hasDerivAt_base y v))).div_const Real.pi)
  simp only [zero_smul, add_zero] at h1
  unfold radicand xs
  convert h1 using 1
  ring

end

/-! ### The derivative of the slit-shell map -/

/-- The explicit derivative of the slit-shell map in complex coordinates. -/
def shellD (δ : ℝ) (y v : E (m + 1)) : Fin (m + 1) → ℂ :=
  let θv : ℝ := -(2 * Real.pi * (fderiv ℝ (Strip.psiStrip δ) (zc y 0) (zc v 0)).im)
  let s0 := Real.sqrt (radicand δ y)
  let s' : ℝ := ((-(fderiv ℝ (Strip.psiStrip δ) (zc y 0) (zc v 0)).re + dFib y v * baseMoment y -
        (1 - fibMoment y) * dBase y v) / Real.pi) / (2 * s0)
  let σ0 := Real.sqrt (1 - fibMoment y)
  let σ' : ℝ := -dFib y v / (2 * σ0)
  Fin.cons (phase δ y * ((θv : ℂ) * Complex.I * (s0 : ℂ) + (s' : ℂ)))
    (fun i => phase δ y * ((θv : ℂ) * Complex.I * ((σ0 : ℂ) * zc y i.succ) +
      ((σ' : ℂ) * zc y i.succ + (σ0 : ℂ) * zc v i.succ)))

section
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

lemma hasDerivAt_shellPhase {y : E (m + 1)} (hy : y ∈ shellDomain δ) (v : E (m + 1)) :
    HasDerivAt (fun t : ℝ => shellPhase δ (y + t • v)) (shellD δ y v) 0 := by
  rw [hasDerivAt_pi]
  intro j
  have hph := hasDerivAt_phase hδ y v
  refine Fin.cases ?_ (fun i => ?_) j
  · have hs := (hasDerivAt_radicand hδ y v).sqrt (by simpa using ne_of_gt hy.2)
    have h := hph.mul hs.ofReal_comp
    simp only [zero_smul, add_zero, ] at h
    simp only [shellPhase, Fin.cons_zero, shellD]
    convert h using 1
    push_cast; ring
  · have hσ := ((hasDerivAt_fib y v).const_sub 1).sqrt (by simpa using ne_of_gt (sub_pos.2 hy.1))
    have h := (hph.mul hσ.ofReal_comp).mul (hasDerivAt_line y v i.succ)
    simp only [zero_smul, add_zero, Pi.mul_apply] at h
    simp only [shellPhase, Fin.cons_succ, shellD]
    convert h using 1
    push_cast; ring

lemma fderiv_shell_apply {y : E (m + 1)} (hy : y ∈ shellDomain δ) (v : E (m + 1)) :
    fderiv ℝ (shell δ) y v = ofPhase (shellD δ y v) := by
  have hd : DifferentiableAt ℝ (shell δ) y :=
    (shell_contDiffAt hδ hy).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (shell δ ∘ fun t : ℝ => y + t • v) (ofPhase (shellD δ y v)) 0 := by
    have := (ofPhaseCLM (m + 1)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_shellPhase hδ hy v)
    exact this
  exact h1.unique h2

end

/-! ### The pull-back identity -/

lemma reim_eq (a b : ℂ) : a.re * b.im - a.im * b.re = (conj a * b).im := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

/-- `(La)ˣ(Lb)ᵀ - (Lb)ˣ(La)ᵀ = det L · ω(a, b)`. -/
lemma det2_apply (L : ℂ →L[ℝ] ℂ) (a b : ℂ) :
    (L a).re * (L b).im - (L b).re * (L a).im =
      Qhat.det2 L * (a.re * b.im - a.im * b.re) := by
  have ha : L a = a.re • L 1 + a.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]; congr 1; apply Complex.ext <;> simp
  have hb : L b = b.re • L 1 + b.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]; congr 1; apply Complex.ext <;> simp
  rw [ha, hb, Qhat.det2]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma term_zero (E0 : ℂ) (hE : Complex.normSq E0 = 1) (θv θw Yr pv pw : ℝ) :
    (E0 * ((θv : ℂ) * Complex.I * (Yr : ℂ) + (pv : ℂ))).re *
        (E0 * ((θw : ℂ) * Complex.I * (Yr : ℂ) + (pw : ℂ))).im -
      (E0 * ((θv : ℂ) * Complex.I * (Yr : ℂ) + (pv : ℂ))).im *
        (E0 * ((θw : ℂ) * Complex.I * (Yr : ℂ) + (pw : ℂ))).re =
      θw * (Yr * pv) - θv * (Yr * pw) := by
  rw [reim_eq, im_conj_phase _ _ _ _ _ _ hE]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_ofReal, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- `ω(a, b)` for complex numbers. -/
def wedge (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- `⟨a, b⟩` for complex numbers. -/
def dotC (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

lemma term_succ (E0 : ℂ) (hE : Complex.normSq E0 = 1) (θv θw σ0 σv σw : ℝ) (ξ ξv ξw : ℂ) :
    (E0 * ((θv : ℂ) * Complex.I * ((σ0 : ℂ) * ξ) + ((σv : ℂ) * ξ + (σ0 : ℂ) * ξv))).re *
        (E0 * ((θw : ℂ) * Complex.I * ((σ0 : ℂ) * ξ) + ((σw : ℂ) * ξ + (σ0 : ℂ) * ξw))).im -
      (E0 * ((θv : ℂ) * Complex.I * ((σ0 : ℂ) * ξ) + ((σv : ℂ) * ξ + (σ0 : ℂ) * ξv))).im *
        (E0 * ((θw : ℂ) * Complex.I * ((σ0 : ℂ) * ξ) + ((σw : ℂ) * ξ + (σ0 : ℂ) * ξw))).re =
      (σ0 * σv) * wedge ξ ξw - (σ0 * σw) * wedge ξ ξv + (σ0 * σ0) * wedge ξv ξw +
        θv * (-(σ0 * σw) * Complex.normSq ξ) + θv * (-(σ0 * σ0) * dotC ξ ξw) +
        θw * ((σ0 * σv) * Complex.normSq ξ) + θw * ((σ0 * σ0) * dotC ξ ξv) := by
  rw [reim_eq, im_conj_phase _ _ _ _ _ _ hE]
  simp only [wedge, dotC, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_re,
    Complex.ofReal_im, Complex.normSq_apply]
  ring

lemma omegaBase_eq (v w : E (m + 1)) :
    omegaBase v w = ∑ i : Fin m, wedge (zc v i.succ) (zc w i.succ) := rfl

lemma dBase_eq (y v : E (m + 1)) :
    dBase y v = 2 * Real.pi * ∑ i : Fin m, dotC (zc y i.succ) (zc v i.succ) := rfl

section
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

/-- **Pull-back identity** `shell^* ω₀ = Ω` (supplement `lem:two-slit`). -/
theorem shell_pullback {y : E (m + 1)} (hy : y ∈ shellDomain δ) (v w : E (m + 1)) :
    Problem.omega0 (fderiv ℝ (shell δ) y v) (fderiv ℝ (shell δ) y w) = coupledForm y v w := by
  rw [fderiv_shell_apply hδ hy, fderiv_shell_apply hδ hy, omega0_eq]
  simp only [zc_ofPhase]
  rw [Fin.sum_univ_succ]
  simp only [shellD, Fin.cons_zero, Fin.cons_succ]
  have hE := phase_normSq δ y
  rw [term_zero _ hE]
  simp only [term_succ _ hE]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  set L := fderiv ℝ (Strip.psiStrip δ) (zc y 0) with hL
  set s0 := Real.sqrt (radicand δ y) with hs0
  set σ0 := Real.sqrt (1 - fibMoment y) with hσ0
  have hs0pos : 0 < s0 := Real.sqrt_pos.2 hy.2
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.2 (sub_pos.2 hy.1)
  have hπ := Real.pi_pos
  have hsv : ∀ u : E (m + 1), 2 * Real.pi * (s0 * (((-(L (zc u 0)).re + dFib y u * baseMoment y -
      (1 - fibMoment y) * dBase y u) / Real.pi) / (2 * s0))) =
      -(L (zc u 0)).re + dFib y u * (Real.pi * ∑ i : Fin m, Complex.normSq (zc y i.succ)) -
        (1 - fibMoment y) * (2 * Real.pi * ∑ i : Fin m, dotC (zc y i.succ) (zc u i.succ)) := by
    intro u
    rw [show baseMoment y = Real.pi * ∑ i : Fin m, Complex.normSq (zc y i.succ) from rfl,
      dBase_eq]
    field_simp
  have hσ : ∀ u : E (m + 1), 2 * (σ0 * (-dFib y u / (2 * σ0))) = -dFib y u := by
    intro u; field_simp
  have hσ2 : σ0 * σ0 = 1 - fibMoment y := Real.mul_self_sqrt (sub_pos.2 hy.1).le
  have hdet : (L (zc v 0)).re * (L (zc w 0)).im - (L (zc w 0)).re * (L (zc v 0)).im =
      omegaFib v w := by
    rw [det2_apply, Strip.psiStrip_symplectic hδ, one_mul]; rfl
  unfold coupledForm lamBase
  rw [omegaBase_eq, omegaBase_eq, omegaBase_eq]
  linear_combination (-(L (zc w 0)).im) * hsv v + (L (zc v 0)).im * hsv w +
    ((∑ i : Fin m, wedge (zc y i.succ) (zc w i.succ)) +
      (-(2 * Real.pi * (L (zc w 0)).im)) * ∑ i : Fin m, Complex.normSq (zc y i.succ)) / 2 * hσ v +
    (-(∑ i : Fin m, wedge (zc y i.succ) (zc v i.succ)) -
      (-(2 * Real.pi * (L (zc v 0)).im)) * ∑ i : Fin m, Complex.normSq (zc y i.succ)) / 2 * hσ w +
    ((∑ i : Fin m, wedge (zc v i.succ) (zc w i.succ)) -
      (-(2 * Real.pi * (L (zc v 0)).im)) * (∑ i : Fin m, dotC (zc y i.succ) (zc w i.succ)) +
      (-(2 * Real.pi * (L (zc w 0)).im)) * (∑ i : Fin m, dotC (zc y i.succ) (zc v i.succ))) * hσ2 +
    hdet

end

end SymplecticPacking.BranchLargeHigh
