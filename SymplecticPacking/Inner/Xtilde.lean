import Mathlib
import SymplecticPacking.Inner.Rtilde
import SymplecticPacking.Inner.Inverse

/-!
# The x-side of the inner map

`sec:pll`, x-side of the inner map: the inverse `X` of the hyperbola `R = Rmorse`
(paper `def:pll-hyperbola`, `lem:pll-hyperbola-inverse`) and the signed inverse `X̃ = Σ_R⁻¹` of the exactly
quadratic modification `R̃` (paper `cons:pll-morse`, `lem:pll-quadratic`).

Notation: `s(u) = √(u² + 2ηr)`, `a₀ = √(2/α₀)`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology Set
open scoped ContDiff

variable (P : Params)

/-! ### The inverse `X` of `R` (`def:pll-hyperbola`) -/

/-- `X(u) = (-m u² + n u √(u² + 2ηr)) / r²`. -/
def Xinv (u : ℝ) : ℝ := (-P.m * u ^ 2 + P.n * u * √(u ^ 2 + 2 * P.eta * P.r)) / P.r ^ 2

/-- `a₀ = √(2/α₀)`. -/
def a0 : ℝ := √(2 / P.alpha0)

lemma two_eta_r_pos : 0 < 2 * P.eta * P.r := by
  have := P.eta_pos; have := P.r_pos; positivity

lemma sX_pos (u : ℝ) : 0 < √(u ^ 2 + 2 * P.eta * P.r) :=
  Real.sqrt_pos.2 (by have := two_eta_r_pos P; positivity)

lemma sX_sq (u : ℝ) : √(u ^ 2 + 2 * P.eta * P.r) ^ 2 = u ^ 2 + 2 * P.eta * P.r :=
  Real.sq_sqrt (by have := two_eta_r_pos P; positivity)

lemma abs_lt_sX (u : ℝ) : |u| < √(u ^ 2 + 2 * P.eta * P.r) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith [two_eta_r_pos P])

lemma m_mul_le (a b : ℝ) : a * b ≤ |a| * |b| := by rw [← abs_mul]; exact le_abs_self _

/-- `n s(u) - m u > 0`. -/
lemma Xinv_factor_pos (u : ℝ) : 0 < P.n * √(u ^ 2 + 2 * P.eta * P.r) - P.m * u := by
  have h1 := abs_lt_sX P u
  have h2 := abs_m_lt_n P
  have h2' : |P.m| < P.n := h2
  have h3 := m_mul_le P.m u
  have hn := P.n_pos
  have : 0 < P.n * (√(u ^ 2 + 2 * P.eta * P.r) - |u|) := mul_pos hn (by linarith)
  have : 0 ≤ (P.n - |P.m|) * |u| := mul_nonneg (by linarith) (abs_nonneg u)
  nlinarith

lemma Xinv_eq_mul (u : ℝ) :
    Xinv P u = u * (P.n * √(u ^ 2 + 2 * P.eta * P.r) - P.m * u) / P.r ^ 2 := by
  unfold Xinv; ring

lemma Xinv_zero : Xinv P 0 = 0 := by unfold Xinv; simp

lemma Xinv_pos {u : ℝ} (hu : 0 < u) : 0 < Xinv P u := by
  rw [Xinv_eq_mul]; have := Xinv_factor_pos P u; have := P.r_pos; positivity

lemma Xinv_neg {u : ℝ} (hu : u < 0) : Xinv P u < 0 := by
  rw [Xinv_eq_mul]; have hf := Xinv_factor_pos P u; have := P.r_pos
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hu hf) (by positivity)

/-- `sign X(u) = sign u`. -/
theorem Xinv_sign (u : ℝ) : Real.sign (Xinv P u) = Real.sign u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [Real.sign_of_neg hu, Real.sign_of_neg (Xinv_neg P hu)]
  · rw [Xinv_zero]
  · rw [Real.sign_of_pos hu, Real.sign_of_pos (Xinv_pos P hu)]

/-- **Lemma `lem:pll-hyperbola-inverse`**: `R(X(u)) = u²`. -/
theorem Rmorse_Xinv (u : ℝ) : P.Rmorse (Xinv P u) = u ^ 2 := by
  have hs2 := sX_sq P u
  have hs0 := sX_pos P u
  set s := √(u ^ 2 + 2 * P.eta * P.r) with hs_def
  have hr := P.r_pos
  have hn := P.n_pos
  have he := P.eta_pos
  have hnm : P.n ^ 2 - P.m ^ 2 = P.r ^ 2 := P.n_sq_sub_m_sq
  set c := u ^ 2 + P.eta * P.r with hc_def
  set w := P.xstar + Xinv P u with hw_def
  have hx : P.r ^ 2 * P.xstar = -P.m * P.eta * P.r := by
    unfold Params.xstar; field_simp
  have hX : P.r ^ 2 * Xinv P u = -P.m * u ^ 2 + P.n * u * s := by
    unfold Xinv; rw [← hs_def]; field_simp
  have hw : P.r ^ 2 * w = -P.m * c + P.n * u * s := by
    rw [hw_def, mul_add, hx, hX, hc_def]; ring
  -- `c > |u| s`
  have hcs : |u| * s < c := by
    have hsq : c ^ 2 - (|u| * s) ^ 2 = (P.eta * P.r) ^ 2 := by
      rw [mul_pow, sq_abs, hs2, hc_def]; ring
    have : 0 < c := by rw [hc_def]; positivity
    have : 0 ≤ |u| * s := by positivity
    nlinarith [mul_pos he hr]
  have hpos : 0 < P.n * c - P.m * u * s := by
    have h2 : |P.m| < P.n := abs_m_lt_n P
    have h3 : P.m * u * s ≤ |P.m| * (|u| * s) := by
      rw [mul_assoc]; refine (m_mul_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hs0]
    have : 0 ≤ |u| * s := by positivity
    nlinarith
  have hcmw : P.r ^ 2 * (c - P.m * w) = P.n * (P.n * c - P.m * u * s) := by
    linear_combination (-P.m) * hw - c * hnm
  have hcmw_pos : 0 < c - P.m * w := by
    have : 0 < P.r ^ 2 * (c - P.m * w) := by rw [hcmw]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hsq : P.n ^ 2 * (w ^ 2 + P.eta ^ 2) = (c - P.m * w) ^ 2 := by
    have hr4 : P.r ^ 2 ≠ 0 := by positivity
    have key : (P.r ^ 2) ^ 2 * (P.n ^ 2 * (w ^ 2 + P.eta ^ 2) - (c - P.m * w) ^ 2) = 0 := by
      have e1 : (P.r ^ 2) ^ 2 * (P.n ^ 2 * (w ^ 2 + P.eta ^ 2) - (c - P.m * w) ^ 2)
          = P.n ^ 2 * ((P.r ^ 2 * w) ^ 2 + P.eta ^ 2 * (P.r ^ 2) ^ 2)
            - (P.r ^ 2 * c - P.m * (P.r ^ 2 * w)) ^ 2 := by ring
      rw [e1, hw, hc_def]
      linear_combination ((-P.m * (u ^ 2 + P.eta * P.r) + P.n * u * s) ^ 2
        + P.r ^ 2 * (u ^ 2 + P.eta * P.r) ^ 2) * hnm + P.r ^ 2 * P.n ^ 2 * u ^ 2 * hs2
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h (pow_ne_zero 2 hr4)
    · linarith
  have hsqrt : √(w ^ 2 + P.eta ^ 2) = (c - P.m * w) / P.n := by
    rw [show w ^ 2 + P.eta ^ 2 = ((c - P.m * w) / P.n) ^ 2 by
      rw [div_pow, eq_div_iff (by positivity)]; linarith]
    exact Real.sqrt_sq (div_nonneg hcmw_pos.le hn.le)
  unfold Params.Rmorse
  rw [← hw_def, hsqrt, hc_def]
  field_simp
  ring

/-! ### Derivative and monotonicity of `X` -/

/-! ### Uniqueness (`lem:pll-hyperbola-inverse`) -/

lemma Rmorse1_pos {x : ℝ} (hx : 0 < x) : 0 < Rmorse1 P x := by
  have := Rmorse1_strictMono P hx; rwa [Rmorse1_zero] at this

lemma Rmorse1_neg {x : ℝ} (hx : x < 0) : Rmorse1 P x < 0 := by
  have := Rmorse1_strictMono P hx; rwa [Rmorse1_zero] at this

lemma Rmorse_strictMonoOn : StrictMonoOn P.Rmorse (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) (Rmorse_contDiff P).continuous.continuousOn
    (fun x hx => by
      rw [interior_Ici] at hx; rw [deriv_Rmorse]; exact Rmorse1_pos P hx)

lemma Rmorse_strictAntiOn : StrictAntiOn P.Rmorse (Iic 0) :=
  strictAntiOn_of_deriv_neg (convex_Iic 0) (Rmorse_contDiff P).continuous.continuousOn
    (fun x hx => by
      rw [interior_Iic] at hx; rw [deriv_Rmorse]; exact Rmorse1_neg P hx)

/-- **Lemma `lem:pll-hyperbola-inverse`** (uniqueness): for `u ≠ 0`, `X(u)` is the only solution of
`R(x) = u²` with the sign of `u`. -/
theorem Xinv_unique {u x : ℝ} (hu : u ≠ 0) (hx : P.Rmorse x = u ^ 2)
    (hsign : Real.sign x = Real.sign u) : x = Xinv P u := by
  rcases lt_or_gt_of_ne hu with hu | hu
  · have hx0 : x < 0 := by
      rw [Real.sign_of_neg hu] at hsign
      rcases lt_trichotomy x 0 with h | rfl | h
      · exact h
      · rw [Real.sign_zero] at hsign; norm_num at hsign
      · rw [Real.sign_of_pos h] at hsign; norm_num at hsign
    exact Rmorse_strictAntiOn P |>.injOn (Set.mem_Iic.2 hx0.le)
      (Set.mem_Iic.2 (Xinv_neg P hu).le) (by rw [hx, Rmorse_Xinv])
  · have hx0 : 0 < x := by
      rw [Real.sign_of_pos hu] at hsign
      rcases lt_trichotomy x 0 with h | rfl | h
      · rw [Real.sign_of_neg h] at hsign; norm_num at hsign
      · rw [Real.sign_zero] at hsign; norm_num at hsign
      · exact h
    exact Rmorse_strictMonoOn P |>.injOn (Set.mem_Ici.2 hx0.le)
      (Set.mem_Ici.2 (Xinv_pos P hu).le) (by rw [hx, Rmorse_Xinv])

/-! ### The signed square root `Σ_R` and `X̃` (`cons:pll-morse`) -/

/-- `Σ_R(x) = sign(x) √(R̃(x))`. -/
def SigmaR (x : ℝ) : ℝ := Real.sign x * √(Rtilde P x)

/-- `X̃ = Σ_R⁻¹`. -/
def Xtilde : ℝ → ℝ := invR (SigmaR P)

/-- `u_ε = √(α₀/2) ε_R`. -/
def uEps : ℝ := √(P.alpha0 / 2) * epsR P

lemma sqrt_alpha0_half_pos : 0 < √(P.alpha0 / 2) :=
  Real.sqrt_pos.2 (by have := P.alpha0_pos; positivity)

lemma SigmaR_zero : SigmaR P 0 = 0 := by unfold SigmaR; rw [Real.sign_zero, zero_mul]

lemma SigmaR_of_pos {x : ℝ} (hx : 0 < x) : SigmaR P x = √(Rtilde P x) := by
  unfold SigmaR; rw [Real.sign_of_pos hx, one_mul]

lemma SigmaR_of_neg {x : ℝ} (hx : x < 0) : SigmaR P x = -√(Rtilde P x) := by
  unfold SigmaR; rw [Real.sign_of_neg hx, neg_one_mul]

/-- **Lemma `lem:pll-quadratic`(i)**: `Σ_R(x) = √(α₀/2) x` for `|x| ≤ ε_R`. -/
theorem SigmaR_linear {x : ℝ} (hx : |x| ≤ epsR P) : SigmaR P x = √(P.alpha0 / 2) * x := by
  unfold SigmaR
  rw [Rtilde_eq_quad P hx, show P.alpha0 * x ^ 2 / 2 = P.alpha0 / 2 * x ^ 2 by ring,
    Real.sqrt_mul (by have := P.alpha0_pos; positivity), Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- `Σ_R² = R̃`. -/
theorem SigmaR_sq (x : ℝ) : SigmaR P x ^ 2 = Rtilde P x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [SigmaR_of_neg P h, neg_sq, Real.sq_sqrt (Rtilde_pos P h.ne).le]
  · rw [SigmaR_zero, Rtilde_zero]; ring
  · rw [SigmaR_of_pos P h, Real.sq_sqrt (Rtilde_pos P h.ne').le]

lemma Rtilde_differentiable : Differentiable ℝ (Rtilde P) :=
  (Rtilde_smooth P).differentiable (by simp)

/-- The three local descriptions of `Σ_R` with their derivatives. -/
lemma SigmaR_hasDerivAt_local (x : ℝ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (SigmaR P) d x ∧ ContDiffAt ℝ ∞ (SigmaR P) x := by
  have he := epsR_pos P
  by_cases h0 : |x| < epsR P
  · have hev : SigmaR P =ᶠ[𝓝 x] fun z => √(P.alpha0 / 2) * z := by
      filter_upwards [(continuous_abs.tendsto x).eventually (gt_mem_nhds h0)] with z hz
      exact SigmaR_linear P hz.le
    refine ⟨√(P.alpha0 / 2), sqrt_alpha0_half_pos P, ?_, ?_⟩
    · have := (hasDerivAt_id x).const_mul (√(P.alpha0 / 2))
      rw [mul_one] at this
      exact this.congr_of_eventuallyEq hev
    · exact (contDiffAt_id.const_smul (√(P.alpha0 / 2))).congr_of_eventuallyEq hev
  · rw [not_lt] at h0
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; rw [abs_zero] at h0; linarith) with hx | hx
    · have hR := Rtilde_pos P hx.ne
      have hev : SigmaR P =ᶠ[𝓝 x] fun z => -√(Rtilde P z) := by
        filter_upwards [gt_mem_nhds hx] with z hz using SigmaR_of_neg P hz
      have hd := (((Rtilde_differentiable P) x).hasDerivAt.sqrt hR.ne').neg
      refine ⟨-(deriv (Rtilde P) x / (2 * √(Rtilde P x))), ?_, hd.congr_of_eventuallyEq hev, ?_⟩
      · have := Rtilde_deriv_neg P hx
        have : 0 < √(Rtilde P x) := Real.sqrt_pos.2 hR
        have : deriv (Rtilde P) x / (2 * √(Rtilde P x)) < 0 :=
          div_neg_of_neg_of_pos ‹_› (by linarith)
        linarith
      · exact (((Rtilde_smooth P).contDiffAt.sqrt hR.ne').neg).congr_of_eventuallyEq hev
    · have hR := Rtilde_pos P hx.ne'
      have hev : SigmaR P =ᶠ[𝓝 x] fun z => √(Rtilde P z) := by
        filter_upwards [lt_mem_nhds hx] with z hz using SigmaR_of_pos P hz
      have hd := ((Rtilde_differentiable P) x).hasDerivAt.sqrt hR.ne'
      refine ⟨deriv (Rtilde P) x / (2 * √(Rtilde P x)), ?_, hd.congr_of_eventuallyEq hev, ?_⟩
      · have := Rtilde_deriv_pos P hx
        have : 0 < √(Rtilde P x) := Real.sqrt_pos.2 hR
        positivity
      · exact ((Rtilde_smooth P).contDiffAt.sqrt hR.ne').congr_of_eventuallyEq hev

/-- **Lemma `lem:pll-quadratic`(i)**: `Σ_R` is `C^∞`. -/
theorem SigmaR_smooth : ContDiff ℝ ∞ (SigmaR P) :=
  contDiff_iff_contDiffAt.2 fun x => (SigmaR_hasDerivAt_local P x).choose_spec.2.2

lemma SigmaR_differentiable : Differentiable ℝ (SigmaR P) :=
  (SigmaR_smooth P).differentiable (by simp)

/-- **Lemma `lem:pll-quadratic`(i)**: `Σ_R' > 0`. -/
theorem SigmaR_deriv_pos (x : ℝ) : 0 < deriv (SigmaR P) x := by
  obtain ⟨d, hd, hD, -⟩ := SigmaR_hasDerivAt_local P x
  rw [hD.deriv]; exact hd

theorem SigmaR_strictMono : StrictMono (SigmaR P) := strictMono_of_deriv_pos (SigmaR_deriv_pos P)

theorem SigmaR_continuous : Continuous (SigmaR P) := (SigmaR_smooth P).continuous

theorem SigmaR_tendsto_atTop : Tendsto (SigmaR P) atTop atTop := by
  have h : Tendsto (fun x => √(Rtilde P x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Rtilde_tendsto_atTop P)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx using (SigmaR_of_pos P hx).symm

theorem SigmaR_tendsto_atBot : Tendsto (SigmaR P) atBot atBot := by
  have h : Tendsto (fun x => -√(Rtilde P x)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (Real.tendsto_sqrt_atTop.comp (Rtilde_tendsto_atBot P))
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx using (SigmaR_of_neg P hx).symm

lemma SigmaR_hasDerivAt (x : ℝ) : HasDerivAt (SigmaR P) (deriv (SigmaR P) x) x :=
  ((SigmaR_differentiable P) x).hasDerivAt

/-! ### `X̃` (`lem:pll-quadratic` (ii)–(iv)) -/

theorem SigmaR_Xtilde (u : ℝ) : SigmaR P (Xtilde P u) = u :=
  apply_invR' (SigmaR_continuous P) (SigmaR_strictMono P) (SigmaR_tendsto_atTop P)
    (SigmaR_tendsto_atBot P) u

theorem Xtilde_SigmaR (x : ℝ) : Xtilde P (SigmaR P x) = x :=
  invR_apply' (SigmaR_strictMono P) x

/-- **Lemma `lem:pll-quadratic`(ii)**: `R̃(X̃(u)) = u²`. -/
theorem Rtilde_Xtilde (u : ℝ) : Rtilde P (Xtilde P u) = u ^ 2 := by
  rw [← SigmaR_sq, SigmaR_Xtilde]

theorem Xtilde_strictMono : StrictMono (Xtilde P) :=
  invR_strictMono (SigmaR_continuous P) (SigmaR_strictMono P) (SigmaR_tendsto_atTop P)
    (SigmaR_tendsto_atBot P)

theorem Xtilde_smooth : ContDiff ℝ ∞ (Xtilde P) :=
  invR_contDiff (SigmaR_continuous P) (SigmaR_strictMono P) (SigmaR_tendsto_atTop P)
    (SigmaR_tendsto_atBot P) (SigmaR_hasDerivAt P) (SigmaR_deriv_pos P) (SigmaR_smooth P)

theorem Xtilde_deriv_pos (u : ℝ) : 0 < deriv (Xtilde P) u :=
  deriv_invR_pos (SigmaR_continuous P) (SigmaR_strictMono P) (SigmaR_tendsto_atTop P)
    (SigmaR_tendsto_atBot P) (SigmaR_hasDerivAt P) (SigmaR_deriv_pos P) u

theorem Xtilde_zero : Xtilde P 0 = 0 := by
  have := Xtilde_SigmaR P 0; rwa [SigmaR_zero] at this

theorem Xtilde_pos {u : ℝ} (hu : 0 < u) : 0 < Xtilde P u := by
  have := Xtilde_strictMono P hu; rwa [Xtilde_zero] at this

theorem Xtilde_neg {u : ℝ} (hu : u < 0) : Xtilde P u < 0 := by
  have := Xtilde_strictMono P hu; rwa [Xtilde_zero] at this

/-- **Lemma `lem:pll-quadratic`(ii)**: `sign X̃(u) = sign u`. -/
theorem Xtilde_sign (u : ℝ) : Real.sign (Xtilde P u) = Real.sign u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [Real.sign_of_neg hu, Real.sign_of_neg (Xtilde_neg P hu)]
  · rw [Xtilde_zero]
  · rw [Real.sign_of_pos hu, Real.sign_of_pos (Xtilde_pos P hu)]

lemma a0_mul_sqrt : a0 P * √(P.alpha0 / 2) = 1 := by
  unfold a0
  rw [← Real.sqrt_mul (by have := P.alpha0_pos; positivity)]
  rw [show 2 / P.alpha0 * (P.alpha0 / 2) = 1 by field_simp [P.alpha0_pos.ne'], Real.sqrt_one]

/-- **Lemma `lem:pll-quadratic`(iii)**: `X̃(u) = a₀ u` for `|u| ≤ u_ε`. -/
theorem Xtilde_linear {u : ℝ} (hu : |u| ≤ uEps P) : Xtilde P u = a0 P * u := by
  unfold Xtilde
  rw [invR_linear (SigmaR_strictMono P) (sqrt_alpha0_half_pos P)
    (fun x hx => SigmaR_linear P hx) hu]
  have ha := a0_mul_sqrt P
  have := (sqrt_alpha0_half_pos P).ne'
  field_simp
  linear_combination -u * ha

/-- **Lemma `lem:pll-quadratic`(iii)**: `X̃'(u) = a₀` for `|u| < u_ε`. -/
theorem Xtilde_deriv_linear {u : ℝ} (hu : |u| < uEps P) : deriv (Xtilde P) u = a0 P := by
  have hev : Xtilde P =ᶠ[𝓝 u] fun v => a0 P * v := by
    filter_upwards [(continuous_abs.tendsto u).eventually (gt_mem_nhds hu)] with v hv
    exact Xtilde_linear P hv.le
  rw [hev.deriv_eq]
  have := (hasDerivAt_id u).const_mul (a0 P)
  rw [mul_one] at this
  exact this.deriv

/-- **Lemma `lem:pll-quadratic`(iv)**: if `|X(u)| ≥ 2ε_R` or `|X̃(u)| ≥ 2ε_R`, then `X̃(u) = X(u)`. -/
theorem Xtilde_eq_Xinv {u : ℝ} (h : 2 * epsR P ≤ |Xinv P u| ∨ 2 * epsR P ≤ |Xtilde P u|) :
    Xtilde P u = Xinv P u := by
  rcases h with h | h
  · apply invR_eq_of_apply_eq (SigmaR_strictMono P).injective
    unfold SigmaR
    rw [Rtilde_eq_far P h, Rmorse_Xinv, Real.sqrt_sq_eq_abs, Xinv_sign]
    rcases lt_trichotomy u 0 with hu | rfl | hu
    · rw [Real.sign_of_neg hu, abs_of_neg hu]; ring
    · simp
    · rw [Real.sign_of_pos hu, abs_of_pos hu]; ring
  · have hu : u ≠ 0 := by
      rintro rfl; rw [Xtilde_zero, abs_zero] at h; linarith [epsR_pos P]
    apply Xinv_unique P hu _ (Xtilde_sign P u)
    rw [← Rtilde_eq_far P h, Rtilde_Xtilde]

/-- **Lemma `lem:pll-quadratic`(iv)**: `|X̃(u)| ≤ max(|X(u)|, 2ε_R) ≤ |X(u)| + 2ε_R`. -/
theorem Xtilde_abs_le (u : ℝ) :
    |Xtilde P u| ≤ max |Xinv P u| (2 * epsR P) ∧
      max |Xinv P u| (2 * epsR P) ≤ |Xinv P u| + 2 * epsR P := by
  have he := epsR_pos P
  refine ⟨?_, max_le (by linarith) (by linarith [abs_nonneg (Xinv P u)])⟩
  rcases lt_or_ge |Xtilde P u| (2 * epsR P) with h | h
  · exact le_max_of_le_right h.le
  · rw [Xtilde_eq_Xinv P (Or.inr h)]; exact le_max_left _ _

end SymplecticPacking.Inner
