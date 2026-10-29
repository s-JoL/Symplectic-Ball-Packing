import SymplecticPacking.Forms.Kahler
import SymplecticPacking.Return.Algebra

/-!
# The ambient Kähler form `Ω_E`

`sec:rtc`, the ambient Kähler form `Ω_E` on representatives `(Z, W) ∈ ℂ³ × ℂ`
(Equation eq:rtc-OmegaE, Lemmas lem:rtc-dc, lem:rtc-kahler,
Lemma lem:rtc-transport-field (iv) in its form-theoretic version).

* `PhiE dn (Z, W) = log ‖Z‖² + d_n log(1 + |W|²/‖Z‖⁶)` (on `Z ≠ 0`), `lamE = d^c PhiE`,
  `OmegaE = d lamE` (`Forms.d1`). Closedness: `OmegaE_closed`.
  Since `log ‖Z‖²` has `dd^c = ω_FS` (pulled back to `ℂ³ ∖ 0`), `OmegaE` is the pullback of
  `Ω_E = ω_FS + d_n dd^c log(1 + ‖W‖²)` along `(ℂ³∖0) × ℂ → E₃`.
* `lamE_eq`: explicit formula for `lamE` at every point with `Z ≠ 0`;
  `dc_log_one_add` (Lemma lem:rtc-dc at unit representatives:
  `d^c log(1+‖W‖²) = ‖W‖²/(1+‖W‖²) α`), `dc_log_normW` (`d^c log ‖W‖² = α`).
* `OmegaE_unit`: `OmegaE` at a unit representative, for arbitrary tangent vectors.
* `OmegaE_herm` (Lemma lem:rtc-kahler): in the gauge `Z†Ż = 0`,
  `OmegaE((Ż₁,Ẇ₁),(Ż₂,Ẇ₂)) = (1/π) Im(A Ż₁†Ż₂ + B conj(Ẇ₁) Ẇ₂)`.
* Orbit degeneracy: `OmegaE` vanishes on the infinitesimal `ℂ*`-orbit directions `(Z, 3W)` and
  `i (Z, 3W)` (`OmegaE_orbit`, `OmegaE_orbitI` and the right-hand versions).
* `OmegaE_pos`: positivity on the gauge slice (`0 < d_n ≤ 1/3`).
* `transport_isotropic`: at points of `X_T`, `OmegaE(V, ξ) = 0` for the `(Z, W)`-part `V` of the
  transport field and every `ξ` tangent to `X_T` (`dF_Z(Ż) = T Ẇ`), no gauge assumption on `ξ`.

Real-vector conventions: tangent vectors are `v = (v.1, v.2) ∈ ℂ³ × ℂ`; `η_H` is represented by
its real part `etaH Z Ż = Im(Z†Ż)/(2π)` (equal to `(2πi)⁻¹ Z†Ż` on vectors tangent to the unit
sphere, where `Re(Z†Ż) = 0`).
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate ContinuousLinearMap Filter Topology
open SymplecticPacking.Forms (Form1 Form2 d1 d1_apply d1_skew fderiv_eval1 isClosed2_d1_at)
open scoped Real ContDiff

/-! ### Definitions -/

/-- The potential `Φ_E(Z, W) = log ‖Z‖² + d_n log(1 + |W|²/‖Z‖⁶)` (meaningful for `Z ≠ 0`). -/
def PhiE (dn : ℝ) (x : C3 × ℂ) : ℝ :=
  Real.log (nsq x.1) + dn * Real.log (1 + normSq x.2 / nsq x.1 ^ 3)

/-- `λ_E = d^c Φ_E`. -/
def lamE (dn : ℝ) : Form1 (C3 × ℂ) := dc (PhiE dn)

/-- `Ω_E = d λ_E = dd^c Φ_E`. -/
def OmegaE (dn : ℝ) : Form2 (C3 × ℂ) := d1 (lamE dn)

/-- Real part of `η_H = (2πi)⁻¹ Z† dZ`. -/
def etaH (Z U : C3) : ℝ := (herm Z U).im / (2 * π)

/-- `α = d(arg W)/(2π) − 3 η_H` (unit representatives, `W ≠ 0`). -/
def alphaE (Z : C3) (W : ℂ) (v : C3 × ℂ) : ℝ := ((v.2 / W).im - 3 * (herm Z v.1).im) / (2 * π)

/-! ### Smoothness -/

lemma nsq_eq_sum_norm (Z : C3) : nsq Z = ∑ j, ‖Z j‖ ^ 2 := by
  simp [nsq, normSq_eq_norm_sq]

lemma contDiff_normSq' {n : WithTop ℕ∞} : ContDiff ℝ n (fun w : ℂ => normSq w) := by
  have : (fun w : ℂ => normSq w) = fun w => ‖w‖ ^ 2 := by funext w; exact normSq_eq_norm_sq w
  rw [this]; exact contDiff_norm_sq ℝ

lemma contDiff_nsq {n : WithTop ℕ∞} : ContDiff ℝ n nsq := by
  have : nsq = fun Z : C3 => ∑ j, ‖Z j‖ ^ 2 := funext nsq_eq_sum_norm
  rw [this]
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)

lemma nsq_eq_zero {Z : C3} : nsq Z = 0 ↔ Z = 0 := by
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => normSq_nonneg (Z j))).mp h
    funext j; exact normSq_eq_zero.mp (h' j (Finset.mem_univ j))
  · rintro rfl; simp [nsq]

lemma nsq_pos {Z : C3} (h : Z ≠ 0) : 0 < nsq Z :=
  lt_of_le_of_ne (nsq_nonneg Z) (Ne.symm (mt nsq_eq_zero.mp h))

lemma contDiffAt_PhiE (dn : ℝ) {x : C3 × ℂ} (hx : 0 < nsq x.1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (PhiE dn) x := by
  have h1 : ContDiff ℝ n fun y : C3 × ℂ => nsq y.1 := contDiff_nsq.comp contDiff_fst
  have h2 : ContDiff ℝ n fun y : C3 × ℂ => normSq y.2 := contDiff_normSq'.comp contDiff_snd
  have hpos : 0 < 1 + normSq x.2 / nsq x.1 ^ 3 := by
    have := normSq_nonneg x.2; positivity
  exact (h1.contDiffAt.log hx.ne').add (contDiffAt_const.mul
    ((contDiffAt_const.add (h2.contDiffAt.div (h1.contDiffAt.pow 3)
      (pow_ne_zero 3 hx.ne'))).log hpos.ne'))

lemma differentiableAt_PhiE (dn : ℝ) {x : C3 × ℂ} (hx : 0 < nsq x.1) :
    DifferentiableAt ℝ (PhiE dn) x :=
  (contDiffAt_PhiE dn hx (n := 1)).differentiableAt (by norm_num)

lemma differentiableAt_lamE (dn : ℝ) {x : C3 × ℂ} (hx : 0 < nsq x.1) :
    DifferentiableAt ℝ (lamE dn) x :=
  differentiableAt_dc (contDiffAt_PhiE dn hx)

/-- `Ω_E` is closed. -/
theorem OmegaE_closed (dn : ℝ) {x : C3 × ℂ} (hx : x.1 ≠ 0) (u v w : C3 × ℂ) :
    fderiv ℝ (OmegaE dn) x u v w - fderiv ℝ (OmegaE dn) x v u w +
      fderiv ℝ (OmegaE dn) x w u v = 0 :=
  isClosed2_d1_at (contDiffAt_dc (contDiffAt_PhiE dn (nsq_pos hx))) u v w

/-! ### Quantities along lines -/

lemma nsq_add_smul (Z U : C3) (t : ℝ) :
    nsq (Z + t • U) = nsq Z + 2 * t * (herm Z U).re + t ^ 2 * nsq U := by
  simp only [nsq, herm, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, normSq_add_smul,
    add_re]
  ring

lemma herm_add_smul_im (Z U X : C3) (t : ℝ) :
    (herm (Z + t • U) X).im = (herm Z X).im + t * (herm U X).im := by
  simp only [herm, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, real_smul, map_add, map_mul,
    conj_ofReal, add_mul, add_im, mul_im, mul_re, ofReal_re, ofReal_im]
  ring

lemma conj_add_smul_im (W U X : ℂ) (t : ℝ) :
    (conj (W + t • U) * X).im = (conj W * X).im + t * (conj U * X).im := by
  simp only [real_smul, map_add, map_mul, conj_ofReal, add_mul, add_im, mul_im, mul_re,
    ofReal_re, ofReal_im]
  ring

lemma herm_I_right (Z U : C3) : herm Z (I • U) = I * herm Z U := herm_smul_right _ _ _

lemma re_I_mul (z : ℂ) : (I * z).re = -z.im := by simp

lemma hasDerivAt_quad (c0 c1 c2 : ℝ) :
    HasDerivAt (fun t : ℝ => c0 + 2 * t * c1 + t ^ 2 * c2) (2 * c1) 0 := by
  have := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const c1).const_add c0).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c2)
  convert this using 1
  · funext t; simp only [Pi.add_apply, id, Pi.pow_apply]
  · simp

lemma hasDerivAt_lin (c0 c1 : ℝ) : HasDerivAt (fun t : ℝ => c0 + t * c1) c1 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c1).const_add c0

/-! ### The explicit formula for `λ_E` -/

/-- Derivative of the potential along a curve with `q = ‖Z‖² > 0`, `r = |W|²`. -/
lemma hasDerivAt_potential (dn : ℝ) {q r : ℝ → ℝ} {q' r' : ℝ} (hq : HasDerivAt q q' 0)
    (hr : HasDerivAt r r' 0) (hq0 : 0 < q 0) (hr0 : 0 ≤ r 0) :
    HasDerivAt (fun t => Real.log (q t) + dn * Real.log (1 + r t / q t ^ 3))
      (q' / q 0 + dn * ((r' * q 0 - 3 * r 0 * q') / (q 0 * (q 0 ^ 3 + r 0)))) 0 := by
  have hq3 : q 0 ^ 3 ≠ 0 := by positivity
  have hpos : 1 + r 0 / q 0 ^ 3 ≠ 0 := by positivity
  have := (hq.log hq0.ne').add ((((hr.div (hq.pow 3) hq3).const_add 1).log hpos).const_mul dn)
  convert this using 1
  have h4 : q 0 ^ 3 + r 0 ≠ 0 := by positivity
  simp only [Pi.pow_apply, Pi.div_apply]
  field_simp
  push_cast
  ring

/-- `λ_E` at a point with `Z ≠ 0`, `a = Im(Z†Ż)`, `b = Im(conj W Ẇ)`, `Q = ‖Z‖²`, `R = |W|²`:
`λ_E(Ż, Ẇ) = (1/2π) (a/Q + d_n (Q b − 3 R a)/(Q (Q³ + R)))`. -/
def lamExp (dn : ℝ) (x w : C3 × ℂ) : ℝ :=
  1 / (2 * π) * ((herm x.1 w.1).im / nsq x.1 +
    dn * ((nsq x.1 * (conj x.2 * w.2).im - 3 * normSq x.2 * (herm x.1 w.1).im) /
      (nsq x.1 * (nsq x.1 ^ 3 + normSq x.2))))

theorem lamE_eq (dn : ℝ) {x : C3 × ℂ} (hx : 0 < nsq x.1) (w : C3 × ℂ) :
    lamE dn x w = lamExp dn x w := by
  have hline : HasDerivAt (fun t : ℝ => PhiE dn (x + t • (I • w)))
      (2 * (herm x.1 (I • w.1)).re / nsq x.1 + dn * ((2 * (conj x.2 * (I * w.2)).re * nsq x.1 -
        3 * normSq x.2 * (2 * (herm x.1 (I • w.1)).re)) /
          (nsq x.1 * (nsq x.1 ^ 3 + normSq x.2)))) 0 := by
    have h := hasDerivAt_potential dn (hasDerivAt_quad (nsq x.1) (herm x.1 (I • w.1)).re
      (nsq (I • w.1))) (hasDerivAt_quad (normSq x.2) (conj x.2 * (I * w.2)).re
      (normSq (I * w.2))) (by simpa using hx) (by simpa using normSq_nonneg x.2)
    convert h using 1
    · funext t
      simp only [PhiE, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        nsq_add_smul, normSq_add_smul, smul_eq_mul]
    · simp
  rw [lamE, dc_apply, fderiv_apply_of_line (differentiableAt_PhiE dn hx) hline, lamExp,
    herm_I_right, re_I_mul]
  have h2 : (conj x.2 * (I * w.2)).re = -(conj x.2 * w.2).im := by
    rw [mul_left_comm, re_I_mul]
  rw [h2]
  have hq := hx.ne'
  have h4 : nsq x.1 ^ 3 + normSq x.2 ≠ 0 := by have := normSq_nonneg x.2; positivity
  field_simp
  ring

/-- Lemma lem:rtc-dc, at a unit representative:
`λ_E = η_H + d_n (1/(2π)) (Im(conj W Ẇ) − 3|W|² Im(Z†Ż))/(1 + |W|²)`, i.e.
`d^c log(1 + ‖W‖²) = |W|²/(1+|W|²) · α` (smooth across `W = 0`). -/
theorem dc_log_one_add (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (w : C3 × ℂ) :
    lamE dn (Z, W) w = etaH Z w.1 +
      dn * (((conj W * w.2).im - 3 * normSq W * (herm Z w.1).im) / (2 * π * (1 + normSq W))) := by
  rw [lamE_eq dn (by simp [hZ]), lamExp, etaH]
  simp only [hZ]
  have h1 : 0 < 1 + normSq W := one_add_normSq_pos W
  field_simp

/-- Lemma lem:rtc-dc, first identity: `d^c log ‖W‖² = α` (unit representative, `W ≠ 0`),
where `‖W‖² = |W|²/‖Z‖⁶`. -/
theorem dc_log_normW {Z : C3} (hZ : nsq Z = 1) {W : ℂ} (hW : W ≠ 0) (w : C3 × ℂ) :
    dc (fun x : C3 × ℂ => Real.log (normSq x.2 / nsq x.1 ^ 3)) (Z, W) w = alphaE Z W w := by
  have hR : 0 < normSq W := normSq_pos.mpr hW
  have hdiff : DifferentiableAt ℝ (fun x : C3 × ℂ => Real.log (normSq x.2 / nsq x.1 ^ 3))
      (Z, W) := by
    have h1 : ContDiff ℝ 1 fun y : C3 × ℂ => nsq y.1 := contDiff_nsq.comp contDiff_fst
    have h2 : ContDiff ℝ 1 fun y : C3 × ℂ => normSq y.2 := contDiff_normSq'.comp contDiff_snd
    have := ((h2.contDiffAt (x := (Z, W))).div (h1.contDiffAt.pow 3) (by simp [hZ])).log
      (by simp [hZ, hR.ne'])
    exact this.differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => Real.log (normSq ((Z, W) + t • (I • w)).2 /
      nsq ((Z, W) + t • (I • w)).1 ^ 3))
      ((2 * (conj W * (I * w.2)).re * 1 ^ 3 - normSq W * (3 * 1 ^ 2 *
        (2 * (herm Z (I • w.1)).re))) / (1 ^ 3) ^ 2 / (normSq W / 1 ^ 3)) 0 := by
    have hq := hasDerivAt_quad (nsq Z) (herm Z (I • w.1)).re (nsq (I • w.1))
    have hr := hasDerivAt_quad (normSq W) (conj W * (I * w.2)).re (normSq (I * w.2))
    have h := (hr.div (hq.pow 3) (by simp [hZ])).log (by simp [hZ, hR.ne'])
    convert h using 1
    · funext t
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        nsq_add_smul, normSq_add_smul, smul_eq_mul, Pi.div_apply, Pi.pow_apply]
    · simp [hZ]
  rw [dc_apply, fderiv_apply_of_line hdiff hline, alphaE, herm_I_right, re_I_mul]
  have h2 : (conj W * (I * w.2)).re = -(conj W * w.2).im := by
    rw [mul_left_comm, re_I_mul]
  have hb : (conj W * w.2).im = normSq W * (w.2 / W).im := by
    rw [div_eq_mul_inv, inv_def]
    simp only [mul_im, mul_re, conj_re, conj_im, ofReal_re, ofReal_im]
    field_simp
    ring
  rw [h2, hb]
  field_simp
  ring

/-! ### `Ω_E` at a unit representative -/

/-- Derivative of the explicit `λ_E` along a curve through a unit representative. -/
lemma hasDerivAt_lamExp_curve (dn : ℝ) {q r a b : ℝ → ℝ} {q' r' a' b' : ℝ}
    (hq : HasDerivAt q q' 0) (hr : HasDerivAt r r' 0) (ha : HasDerivAt a a' 0)
    (hb : HasDerivAt b b' 0) (hq0 : q 0 = 1) (hr0 : 0 ≤ r 0) :
    HasDerivAt (fun t => 1 / (2 * π) * (a t / q t +
      dn * ((q t * b t - 3 * r t * a t) / (q t * (q t ^ 3 + r t)))))
      (1 / (2 * π) * (a' - a 0 * q' + dn * ((q' * b 0 + b' - 3 * r' * a 0 - 3 * r 0 * a') /
        (1 + r 0) - (b 0 - 3 * r 0 * a 0) * (q' * (4 + r 0) + r') / (1 + r 0) ^ 2))) 0 := by
  have hd0 : q 0 * (q 0 ^ 3 + r 0) ≠ 0 := by rw [hq0]; positivity
  have h := ((ha.div hq (by rw [hq0]; norm_num)).add
    ((((hq.mul hb).sub ((hr.const_mul 3).mul ha)).div (hq.mul ((hq.pow 3).add hr)) hd0).const_mul
      dn)).const_mul (1 / (2 * π))
  convert h using 1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  rw [hq0]
  have h1 : (1 + r 0) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The derivative `D_v(λ_E(·)(w))` at a unit representative, divided by `1/(2π)`. -/
def DfE (dn : ℝ) (Z : C3) (W : ℂ) (v w : C3 × ℂ) : ℝ :=
  (herm v.1 w.1).im - (herm Z w.1).im * (2 * (herm Z v.1).re) +
    dn * ((2 * (herm Z v.1).re * (conj W * w.2).im + (conj v.2 * w.2).im -
        3 * (2 * (conj W * v.2).re) * (herm Z w.1).im - 3 * normSq W * (herm v.1 w.1).im) /
        (1 + normSq W) -
      ((conj W * w.2).im - 3 * normSq W * (herm Z w.1).im) *
        (2 * (herm Z v.1).re * (4 + normSq W) + 2 * (conj W * v.2).re) / (1 + normSq W) ^ 2)

theorem fderiv_lamE_unit (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (v w : C3 × ℂ) :
    fderiv ℝ (lamE dn) (Z, W) v w = 1 / (2 * π) * DfE dn Z W v w := by
  have hx : 0 < nsq (Z, W).1 := by simp [hZ]
  have hL := differentiableAt_lamE dn hx
  rw [← fderiv_eval1 hL]
  have hg : DifferentiableAt ℝ (fun y => lamE dn y w) (Z, W) :=
    hL.clm_apply (differentiableAt_const w)
  apply fderiv_apply_of_line hg
  -- the explicit curve
  have hq := hasDerivAt_quad (nsq Z) (herm Z v.1).re (nsq v.1)
  have hr := hasDerivAt_quad (normSq W) (conj W * v.2).re (normSq v.2)
  have ha := hasDerivAt_lin (herm Z w.1).im (herm v.1 w.1).im
  have hb := hasDerivAt_lin (conj W * w.2).im (conj v.2 * w.2).im
  have h := hasDerivAt_lamExp_curve dn hq hr ha hb (by simp [hZ]) (by simp [normSq_nonneg])
  have h' : HasDerivAt (fun t : ℝ => lamExp dn ((Z, W) + t • v) w)
      (1 / (2 * π) * DfE dn Z W v w) 0 := by
    convert h using 1
    · funext t
      simp only [lamExp, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        nsq_add_smul, normSq_add_smul, herm_add_smul_im, conj_add_smul_im]
    · simp only [DfE]; ring
  apply h'.congr_of_eventuallyEq
  -- `λ_E = lamExp` near the curve
  have hc : ContinuousAt (fun t : ℝ => nsq Z + 2 * t * (herm Z v.1).re + t ^ 2 * nsq v.1) 0 :=
    hq.continuousAt
  have hev := continuousAt_const.eventually_lt hc
    (by simp [hZ] : (0 : ℝ) < nsq Z + 2 * 0 * (herm Z v.1).re + 0 ^ 2 * nsq v.1)
  filter_upwards [hev] with t ht
  apply lamE_eq dn
  simpa [nsq_add_smul] using ht

/-- `Ω_E` at a unit representative, for arbitrary tangent vectors. -/
theorem OmegaE_unit (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (v w : C3 × ℂ) :
    OmegaE dn (Z, W) v w = 1 / (2 * π) * (DfE dn Z W v w - DfE dn Z W w v) := by
  rw [OmegaE, d1_apply, fderiv_lamE_unit dn hZ, fderiv_lamE_unit dn hZ]; ring

lemma herm_swap_im (a b : C3) : (herm b a).im = -(herm a b).im := by
  rw [← herm_conj, conj_im]

/-- Lemma lem:rtc-kahler: in the gauge `Z†Ż₁ = Z†Ż₂ = 0`,
`Ω_E((Ż₁,Ẇ₁),(Ż₂,Ẇ₂)) = (1/π) Im(A Ż₁†Ż₂ + B conj(Ẇ₁) Ẇ₂)`. -/
theorem OmegaE_herm (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (v w : C3 × ℂ)
    (hv : herm Z v.1 = 0) (hw : herm Z w.1 = 0) :
    OmegaE dn (Z, W) v w =
      1 / π * ((Acoef dn W : ℂ) * herm v.1 w.1 + (Bcoef dn W : ℂ) * (conj v.2 * w.2)).im := by
  rw [OmegaE_unit dn hZ, DfE, DfE, hv, hw, herm_swap_im v.1 w.1]
  simp only [zero_re, zero_im, Acoef, Bcoef, pW, add_im, mul_im, mul_re, conj_re, conj_im,
    ofReal_re, ofReal_im, normSq_apply]
  have h1 : 0 < 1 + (W.re * W.re + W.im * W.im) := by nlinarith [sq_nonneg W.re, sq_nonneg W.im]
  field_simp
  ring

/-! ### Degeneracy along the `ℂ*`-orbits -/

/-- The infinitesimal orbit direction of `λ ↦ (λZ, λ³W)` at `λ = 1`. -/
def orbitVec (Z : C3) (W : ℂ) : C3 × ℂ := (Z, 3 * W)

lemma herm_self_unit {Z : C3} (hZ : nsq Z = 1) : herm Z Z = 1 := by
  rw [herm_self, hZ, ofReal_one]

theorem OmegaE_orbit (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (w : C3 × ℂ) :
    OmegaE dn (Z, W) (orbitVec Z W) w = 0 := by
  rw [OmegaE_unit dn hZ, DfE, DfE]
  simp only [orbitVec, herm_self_unit hZ, ← herm_conj w.1 Z]
  set α := herm Z w.1
  simp only [one_re, one_im, conj_re, conj_im, mul_im, mul_re, normSq_apply, re_ofNat,
    im_ofNat]
  have h1 : 0 < 1 + (W.re * W.re + W.im * W.im) := by nlinarith [sq_nonneg W.re, sq_nonneg W.im]
  field_simp
  ring

theorem OmegaE_orbitI (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (w : C3 × ℂ) :
    OmegaE dn (Z, W) (I • orbitVec Z W) w = 0 := by
  rw [OmegaE_unit dn hZ, DfE, DfE]
  simp only [orbitVec, Prod.smul_mk, smul_eq_mul, herm_smul_left, herm_smul_right,
    herm_self_unit hZ, ← herm_conj w.1 Z]
  set α := herm Z w.1
  simp only [conj_re, conj_im, mul_im, mul_re, normSq_apply, re_ofNat,
    im_ofNat, I_re, I_im, map_mul, conj_I, mul_one, neg_re, neg_im]
  have h1 : 0 < 1 + (W.re * W.re + W.im * W.im) := by nlinarith [sq_nonneg W.re, sq_nonneg W.im]
  field_simp
  ring

theorem OmegaE_orbit_right (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (w : C3 × ℂ) :
    OmegaE dn (Z, W) w (orbitVec Z W) = 0 := by
  rw [OmegaE, d1_skew, ← OmegaE, OmegaE_orbit dn hZ, neg_zero]

theorem OmegaE_orbitI_right (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (w : C3 × ℂ) :
    OmegaE dn (Z, W) w (I • orbitVec Z W) = 0 := by
  rw [OmegaE, d1_skew, ← OmegaE, OmegaE_orbitI dn hZ, neg_zero]

/-! ### Positivity on the gauge slice -/

/-- `Ω_E(ξ, iξ) = (1/π)(A ‖Ż‖² + B |Ẇ|²)` in the gauge. -/
theorem OmegaE_I_self (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (W : ℂ) (v : C3 × ℂ)
    (hv : herm Z v.1 = 0) :
    OmegaE dn (Z, W) v (I • v) = 1 / π * (Acoef dn W * nsq v.1 + Bcoef dn W * normSq v.2) := by
  have hIv : herm Z (I • v).1 = 0 := by
    rw [Prod.smul_fst, herm_smul_right, hv, mul_zero]
  have h2 : conj v.2 * (I * v.2) = I * (normSq v.2 : ℂ) := by
    rw [mul_left_comm, ← ofReal_normSq']
  rw [OmegaE_herm dn hZ W v (I • v) hv hIv, Prod.smul_fst, Prod.smul_snd, herm_smul_right,
    herm_self, smul_eq_mul, h2]
  simp

/-- Lemma lem:rtc-kahler (positivity): for `0 < d_n ≤ 1/3`, `Ω_E(ξ, iξ) > 0` for every
nonzero `ξ` in the gauge slice `Z†Ż = 0`. -/
theorem OmegaE_pos {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} (hZ : nsq Z = 1)
    (W : ℂ) (v : C3 × ℂ) (hv : herm Z v.1 = 0) (hne : v ≠ 0) :
    0 < OmegaE dn (Z, W) v (I • v) := by
  rw [OmegaE_I_self dn hZ W v hv]
  have hA := Acoef_pos hdn hdn3 W
  have hB := Bcoef_pos hdn W
  have h0 : 0 < nsq v.1 ∨ 0 < normSq v.2 := by
    by_contra h
    push Not at h
    have h1 : v.1 = 0 := nsq_eq_zero.mp (le_antisymm h.1 (nsq_nonneg _))
    have h2 : v.2 = 0 := normSq_eq_zero.mp (le_antisymm h.2 (normSq_nonneg _))
    exact hne (Prod.ext h1 h2)
  have := nsq_nonneg v.1
  have := normSq_nonneg v.2
  rcases h0 with h0 | h0 <;> positivity

/-! ### Isotropy of the transport field (Lemma lem:rtc-transport-field (iv)) -/

lemma dF_sub (Z a b : C3) : dF Z (a - b) = dF Z a - dF Z b := by
  simp only [dF, Fin.sum_univ_three, Pi.sub_apply]; ring

lemma dF_smul (Z a : C3) (c : ℂ) : dF Z (c • a) = c * dF Z a := by
  simp only [dF, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

lemma dF_self (Z : C3) : dF Z Z = 3 * Fpoly Z := by
  simp only [dF, Fpoly, Fin.sum_univ_three]; ring

/-- At a point of `X_T` (`‖Z‖ = 1`, `F(Z) = T W`), the `(Z, W)`-part of the transport field is
`Ω_E`-orthogonal to every vector `ξ = (Ż, Ẇ)` tangent to `X_T`, i.e. with
`dF_Z(Ż) = T Ẇ` (no gauge condition on `ξ`; the orbit components are killed by degeneracy). -/
theorem transport_isotropic {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} {W : ℂ}
    {T : ℝ} (hZ : nsq Z = 1) (hX : Fpoly Z = T * W) (hN : Nden dn Z W T ≠ 0)
    (ξ : C3 × ℂ) (hξ : dF Z ξ.1 = T * ξ.2) :
    OmegaE dn (Z, W) (transportField dn Z W T) ξ = 0 := by
  set c := herm Z ξ.1
  set ξh : C3 × ℂ := (ξ.1 - c • Z, ξ.2 - 3 * c * W)
  have hdec : ξ = ξh + c.re • orbitVec Z W + c.im • (I • orbitVec Z W) := by
    have key : (c.re : ℂ) + c.im * I = c := re_add_im c
    ext j
    · simp only [ξh, orbitVec, Prod.fst_add, Prod.smul_mk, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, real_smul]
      linear_combination (-(Z j)) * key
    · simp only [ξh, orbitVec, Prod.snd_add, Prod.smul_mk, smul_eq_mul, real_smul]
      linear_combination (-(3 * W)) * key
  have hξh : herm Z ξh.1 = 0 := by
    simp only [ξh]
    rw [sub_eq_add_neg, ← neg_smul, herm_add_right, herm_smul_right, herm_self_unit hZ]
    simp [c]
  have hV := transport_horizontal dn Z W T hZ
  have hA := (Acoef_pos hdn hdn3 W).ne'
  have hB := (Bcoef_pos hdn W).ne'
  rw [hdec, map_add, map_add, map_smul, map_smul, OmegaE_orbit_right dn hZ,
    OmegaE_orbitI_right dn hZ, smul_zero, smul_zero, add_zero, add_zero,
    OmegaE_herm dn hZ W _ _ hV hξh, ← mul_assoc, transport_orthogonal dn Z W T hA hB hN,
    n_dF Z _ hξh]
  have : dF Z ξh.1 - T * ξh.2 = 0 := by
    simp only [ξh]
    rw [dF_sub, dF_smul, dF_self, hξ, hX]
    ring
  rw [this, mul_zero, zero_im, mul_zero]

/-- The same on the constraint set `0 ≤ T` (where `N_den > 0` by `Nden_pos`). -/
theorem transport_isotropic' {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} {W : ℂ}
    {T : ℝ} (hZ : nsq Z = 1) (hX : Fpoly Z = T * W) (hT : 0 ≤ T)
    (ξ : C3 × ℂ) (hξ : dF Z ξ.1 = T * ξ.2) :
    OmegaE dn (Z, W) (transportField dn Z W T) ξ = 0 :=
  transport_isotropic hdn hdn3 hZ hX (Nden_pos hdn hdn3 hZ hX hT).ne' ξ hξ

end SymplecticPacking.Return
