import SymplecticPacking.Bundle.OmegaT
import SymplecticPacking.Qhat.Main

/-!
# Local coordinates of the handle

`sec:shd-four` (`eq:shd4-twist`): the local coordinates of the handle over the annulus, and
calculus helpers for the local model. The twist `𝒟_λ` and the suspension identity
(`lem:shd4-suspension`) for cubic data are in `Branch2/Model/Cubic/Handle/Twist.lean`.

Local coordinates. On `E4 = ℝ⁴` we use, for the handle, the coordinates `(x, y, s, t)`
(indices `0, 1, 2, 3`), where `w = x + iy` (`wL`) is the fibre coordinate in the `𝒜⁺`-frame
`(Z₀/|Z₀|)³` and `(s, t) = (u, v)` are the torus coordinates. `p = π|w|²` is `Bundle.pE`. The
passage to the global `Zunit`-frame coordinates is the fibre rotation `chartA` of
`Handle/Frame.lean`.

* `mk w s t` is the point with coordinates `(w, s, t)`; `pE_mk`: `p = π|w|²`;
  `omegaV = dx ∧ dy`.
* Exterior derivatives and pullbacks of forms on `E4`: `d1_smul_const_form`, `d1_congr`,
  `pull2_add`, `pull2_smul`, `omega2_self`.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e
  d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus contDiff_stepA
  contDiff_deriv_stepA)
open SymplecticPacking.Qhat (qhatP qhatInvP QhamP qhatP_spec hamVF2 omega2 omega2_map Psupp)
open scoped ContDiff Real

/-! ### Coordinates -/

/-- The fibre coordinate `w = x + iy` as a linear map `E4 → ℂ`. -/
def wL : E4 →L[ℝ] ℂ := (dc 0).smulRight (1 : ℂ) + (dc 1).smulRight Complex.I

@[simp] lemma wL_re (X : E4) : (wL X).re = X 0 := by simp [wL]
@[simp] lemma wL_im (X : E4) : (wL X).im = X 1 := by simp [wL]

/-- The point with coordinates `(w, s, t)`, as a continuous linear map of `(w, s, t)`. -/
def mkL : ℂ × ℝ × ℝ →L[ℝ] E4 :=
  (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ))).smulRight (e 0) +
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ))).smulRight (e 1) +
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))).smulRight (e 2) +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))).smulRight (e 3)

/-- The point with fibre coordinate `w` over the base point `(s, t)`. -/
def mk (w : ℂ) (s t : ℝ) : E4 := mkL (w, s, t)

lemma mk_eq (w : ℂ) (s t : ℝ) : mk w s t = w.re • e 0 + w.im • e 1 + s • e 2 + t • e 3 := by
  simp [mk, mkL]

@[simp] lemma mk_apply0 (w : ℂ) (s t : ℝ) : mk w s t 0 = w.re := by simp [mk_eq]
@[simp] lemma mk_apply1 (w : ℂ) (s t : ℝ) : mk w s t 1 = w.im := by simp [mk_eq]
@[simp] lemma mk_apply2 (w : ℂ) (s t : ℝ) : mk w s t 2 = s := by simp [mk_eq]
@[simp] lemma mk_apply3 (w : ℂ) (s t : ℝ) : mk w s t 3 = t := by simp [mk_eq]
@[simp] lemma wL_mk (w : ℂ) (s t : ℝ) : wL (mk w s t) = w := by
  apply Complex.ext <;> simp
@[simp] lemma mk_wL (X : E4) : mk (wL X) (X 2) (X 3) = X := by
  ext i; fin_cases i <;> simp

lemma dc_apply (i : Fin 4) (X : E4) : dc i X = X i := rfl

@[simp] lemma wL_e2 : wL (e 2) = 0 := by apply Complex.ext <;> simp
@[simp] lemma wL_e3 : wL (e 3) = 0 := by apply Complex.ext <;> simp

/-- `p = π |w|²`. -/
lemma pE_eq (X : E4) : pE X = π * ‖wL X‖ ^ 2 := by
  rw [pE, Complex.sq_norm, Complex.normSq_apply, wL_re, wL_im, dc_apply, dc_apply]; ring

@[simp] lemma pE_mk (w : ℂ) (s t : ℝ) : pE (mk w s t) = π * ‖w‖ ^ 2 := by rw [pE_eq, wL_mk]

lemma contDiff_fibreArea : ContDiff ℝ ∞ (fun w : ℂ => π * ‖w‖ ^ 2) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

/-- The vertical form `ω_V = dx ∧ dy`. -/
def omegaV : Form2 E4 := fun _ => wedge (dc 0) (dc 1)

lemma omegaV_apply (X v w : E4) : omegaV X v w = omega2 (wL v) (wL w) := by
  simp [omegaV, omega2]; ring

/-! ### Generic calculus helpers -/

/-- `d(g · L) = dg ∧ L` for a constant covector `L`. -/
lemma d1_smul_const_form {g : E4 → ℝ} {L : E4 →L[ℝ] ℝ} {X : E4} (hg : DifferentiableAt ℝ g X) :
    d1 (fun Y => g Y • L) X = wedge (fderiv ℝ g X) L := by
  have h : HasFDerivAt (fun Y => g Y • L) ((fderiv ℝ g X).smulRight L) X :=
    hg.hasFDerivAt.smul_const L
  ext v w
  simp only [Forms.d1_apply, h.fderiv, smulRight_apply, wedge_apply, smul_apply, smul_eq_mul]

/-- `d1` only depends on the germ. -/
lemma d1_congr {α β : Form1 E4} {X : E4} (h : α =ᶠ[𝓝 X] β) : d1 α X = d1 β X := by
  simp only [d1, h.fderiv_eq]

/-- Pullback is additive in the form. -/
lemma pull2_add (φ : E4 → E4) (Ω₁ Ω₂ : Form2 E4) (X : E4) :
    pull2 φ (Ω₁ + Ω₂) X = pull2 φ Ω₁ X + pull2 φ Ω₂ X := by
  ext v w; simp

lemma pull2_smul (φ : E4 → E4) (c : ℝ) (Ω : Form2 E4) (X : E4) :
    pull2 φ (c • Ω) X = c • pull2 φ Ω X := by
  ext v w; simp

/-- Splitting the derivative of a function on `ℝ × E` into its two partial derivatives. -/
lemma fderiv_prod_apply {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : ℝ × E → G} {t : ℝ} {y : E}
    (hF : DifferentiableAt ℝ F (t, y)) (a : ℝ) (b : E) :
    fderiv ℝ F (t, y) (a, b) =
      a • deriv (fun t' => F (t', y)) t + fderiv ℝ (fun y' => F (t, y')) y b := by
  have h1 : HasDerivAt (fun t' => F (t', y)) (fderiv ℝ F (t, y) (1, 0)) t := by
    have hl : HasDerivAt (fun t' : ℝ => ((t', y) : ℝ × E)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact hF.hasFDerivAt.comp_hasDerivAt t hl
  have h2 : HasFDerivAt (fun y' => F (t, y'))
      ((fderiv ℝ F (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    have hl : HasFDerivAt (fun y' : E => ((t, y') : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
    exact hF.hasFDerivAt.comp y hl
  rw [h1.deriv, h2.fderiv]
  have : ((a, b) : ℝ × E) = a • ((1 : ℝ), (0 : E)) + ((0 : ℝ), b) := by ext <;> simp
  rw [this, map_add, map_smul]
  simp

/-! ### The isotopy as a function of two variables -/

variable (P : Params)

/-! ### The twist map (`eq:shd4-twist`) -/

/-- **The partial twist** `𝒟_λ(s, t, w) = (s, t, q_{λ f(s)}(w))`. -/
def Dlam (lam : ℝ) (X : E4) : E4 := mk (qhatP P (lam * stepA (X 2)) (wL X)) (X 2) (X 3)

/-- **The `s`-generator** `Q^λ_s = λ f'(s) Q_{λ f(s)}`. -/
def Qs (lam s : ℝ) (y : ℂ) : ℝ := lam * deriv stepA s * QhamP P (lam * stepA s) y

/-- **The first-stage coefficient** `G_λ(s, w) = f(s) H*(p(q_λ⁻¹ w))`. -/
def Glam (lam s : ℝ) (w : ℂ) : ℝ := stepA s * P.Hstar (π * ‖qhatInvP P lam w‖ ^ 2)

@[simp] lemma Dlam_apply2 (lam : ℝ) (X : E4) : Dlam P lam X 2 = X 2 := by simp [Dlam]
@[simp] lemma Dlam_apply3 (lam : ℝ) (X : E4) : Dlam P lam X 3 = X 3 := by simp [Dlam]
@[simp] lemma wL_Dlam (lam : ℝ) (X : E4) :
    wL (Dlam P lam X) = qhatP P (lam * stepA (X 2)) (wL X) := by simp [Dlam]

lemma contDiff_tau (lam : ℝ) : ContDiff ℝ ∞ (fun Y : E4 => lam * stepA (Y 2)) :=
  contDiff_const.mul (contDiff_stepA.comp (dc 2).contDiff)

lemma omega2_self (a : ℂ) : omega2 a a = 0 := by simp [omega2]; ring

/-! ### The suspension identity (`lem:shd4-suspension`) -/

/-- `Φ = Q^λ_s ∘ q_{λ f(s)}` as a function on `E4`. -/
def PhiS (lam : ℝ) (X : E4) : ℝ := Qs P lam (X 2) (qhatP P (lam * stepA (X 2)) (wL X))

end SymplecticPacking.Handle
