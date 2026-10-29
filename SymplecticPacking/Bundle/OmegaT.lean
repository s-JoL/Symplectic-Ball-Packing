import SymplecticPacking.Bundle.Alpha1

/-!
# The local form `Ω₀` and the first Moser path

`sec:fer` (`lem:fer-positivity`): the local formula for `Ω₀` in the global frame `Zunit` of the
cover and the first Moser path `Ω_t = Ω₀ + t dα₁`.

Coordinates on `E4 = ℝ⁴`: `(x, y, u, v)` = indices `(0, 1, 2, 3)`; `w = x + iy` is the fibre
coordinate in the frame `Zunit(u, v)`, `p = π(x² + y²)` (`pE`, with derivative `dpE`).
* `hasFDerivAt_lift`: the ambient derivative of a lifted coefficient `f(u, v, p)` that is affine
  in `p`.
* `Omega0loc` is the local formula `Ω₀ = ω_V + (1 − 3p)σ + dp ∧ a_loc` (eq:fer-Omega0-local),
  `ω_V = dx ∧ dy`, `a_loc = −3 Zunit^* η_H` (`aloc`).
* `alpha1E` is `α₁` as an ambient one-form (no `dx`, `dy` components), `OmegaT P t = Ω₀ + t dα₁`
  with the ambient exterior derivative `Forms.d1`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 Form1 Form2 splitForm pf pf_splitForm
  splitForm_nondeg)
open scoped ContDiff Real

/-- `p = π(x² + y²)`. -/
def pE (X : E4) : ℝ := π * (dc 0 X ^ 2 + dc 1 X ^ 2)

/-- `dp = 2π(x dx + y dy)`. -/
def dpE (X : E4) : E4 →L[ℝ] ℝ := (2 * π * dc 0 X) • dc 0 + (2 * π * dc 1 X) • dc 1

lemma hasFDerivAt_pE (X : E4) : HasFDerivAt pE (dpE X) X := by
  have h := (((dc 0).hasFDerivAt (x := X)).pow 2 |>.add (((dc 1).hasFDerivAt (x := X)).pow 2)).const_mul π
  refine h.congr_fderiv ?_
  ext w
  simp [dpE, smul_eq_mul]
  ring

lemma clm_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) : L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The ambient derivative of a lifted coefficient `Y ↦ f(u(Y), v(Y), p(Y))`, for `f` affine in
`p` with smooth slices: `∂_u f du + ∂_v f dv + ∂_p f dp`. -/
lemma hasFDerivAt_lift {f : Coef} (hf : AffineP f) (h0 : ContDiff ℝ ∞ (sl f 0))
    (h1 : ContDiff ℝ ∞ (sl f 1)) (X : E4) :
    HasFDerivAt (fun Y => f (dc 2 Y) (dc 3 Y) (pE Y))
      (pu f (dc 2 X) (dc 3 X) (pE X) • dc 2 + pv f (dc 2 X) (dc 3 X) (pE X) • dc 3 +
        pp f (dc 2 X) (dc 3 X) (pE X) • dpE X) X := by
  set π23 : E4 →L[ℝ] ℝ × ℝ := (dc 2).prod (dc 3)
  set g : ℝ × ℝ → ℝ := sl f 0
  set h : ℝ × ℝ → ℝ := fun x => sl f 1 x - sl f 0 x
  have hh : ContDiff ℝ ∞ h := h1.sub h0
  set u := dc 2 X
  set v := dc 3 X
  have e : (fun Y => f (dc 2 Y) (dc 3 Y) (pE Y)) = fun Y => g (π23 Y) + pE Y * h (π23 Y) := by
    funext Y; rw [hf]; rfl
  have hg' : HasFDerivAt (fun Y => g (π23 Y)) ((fderiv ℝ g (u, v)).comp π23) X :=
    (h0.differentiable (by simp) _).hasFDerivAt.comp X π23.hasFDerivAt
  have hh' : HasFDerivAt (fun Y => h (π23 Y)) ((fderiv ℝ h (u, v)).comp π23) X :=
    (hh.differentiable (by simp) _).hasFDerivAt.comp X π23.hasFDerivAt
  have hd0 : DifferentiableAt ℝ (sl f 0) (u, v) := h0.differentiable (by simp) _
  have hd1 : DifferentiableAt ℝ (sl f 1) (u, v) := h1.differentiable (by simp) _
  have hfd : fderiv ℝ h (u, v) = fderiv ℝ (sl f 1) (u, v) - fderiv ℝ (sl f 0) (u, v) :=
    fderiv_sub hd1 hd0
  have hpu := hf.pu (differentiableAt_sl_u hd0) (differentiableAt_sl_u hd1) (pE X)
  have hpv := hf.pv (differentiableAt_sl_v hd0) (differentiableAt_sl_v hd1) (pE X)
  have hpp : pp f u v (pE X) = f u v 1 - f u v 0 := by
    simp only [pp]
    have : HasDerivAt (fun q => f u v 0 + q * (f u v 1 - f u v 0)) (f u v 1 - f u v 0) (pE X) := by
      simpa using ((hasDerivAt_id (pE X)).mul_const (f u v 1 - f u v 0)).const_add (f u v 0)
    rw [show (fun q => f u v q) = fun q => f u v 0 + q * (f u v 1 - f u v 0) from
      funext fun q => hf u v q]
    exact this.deriv
  rw [e]
  refine (hg'.add ((hasFDerivAt_pE X).mul hh')).congr_fderiv ?_
  rw [hpu, hpv, hpp, pu_eq hd0, pu_eq hd1, pv_eq hd0, pv_eq hd1]
  ext w
  simp only [add_apply, comp_apply, smul_apply, smul_eq_mul, hfd, sub_apply, π23, prod_apply]
  rw [clm_pair (fderiv ℝ g (u, v)), clm_pair (fderiv ℝ (sl f 1) (u, v)),
    clm_pair (fderiv ℝ (sl f 0) (u, v))]
  simp only [g, h, sl]
  ring

/-! ### The forms -/

/-- `a_loc = −3 Zunit^* η_H` at the base point of `X`. -/
def aloc (X : E4) : E4 →L[ℝ] ℝ :=
  (-3 * etaHu (dc 2 X) (dc 3 X)) • dc 2 + (-3 * etaHv (dc 2 X) (dc 3 X)) • dc 3

/-- **`Ω₀` in the frame `Zunit`** (eq:fer-Omega0-local):
`Ω₀ = dx ∧ dy + (1 − 3p) σ du ∧ dv + dp ∧ a_loc`. -/
def Omega0loc : Form2 E4 := fun X =>
  wedge (dc 0) (dc 1) + ((1 - 3 * pE X) * sigmaC (dc 2 X) (dc 3 X)) • wedge (dc 2) (dc 3) +
    wedge (dpE X) (aloc X)

/-- `α₁` as an ambient one-form on `ℝ⁴` (pure base form). -/
def alpha1E (P : Params) : Form1 E4 := fun X =>
  (alpha1 P).cu (dc 2 X) (dc 3 X) (pE X) • dc 2 + (alpha1 P).cv (dc 2 X) (dc 3 X) (pE X) • dc 3

/-- **The first Moser path** `Ω_t = Ω₀ + t dα₁` (`lem:fer-positivity`). -/
def OmegaT (P : Params) (t : ℝ) : Form2 E4 := fun X => Omega0loc X + t • d1 (alpha1E P) X

/-- `κ_t = (1 − t) κ + t κ₁`. -/
def kappaT (P : Params) (t : ℝ) : Coef := fun u v p => (1 - t) * kappa u v p + t * kappa1 P u v p

lemma d1_const (c : E4 →L[ℝ] ℝ) (X : E4) : d1 (fun _ : E4 => c) X = 0 := by
  ext v w; simp [Forms.d1]

/-- `dα₁ = d_C α₁ du ∧ dv + dp ∧ ∂_p α₁`. -/
theorem d1_alpha1E (P : Params) (X : E4) :
    d1 (alpha1E P) X =
      (alpha1 P).dC (dc 2 X) (dc 3 X) (pE X) • wedge (dc 2) (dc 3) +
        wedge (dpE X) (pp (alpha1 P).cu (dc 2 X) (dc 3 X) (pE X) • dc 2 +
          pp (alpha1 P).cv (dc 2 X) (dc 3 X) (pE X) • dc 3) := by
  obtain ⟨ha, hb⟩ := alpha1_affine P
  have hA := hasFDerivAt_lift ha (smooth_alpha1 P 0).1 (smooth_alpha1 P 1).1 X
  have hB := hasFDerivAt_lift hb (smooth_alpha1 P 0).2 (smooth_alpha1 P 1).2 X
  have e : alpha1E P = (fun Y => (alpha1 P).cu (dc 2 Y) (dc 3 Y) (pE Y) • (fun _ => dc 2) Y) +
      (fun Y => (alpha1 P).cv (dc 2 Y) (dc 3 Y) (pE Y) • (fun _ => dc 3) Y) := rfl
  have dA : DifferentiableAt ℝ
      (fun Y => (alpha1 P).cu (dc 2 Y) (dc 3 Y) (pE Y) • (fun _ => dc 2) Y) X :=
    hA.differentiableAt.smul_const _
  have dB : DifferentiableAt ℝ
      (fun Y => (alpha1 P).cv (dc 2 Y) (dc 3 Y) (pE Y) • (fun _ => dc 3) Y) X :=
    hB.differentiableAt.smul_const _
  rw [e, Forms.d1_add_apply dA dB, Forms.d1_mul_apply hA.differentiableAt
    (differentiableAt_const _), Forms.d1_mul_apply hB.differentiableAt (differentiableAt_const _),
    d1_const, d1_const]
  simp only [d0, hA.fderiv, hB.fderiv]
  ext v w
  simp only [add_apply, smul_apply, wedge_apply, smul_eq_mul, BForm.dC, zero_apply, mul_zero,
    add_zero]
  ring

/-- **`Ω_t` is a split form** (`lem:fer-positivity`): in the frame `Zunit`,
`Ω_t = ω_V + κ_t + dp ∧ γ_t`, `γ_t = a_loc + t ∂_p α₁`. -/
theorem OmegaT_split (P : Params) (t : ℝ) (X : E4) :
    OmegaT P t X = splitForm (2 * π * dc 0 X) (2 * π * dc 1 X)
      (-3 * etaHu (dc 2 X) (dc 3 X) + t * pp (alpha1 P).cu (dc 2 X) (dc 3 X) (pE X))
      (-3 * etaHv (dc 2 X) (dc 3 X) + t * pp (alpha1 P).cv (dc 2 X) (dc 3 X) (pE X))
      (kappaT P t (dc 2 X) (dc 3 X) (pE X)) := by
  have hc := alpha1_curvature P (dc 2 X) (dc 3 X) (pE X)
  simp only [OmegaT, d1_alpha1E, hc]
  ext v w
  simp only [Omega0loc, aloc, dpE, splitForm, kappaT, kappa, add_apply, smul_apply, wedge_apply,
    smul_eq_mul]
  ring

end SymplecticPacking.Bundle
