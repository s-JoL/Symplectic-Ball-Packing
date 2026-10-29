import SymplecticPacking.Bundle.OmegaT
import SymplecticPacking.Branch2.Model.Cubic.Bundle.Alpha1

/-!
# The first Moser path and its positivity

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Bundle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:fer` (`lem:fer-positivity`): the first Moser path
`Ω_t = Ω₀ + t dα₁` in the global frame `Zunit` of the cover, and its positivity.

Coordinates on `E4 = ℝ⁴`: `(x, y, u, v)` = indices `(0, 1, 2, 3)`; `w = x + iy` is the fibre
coordinate in the frame `Zunit(u, v)`, `p = π(x² + y²)` (`pE`).
* `Omega0loc` is the local formula `Ω₀ = ω_V + (1 − 3p)σ + dp ∧ a_loc` (eq:fer-Omega0-local),
  `ω_V = dx ∧ dy`, `a_loc = −3 Zunit^* η_H`.
* `alpha1E` is `α₁` as an ambient one-form (no `dx`, `dy` components), `OmegaT P t = Ω₀ + t dα₁`
  with the ambient exterior derivative `Forms.d1`.
* `OmegaT_split`: `Ω_t = ω_V + κ_t du∧dv + dp ∧ γ_t` with `κ_t = (1−t)κ + tκ₁` and
  `γ_t = a_loc + t ∂_p α₁` — i.e. `Forms.splitForm`.
* `OmegaT_sq`: the Pfaffian of `Ω_t` is `κ_t` (`Ω_t² = 2 ω_V ∧ κ_t`); `kappaT_pos`,
  `OmegaT_nondeg'`: `κ_t > 0` and `Ω_t` is nondegenerate on `{p ≤ h}` for `t ∈ [0, 1]`.
-/

noncomputable section

namespace SymplecticPacking.Bundle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 Form1 Form2 splitForm pf pf_splitForm splitForm_nondeg)
open scoped ContDiff Real

/-! ### The forms -/

/-- `α₁` as an ambient one-form on `ℝ⁴` (pure base form). -/
def alpha1E (P : Branch2.VCubic) : Form1 E4 := fun X =>
  (alpha1 P).cu (dc 2 X) (dc 3 X) (pE X) • dc 2 + (alpha1 P).cv (dc 2 X) (dc 3 X) (pE X) • dc 3

/-- **The first Moser path** `Ω_t = Ω₀ + t dα₁` (`lem:fer-positivity`). -/
def OmegaT (P : Branch2.VCubic) (t : ℝ) : Form2 E4 := fun X => Omega0loc X + t • d1 (alpha1E P) X

/-- `κ_t = (1 − t) κ + t κ₁`. -/
def kappaT (P : Branch2.VCubic) (t : ℝ) : Coef := fun u v p => (1 - t) * kappa u v p + t * kappa1 P u v p

/-- `dα₁ = d_C α₁ du ∧ dv + dp ∧ ∂_p α₁`. -/
theorem d1_alpha1E (P : Branch2.VCubic) (X : E4) :
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
theorem OmegaT_split (P : Branch2.VCubic) (t : ℝ) (X : E4) :
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

/-- **`Ω_t² = 2 ω_V ∧ κ_t`**: the Pfaffian of `Ω_t` is `κ_t` (`lem:fer-positivity`,
eq:fer-positivity). -/
theorem OmegaT_sq (P : Branch2.VCubic) (t : ℝ) (X : E4) :
    pf (OmegaT P t X) = kappaT P t (dc 2 X) (dc 3 X) (pE X) := by
  rw [OmegaT_split, pf_splitForm]

lemma kappaT_pos (P : Branch2.VCubic) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u v p : ℝ}
    (hp : 0 < 1 - 3 * p) (hH : 0 ≤ P.Hstar p) : 0 < kappaT P t u v p := by
  have h1 : 0 < kappa u v p := mul_pos hp (sigmaC_pos u v)
  have h2 : 0 < kappa1 P u v p :=
    lt_of_lt_of_le (kappa_pos P).2.2 ((kappa_pos P).2.1 u v p hH)
  unfold kappaT
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simpa using h1
  · nlinarith [ht.2]

/-- **Nondegeneracy of `Ω_t`** wherever `1 − 3p > 0` and `H*(p) ≥ 0`, `t ∈ [0, 1]`. -/
theorem OmegaT_nondeg' (P : Branch2.VCubic) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {X : E4}
    (hp : 0 < 1 - 3 * pE X) (hH : 0 ≤ P.Hstar (pE X)) :
    ∀ v, (∀ w, OmegaT P t X v w = 0) → v = 0 := by
  rw [OmegaT_split]
  exact splitForm_nondeg (kappaT_pos P ht hp hH).ne'

end SymplecticPacking.Bundle.Cubic
