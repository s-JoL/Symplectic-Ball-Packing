import SymplecticPacking.Handle.Twist
import SymplecticPacking.Branch2.Model.Cubic.Bundle.OmegaT

/-!
# The twist of the handle and the suspension identity

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`eq:shd4-twist`, `lem:shd4-suspension`): the local model of the handle over the
annulus and the suspension identity, in the local coordinates `(x, y, s, t)` of
`Handle/Twist.lean` (`w = x + iy = wL X`, `(s, t) = (u, v)`, `p = π|w|²`).

* `qq`, `QQ`, `qqInv`: the comparison isotopy `q_τ = qhatP P τ`, its generator and its inverse
  as maps of `E4`, with their smoothness and collar properties.
* `Dlam P λ (s, t, w) = (s, t, q_{λ f(s)}(w))` (`eq:shd4-twist`), with `f = stepA`;
  `Qs P λ s = λ f'(s) Q_{λ f(s)}` is its `s`-generator and
  `Glam P λ s w = f(s) H*(p(q_λ⁻¹ w))`.
* `suspension` (`lem:shd4-suspension`):
  `𝒟_λ^* ω_V = ω_V + d[(Q^λ_s ∘ q_{λ f(s)}) ds]`.
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus contDiff_stepA contDiff_deriv_stepA)
open SymplecticPacking.Qhat (hamVF2 omega2 omega2_map)
open SymplecticPacking.Qhat.Cubic (qhatP qhatInvP QhamP qhatP_spec Psupp)
open scoped ContDiff Real

/-! ### Coordinates -/

/-! ### Generic calculus helpers -/

/-! ### The isotopy as a function of two variables -/

variable (P : Branch2.VCubic)

/-- `q(τ, w) = q_τ(w)`. -/
def qq : ℝ × ℂ → ℂ := fun z => qhatP P z.1 z.2

/-- `Q(τ, y) = Q_τ(y)`. -/
def QQ : ℝ × ℂ → ℝ := fun z => QhamP P z.1 z.2

/-- `q⁻¹(τ, w) = q_τ⁻¹(w)`. -/
def qqInv : ℝ × ℂ → ℂ := fun z => qhatInvP P z.1 z.2

lemma contDiff_qq : ContDiff ℝ ∞ (qq P) := (qhatP_spec P).1
lemma contDiff_QQ : ContDiff ℝ ∞ (QQ P) := by
  obtain ⟨-, -, h, -⟩ := qhatP_spec P; exact h
lemma contDiff_qqInv : ContDiff ℝ ∞ (qqInv P) := by
  obtain ⟨-, h, -⟩ := qhatP_spec P; exact h

lemma contDiff_qhatInvP (τ : ℝ) : ContDiff ℝ ∞ (qhatInvP P τ) := by
  have h : ContDiff ℝ ∞ (fun w => qqInv P (τ, w)) :=
    (contDiff_qqInv P).comp (contDiff_const.prodMk contDiff_id)
  exact h

lemma qhatInvP_qhatP (τ : ℝ) (z : ℂ) : qhatInvP P τ (qhatP P τ z) = z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := qhatP_spec P; exact h τ z

lemma qhatP_qhatInvP (τ : ℝ) (y : ℂ) : qhatP P τ (qhatInvP P τ y) = y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := qhatP_spec P; exact h τ y

lemma qhatP_zero : qhatP P 0 = id := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -, -⟩ := qhatP_spec P; exact h

lemma qhatP_collar {τ : ℝ} {z : ℂ} (hz : Psupp P < π * ‖z‖ ^ 2) : qhatP P τ z = z := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -, -, -, -, -⟩ := qhatP_spec P; exact h τ z hz

lemma qhatInvP_collar {τ : ℝ} {z : ℂ} (hz : Psupp P < π * ‖z‖ ^ 2) : qhatInvP P τ z = z := by
  conv_lhs => rw [← qhatP_collar P (τ := τ) hz]
  exact qhatInvP_qhatP P τ z

lemma QhamP_collar {τ : ℝ} {y : ℂ} (hy : Psupp P < π * ‖y‖ ^ 2) : QhamP P τ y = 0 := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -, -, -⟩ := qhatP_spec P; exact h τ y hy

lemma det_qhatP (τ : ℝ) (z : ℂ) :
    LinearMap.det (fderiv ℝ (qhatP P τ) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  obtain ⟨-, -, -, h, -, -, -, -, -, -, -, -, -, -⟩ := qhatP_spec P; exact h τ z

lemma omega2_hamVF (τ : ℝ) (z v : ℂ) :
    omega2 (hamVF2 (QhamP P τ) (qhatP P τ z)) v = -fderiv ℝ (QhamP P τ) (qhatP P τ z) v := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -, -, -⟩ := qhatP_spec P; exact h τ z v

lemma hasDerivAt_qhatP (τ : ℝ) (z : ℂ) :
    HasDerivAt (fun s => qhatP P s z) (hamVF2 (QhamP P τ) (qhatP P τ z)) τ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -, -, -, -⟩ := qhatP_spec P; exact h τ z

lemma fderiv_qq_apply (τ : ℝ) (w : ℂ) (a : ℝ) (b : ℂ) :
    fderiv ℝ (qq P) (τ, w) (a, b) =
      a • hamVF2 (QhamP P τ) (qhatP P τ w) + fderiv ℝ (qhatP P τ) w b := by
  rw [fderiv_prod_apply ((contDiff_qq P).differentiable (by simp) _)]
  congr 2
  exact (hasDerivAt_qhatP P τ w).deriv

lemma fderiv_QQ_apply (τ : ℝ) (y : ℂ) (a : ℝ) (b : ℂ) :
    fderiv ℝ (QQ P) (τ, y) (a, b) =
      a * deriv (fun t' => QhamP P t' y) τ + fderiv ℝ (QhamP P τ) y b := by
  rw [fderiv_prod_apply ((contDiff_QQ P).differentiable (by simp) _), smul_eq_mul]; rfl

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

lemma hasFDerivAt_tau (lam : ℝ) (X : E4) :
    HasFDerivAt (fun Y : E4 => lam * stepA (Y 2)) ((lam * deriv stepA (X 2)) • dc 2) X := by
  have h : HasDerivAt stepA (deriv stepA (X 2)) (X 2) :=
    (contDiff_stepA.differentiable (by simp) _).hasDerivAt
  have := (h.comp_hasFDerivAt X (dc 2).hasFDerivAt).const_mul lam
  exact this.congr_fderiv (smul_smul _ _ _)

theorem contDiff_Dlam_joint :
    ContDiff ℝ ∞ (fun z : ℝ × E4 => Dlam P z.1 z.2) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × E4 => z.1 * stepA (z.2 2)) :=
    contDiff_fst.mul (contDiff_stepA.comp ((dc 2).contDiff.comp contDiff_snd))
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × E4 => qq P (z.1 * stepA (z.2 2), wL z.2)) :=
    (contDiff_qq P).comp (h1.prodMk (wL.contDiff.comp contDiff_snd))
  exact mkL.contDiff.comp (h2.prodMk (((dc 2).contDiff.comp contDiff_snd).prodMk
    ((dc 3).contDiff.comp contDiff_snd)))

theorem contDiff_Dlam (lam : ℝ) : ContDiff ℝ ∞ (Dlam P lam) := by
  have h : ContDiff ℝ ∞ (fun X => Dlam P (lam, X).1 (lam, X).2) :=
    (contDiff_Dlam_joint P).comp (contDiff_const.prodMk contDiff_id)
  exact h

/-- **The derivative of the twist**: `D𝒟_λ (a, v₂, v₃) = (A a + λ f'(s) v₂ X_Q, v₂, v₃)` with
`A = Dq_τ(w)`, `τ = λ f(s)`, `X_Q = X_{Q_τ}(q_τ w)`. -/
theorem fderiv_Dlam_apply (lam : ℝ) (X v : E4) :
    fderiv ℝ (Dlam P lam) X v =
      mk ((lam * deriv stepA (X 2) * v 2) • hamVF2 (QhamP P (lam * stepA (X 2)))
          (qhatP P (lam * stepA (X 2)) (wL X)) +
        fderiv ℝ (qhatP P (lam * stepA (X 2))) (wL X) (wL v)) (v 2) (v 3) := by
  have hq : HasFDerivAt (qq P) (fderiv ℝ (qq P) (lam * stepA (X 2), wL X))
      (lam * stepA (X 2), wL X) :=
    ((contDiff_qq P).differentiable (by simp) _).hasFDerivAt
  have hin := (hasFDerivAt_tau lam X).prodMk wL.hasFDerivAt
  have hc := hq.comp X hin
  have hall : HasFDerivAt (Dlam P lam) _ X :=
    mkL.hasFDerivAt.comp X (hc.prodMk ((dc 2).hasFDerivAt.prodMk (dc 3).hasFDerivAt))
  rw [hall.fderiv]
  simp only [comp_apply, prod_apply, smul_apply, smul_eq_mul]
  rw [fderiv_qq_apply]
  simp [mk]

lemma dc2_fderiv_Dlam (lam : ℝ) (X v : E4) : fderiv ℝ (Dlam P lam) X v 2 = v 2 := by
  rw [fderiv_Dlam_apply]; simp

lemma dc3_fderiv_Dlam (lam : ℝ) (X v : E4) : fderiv ℝ (Dlam P lam) X v 3 = v 3 := by
  rw [fderiv_Dlam_apply]; simp

/-- `ω₂(Av, Aw) = ω₂(v, w)` for `A = Dq_τ`. -/
lemma omega2_dq (τ : ℝ) (z a b : ℂ) :
    omega2 (fderiv ℝ (qhatP P τ) z a) (fderiv ℝ (qhatP P τ) z b) = omega2 a b := by
  rw [omega2_map, det_qhatP, one_mul]

/-- The derivative of the twist is injective (hence bijective). -/
theorem fderiv_Dlam_injective (lam : ℝ) (X : E4) :
    Function.Injective (fderiv ℝ (Dlam P lam) X) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ (Dlam P lam) X)).mpr fun v hv => ?_
  have h2 : v 2 = 0 := by rw [← dc2_fderiv_Dlam P lam X v, hv]; rfl
  have h3 : v 3 = 0 := by rw [← dc3_fderiv_Dlam P lam X v, hv]; rfl
  have hw : fderiv ℝ (qhatP P (lam * stepA (X 2))) (wL X) (wL v) = 0 := by
    have := congrArg wL hv
    rw [fderiv_Dlam_apply, wL_mk, h2, mul_zero, zero_smul, zero_add, map_zero] at this
    exact this
  have hu : IsUnit (fderiv ℝ (qhatP P (lam * stepA (X 2))) (wL X) : ℂ →ₗ[ℝ] ℂ) := by
    rw [LinearMap.isUnit_iff_isUnit_det, det_qhatP]; exact isUnit_one
  have hw0 : wL v = 0 :=
    (LinearMap.isUnit_iff_ker_eq_bot _ |>.mp hu ▸ LinearMap.mem_ker.mpr hw : wL v ∈ (⊥ : Submodule ℝ ℂ))
  rw [← mk_wL v, hw0, h2, h3]
  simp [mk_eq]

/-! ### The suspension identity (`lem:shd4-suspension`) -/

/-- `Φ = Q^λ_s ∘ q_{λ f(s)}` as a function on `E4`. -/
def PhiS (lam : ℝ) (X : E4) : ℝ := Qs P lam (X 2) (qhatP P (lam * stepA (X 2)) (wL X))

lemma PhiS_eq (lam : ℝ) : PhiS P lam = fun X => (lam * deriv stepA (X 2)) *
    QQ P (lam * stepA (X 2), qq P (lam * stepA (X 2), wL X)) := by
  funext X; simp only [PhiS, Qs, QQ, qq]

theorem contDiff_PhiS_joint : ContDiff ℝ ∞ (fun z : ℝ × E4 => PhiS P z.1 z.2) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × E4 => z.1 * stepA (z.2 2)) :=
    contDiff_fst.mul (contDiff_stepA.comp ((dc 2).contDiff.comp contDiff_snd))
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × E4 => qq P (z.1 * stepA (z.2 2), wL z.2)) :=
    (contDiff_qq P).comp (h1.prodMk (wL.contDiff.comp contDiff_snd))
  have h3 : ContDiff ℝ ∞ (fun z : ℝ × E4 => z.1 * deriv stepA (z.2 2)) :=
    contDiff_fst.mul (contDiff_deriv_stepA.comp ((dc 2).contDiff.comp contDiff_snd))
  have e : (fun z : ℝ × E4 => PhiS P z.1 z.2) = fun z => (z.1 * deriv stepA (z.2 2)) *
      QQ P (z.1 * stepA (z.2 2), qq P (z.1 * stepA (z.2 2), wL z.2)) :=
    funext fun z => congrFun (PhiS_eq P z.1) z.2
  rw [e]
  exact h3.mul ((contDiff_QQ P).comp (h1.prodMk h2))

theorem contDiff_PhiS (lam : ℝ) : ContDiff ℝ ∞ (PhiS P lam) := by
  have h : ContDiff ℝ ∞ (fun X => PhiS P (lam, X).1 (lam, X).2) :=
    (contDiff_PhiS_joint P).comp (contDiff_const.prodMk contDiff_id)
  exact h

/-- The derivative of `Φ`: its fibre part is `λ f'(s) dQ_τ(q_τ w) ∘ Dq_τ(w)`. -/
theorem fderiv_PhiS_apply (lam : ℝ) (X : E4) : ∃ C : ℝ, ∀ v : E4,
    fderiv ℝ (PhiS P lam) X v =
      lam * deriv stepA (X 2) * fderiv ℝ (QhamP P (lam * stepA (X 2)))
        (qhatP P (lam * stepA (X 2)) (wL X))
        (fderiv ℝ (qhatP P (lam * stepA (X 2))) (wL X) (wL v)) + v 2 * C := by
  set τ := lam * stepA (X 2)
  set w := wL X
  set y := qhatP P τ w
  set V := hamVF2 (QhamP P τ) y
  set c := lam * deriv stepA (X 2)
  have hf2 : HasDerivAt (deriv stepA) (deriv (deriv stepA) (X 2)) (X 2) :=
    (contDiff_deriv_stepA.differentiable (by simp) _).hasDerivAt
  have hc : HasFDerivAt (fun Y : E4 => lam * deriv stepA (Y 2))
      ((lam * deriv (deriv stepA) (X 2)) • dc 2) X := by
    have := (hf2.comp_hasFDerivAt X (dc 2).hasFDerivAt).const_mul lam
    exact this.congr_fderiv (smul_smul _ _ _)
  have hq : HasFDerivAt (qq P) (fderiv ℝ (qq P) (τ, w)) (τ, w) :=
    ((contDiff_qq P).differentiable (by simp) _).hasFDerivAt
  have hQ : HasFDerivAt (QQ P) (fderiv ℝ (QQ P) (τ, y)) (τ, y) :=
    ((contDiff_QQ P).differentiable (by simp) _).hasFDerivAt
  have hin := (hasFDerivAt_tau lam X).prodMk wL.hasFDerivAt
  have hqc := hq.comp X hin
  have hQc := hQ.comp X ((hasFDerivAt_tau lam X).prodMk hqc)
  have hall : HasFDerivAt (PhiS P lam) _ X := hc.mul hQc
  refine ⟨lam * deriv (deriv stepA) (X 2) * QQ P (τ, y) +
    c * (c * deriv (fun t' => QhamP P t' y) τ + c * fderiv ℝ (QhamP P τ) y V), fun v => ?_⟩
  rw [hall.fderiv]
  simp only [add_apply, smul_apply, comp_apply, prod_apply, smul_eq_mul]
  rw [fderiv_qq_apply, fderiv_QQ_apply]
  simp only [map_add, map_smul, smul_eq_mul, dc_apply]
  simp only [QQ] at *
  ring

/-- **Suspension identity** (`lem:shd4-suspension`):
`𝒟_λ^* ω_V = ω_V + d[(Q^λ_s ∘ q_{λ f(s)}) ds]`. -/
theorem suspension (lam : ℝ) (X : E4) :
    pull2 (Dlam P lam) omegaV X = omegaV X + d1 (fun Y => PhiS P lam Y • dc 2) X := by
  obtain ⟨C, hC⟩ := fderiv_PhiS_apply P lam X
  rw [d1_smul_const_form ((contDiff_PhiS P lam).differentiable (by simp) X)]
  ext v w
  simp only [Forms.pull2_apply, add_apply, wedge_apply, omegaV_apply, fderiv_Dlam_apply, wL_mk,
    hC, dc_apply]
  set τ := lam * stepA (X 2)
  set A := fderiv ℝ (qhatP P τ) (wL X)
  set V := hamVF2 (QhamP P τ) (qhatP P τ (wL X))
  set c := lam * deriv stepA (X 2)
  have e1 : omega2 ((c * v 2) • V + A (wL v)) ((c * w 2) • V + A (wL w)) =
      omega2 (A (wL v)) (A (wL w)) + (c * v 2) * omega2 V (A (wL w)) -
        (c * w 2) * omega2 V (A (wL v)) := by
    rw [Qhat.omega2_add_left, Qhat.omega2_add_right, Qhat.omega2_add_right, Qhat.omega2_smul_left,
      Qhat.omega2_smul_left, Qhat.omega2_smul_right, Qhat.omega2_smul_right, omega2_self,
      Qhat.omega2_skew (A (wL v)) V]
    ring
  rw [e1, omega2_dq, omega2_hamVF, omega2_hamVF]
  norm_num
  ring

end SymplecticPacking.Handle.Cubic
