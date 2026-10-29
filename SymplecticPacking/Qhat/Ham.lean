import SymplecticPacking.Qhat.Normal
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy

/-!
# The Hamiltonian of the comparison isotopy

`sec:pln-ham`: the Hamiltonian of `q̂_t` (`cons:pln-hamiltonian`, `prop:pln-hamiltonian`).

`a^q_t(z)[w] = ω₂(∂_t q̂_t(z), Dq̂_t(z) w)` is closed (differentiate `q̂_t^*ω₂ = ω₂` in `t`, use
symmetry of second derivatives); the radial (Poincaré) primitive
`h^q_t(z) = ∫₀¹ a^q_t(rz)[z] dr` satisfies `dh^q_t = a^q_t` (Mathlib's Poincaré lemma for
segments). With the gauge point `z_bd` in the collar,
`H^q_t = [h^q_t - h^q_t(z_bd)] ∘ q̂_t⁻¹` satisfies `ι_{X_t}ω₂ = +dH^q_t`, and `Q_t = -H^q_t`
generates `q̂_t` with the convention `ι_{X_Q}ω₂ = -dQ` of `sec:shd-four`.

Convention: `ω₂(a, b) = a.re b.im - a.im b.re` (`= dx∧dy`), and the Hamiltonian field of `Q`
with `ι_{X_Q}ω₂ = -dQ` is `X_Q = -∂_yQ + i ∂_xQ` (`hamVF2`).
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Metric ContinuousLinearMap
open scoped ContDiff Real

/-! ### `ω₂` -/

/-- `ω₂ = dx∧dy`: `ω₂(a, b) = a.re b.im - a.im b.re`. -/
def omega2 (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

lemma omega2_add_left (x x' y : ℂ) : omega2 (x + x') y = omega2 x y + omega2 x' y := by
  simp only [omega2, Complex.add_re, Complex.add_im]; ring
lemma omega2_smul_left (c : ℝ) (x y : ℂ) : omega2 (c • x) y = c * omega2 x y := by
  simp only [omega2, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]; ring
lemma omega2_add_right (x y y' : ℂ) : omega2 x (y + y') = omega2 x y + omega2 x y' := by
  simp only [omega2, Complex.add_re, Complex.add_im]; ring
lemma omega2_smul_right (c : ℝ) (x y : ℂ) : omega2 x (c • y) = c * omega2 x y := by
  simp only [omega2, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]; ring
lemma omega2_skew (x y : ℂ) : omega2 x y = -omega2 y x := by simp only [omega2]; ring

/-- `ω₂` as a linear map into linear forms. -/
def omega2ₗ : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ omega2 omega2_add_left omega2_smul_left omega2_add_right omega2_smul_right

/-- `ω₂` as a continuous bilinear map. -/
def omega2L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (ℂ →L[ℝ] ℝ)).toLinearMap.comp omega2ₗ)

@[simp] lemma omega2L_apply (x y : ℂ) : omega2L x y = omega2 x y := rfl

/-- In dimension two, `ω₂(Lv, Lw) = det L · ω₂(v, w)`. -/
theorem omega2_map (L : ℂ →L[ℝ] ℂ) (v w : ℂ) :
    omega2 (L v) (L w) = LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) * omega2 v w := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [Inner.det_eq_re_im]
  conv_lhs => rw [hv, hw]
  simp only [map_add, map_smul, omega2_add_left, omega2_add_right, omega2_smul_left,
    omega2_smul_right]
  simp only [omega2, ContinuousLinearMap.coe_coe]
  ring

/-- The Hamiltonian vector field of `Q` for `ι_{X_Q}ω₂ = -dQ`: `X_Q = -∂_yQ + i ∂_xQ`. -/
def hamVF2 (Q : ℂ → ℝ) (y : ℂ) : ℂ := ⟨-fderiv ℝ Q y Complex.I, fderiv ℝ Q y 1⟩

/-- `ω₂(V, ·) = -dQ` determines `V = X_Q`. -/
theorem eq_hamVF2 {Q : ℂ → ℝ} {y V : ℂ} (h : ∀ v, omega2 V v = -fderiv ℝ Q y v) :
    V = hamVF2 Q y := by
  have h1 := h 1
  have hI := h Complex.I
  simp only [omega2, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h1 hI
  apply Complex.ext
  · simp only [hamVF2]; linarith
  · simp only [hamVF2]; linarith

/-! ### Definitions (`cons:pln-hamiltonian`) -/

/-- The uncurried isotopy `(t, z) ↦ q̂_t(z)`. -/
def uq (D : PathData) (p : ℝ × ℂ) : ℂ := qhat D p.1 p.2

/-- `∂_t q̂_t(z)`. -/
def qvel (D : PathData) (t : ℝ) (z : ℂ) : ℂ := fderiv ℝ (uq D) (t, z) (1, 0)

/-- **`cons:pln-hamiltonian`.** `a^q_t(z)[w] = ω₂(∂_t q̂_t(z), Dq̂_t(z) w)` (`aq_apply`). -/
def aq (D : PathData) (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (omega2L (fderiv ℝ (uq D) (t, z) (1, 0))).comp ((fderiv ℝ (uq D) (t, z)).comp (inr ℝ ℝ ℂ))

/-- **`cons:pln-hamiltonian`.** The radial primitive `h^q_t(z) = ∫₀¹ a^q_t(rz)[z] dr`. -/
def hq (D : PathData) (t : ℝ) (z : ℂ) : ℝ := ∫ r in (0 : ℝ)..1, aq D t (r • z) z

/-- `p_bd = (h + P_supp)/2`. -/
def pbd (D : PathData) : ℝ := (D.h + D.Psupp) / 2

/-- **`cons:pln-hamiltonian`.** The gauge point `z_bd = (√(p_bd/π), 0)`. -/
def zbd (D : PathData) : ℂ := (Real.sqrt (pbd D / π) : ℂ)

open Classical in
/-- `q̂_t⁻¹`: the unique preimage (definite description), `y` if there is none. -/
def qhatInv (D : PathData) (t : ℝ) (y : ℂ) : ℂ :=
  if hu : ∃! z, qhat D t z = y then Explicit.the hu else y

/-- **`cons:pln-hamiltonian`.** `H^q_t = [h^q_t - h^q_t(z_bd)] ∘ q̂_t⁻¹`. -/
def Hq (D : PathData) (t : ℝ) (y : ℂ) : ℝ := hq D t (qhatInv D t y) - hq D t (zbd D)

/-- **`cons:pln-hamiltonian`.** `Q_t = -H^q_t`. -/
def Qham (D : PathData) (t : ℝ) (y : ℂ) : ℝ := -Hq D t y

section ham
variable {D : PathData} (hD : OrdinaryPath D)
include hD

theorem uq_smooth : ContDiff ℝ ∞ (uq D) := qhat_smooth hD

theorem uq_differentiableAt (p : ℝ × ℂ) : DifferentiableAt ℝ (uq D) p :=
  (uq_smooth hD).differentiable (by simp) p

theorem qhat_slice_hasFDerivAt (t : ℝ) (z : ℂ) :
    HasFDerivAt (qhat D t) ((fderiv ℝ (uq D) (t, z)).comp (inr ℝ ℝ ℂ)) z :=
  (uq_differentiableAt hD (t, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)

theorem fderiv_qhat_eq (t : ℝ) (z : ℂ) :
    fderiv ℝ (qhat D t) z = (fderiv ℝ (uq D) (t, z)).comp (inr ℝ ℝ ℂ) :=
  (qhat_slice_hasFDerivAt hD t z).fderiv

/-- `∂_t q̂_t(z)` is the time derivative. -/
theorem qhat_hasDerivAt_time (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s => qhat D s z) (qvel D t z) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, z) : ℝ × ℂ)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  exact (uq_differentiableAt hD (t, z)).hasFDerivAt.comp_hasDerivAt t h1

theorem aq_apply (t : ℝ) (z w : ℂ) :
    aq D t z w = omega2 (qvel D t z) (fderiv ℝ (qhat D t) z w) := by
  rw [fderiv_qhat_eq hD]; rfl

/-! ### Closedness (`aq_closed`) -/

/-- Derivative of `a^q_t` in `z`. -/
def daq (D : PathData) (t : ℝ) (y : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  let Dq := fderiv ℝ (uq D) (t, y)
  let S := fderiv ℝ (fderiv ℝ (uq D)) (t, y)
  { toFun := fun u =>
      (omega2L (S (0, u) (1, 0))).comp (Dq.comp (inr ℝ ℝ ℂ)) +
        (omega2L (Dq (1, 0))).comp ((S (0, u)).comp (inr ℝ ℝ ℂ))
    map_add' := by
      intro u u'; ext v
      have e : ((0 : ℝ), u + u') = ((0 : ℝ), u) + ((0 : ℝ), u') := by simp
      simp only [e, map_add, add_apply, coe_comp, Function.comp_apply, omega2L_apply,
        omega2_add_left, omega2_add_right]
      ring
    map_smul' := by
      intro c u; ext v
      have e : ((0 : ℝ), c • u) = c • ((0 : ℝ), u) := by simp
      simp only [e, map_smul, smul_apply, coe_comp, Function.comp_apply, omega2L_apply,
        omega2_smul_left, omega2_smul_right, RingHom.id_apply, add_apply, smul_eq_mul]
      ring
    cont := by
      apply Continuous.add
      · exact (omega2L.continuous.comp ((apply ℝ ℂ ((1 : ℝ), (0 : ℂ))).continuous.comp
          (S.continuous.comp (continuous_const.prodMk continuous_id)))).clm_comp continuous_const
      · exact continuous_const.clm_comp
          ((S.continuous.comp (continuous_const.prodMk continuous_id)).clm_comp
            continuous_const) }

omit hD in
theorem fderiv_uq_differentiableAt' (h : ContDiff ℝ ∞ (uq D)) (p : ℝ × ℂ) :
    DifferentiableAt ℝ (fderiv ℝ (uq D)) p :=
  ((h.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) p

theorem hasFDerivAt_aq (t : ℝ) (y : ℂ) : HasFDerivAt (aq D t) (daq D t y) y := by
  set Dq := fderiv ℝ (uq D)
  have hD' : HasFDerivAt (fun z => Dq (t, z)) ((fderiv ℝ Dq (t, y)).comp (inr ℝ ℝ ℂ)) y :=
    (fderiv_uq_differentiableAt' (uq_smooth hD) (t, y)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right t y)
  have h1 : HasFDerivAt (fun z => omega2L (Dq (t, z) (1, 0)))
      (omega2L.comp ((apply ℝ ℂ ((1 : ℝ), (0 : ℂ))).comp
        ((fderiv ℝ Dq (t, y)).comp (inr ℝ ℝ ℂ)))) y :=
    omega2L.hasFDerivAt.comp y ((apply ℝ ℂ ((1 : ℝ), (0 : ℂ))).hasFDerivAt.comp y hD')
  have h2 : HasFDerivAt (fun z => (Dq (t, z)).comp (inr ℝ ℝ ℂ))
      ((compL ℝ ℂ (ℝ × ℂ) ℂ).flip (inr ℝ ℝ ℂ) |>.comp
        ((fderiv ℝ Dq (t, y)).comp (inr ℝ ℝ ℂ))) y :=
    ((compL ℝ ℂ (ℝ × ℂ) ℂ).flip (inr ℝ ℝ ℂ)).hasFDerivAt.comp y hD'
  have h3 := h1.clm_comp h2
  refine h3.congr_fderiv ?_
  ext u v
  simp only [daq, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply, coe_comp,
    Function.comp_apply, inr_apply, omega2L_apply, Dq, compL_apply, flip_apply, apply_apply]
  ring

/-- **`prop:pln-hamiltonian`, closedness.** `d a^q_t` is symmetric. -/
theorem aq_closed (t : ℝ) (y u v : ℂ) : daq D t y u v = daq D t y v u := by
  set Dq := fderiv ℝ (uq D) (t, y)
  set S := fderiv ℝ (fderiv ℝ (uq D)) (t, y)
  have hsym : ∀ a b, S a b = S b a := fun a b =>
    (uq_smooth hD).contDiffAt.isSymmSndFDerivAt (by simp) a b
  have hconst : ∀ s, omega2 (fderiv ℝ (uq D) (s, y) (0, u)) (fderiv ℝ (uq D) (s, y) (0, v)) =
      omega2 u v := by
    intro s
    have h := omega2_map (fderiv ℝ (qhat D s) y) u v
    rw [qhat_symplectic hD, one_mul, fderiv_qhat_eq hD] at h
    exact h
  have hcurve : HasDerivAt (fun s => fderiv ℝ (uq D) (s, y)) (S (1, 0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × ℂ)) ((1 : ℝ), (0 : ℂ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (fderiv_uq_differentiableAt' (uq_smooth hD) (t, y)).hasFDerivAt.comp_hasDerivAt t h1
  have hderiv : HasDerivAt
      (fun s => omega2L (fderiv ℝ (uq D) (s, y) (0, u)) (fderiv ℝ (uq D) (s, y) (0, v)))
      (omega2L (S (1, 0) (0, u)) (Dq (0, v)) + omega2L (Dq (0, u)) (S (1, 0) (0, v))) t := by
    have hu := hcurve.clm_apply (hasDerivAt_const t ((0 : ℝ), u))
    have hv := hcurve.clm_apply (hasDerivAt_const t ((0 : ℝ), v))
    simp only [zero_apply, map_zero, add_zero] at hu hv
    have hw := (omega2L.hasFDerivAt.comp_hasDerivAt t hu).clm_apply hv
    simpa [add_comm] using hw
  have hzero : omega2 (S (1, 0) (0, u)) (Dq (0, v)) + omega2 (Dq (0, u)) (S (1, 0) (0, v)) = 0 := by
    have h0 : HasDerivAt
        (fun s => omega2L (fderiv ℝ (uq D) (s, y) (0, u)) (fderiv ℝ (uq D) (s, y) (0, v))) 0 t := by
      have : (fun s => omega2L (fderiv ℝ (uq D) (s, y) (0, u)) (fderiv ℝ (uq D) (s, y) (0, v)))
          = fun _ => omega2 u v := funext fun s => hconst s
      rw [this]; exact hasDerivAt_const t _
    simpa using hderiv.unique h0
  simp only [daq, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply, coe_comp,
    Function.comp_apply, inr_apply, omega2L_apply]
  rw [hsym (0, u) (1, 0), hsym (0, v) (1, 0), hsym (0, u) (0, v)]
  rw [omega2_skew (Dq (0, u)) (S (1, 0) (0, v))] at hzero
  linarith

/-! ### The primitive (`hq_deriv`) -/

/-- **`prop:pln-hamiltonian`.** `d h^q_t = a^q_t` (radial Poincaré primitive). -/
theorem hq_deriv (t : ℝ) (b : ℂ) : HasFDerivAt (hq D t) (aq D t b) b := by
  have hP := (convex_univ (𝕜 := ℝ) (E := ℂ)).hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (fun x _ => (hasFDerivAt_aq hD t x).hasFDerivWithinAt)
    (fun a _ x _ y _ => aq_closed hD t a x y) (mem_univ 0) (mem_univ b)
  have hP' := hP.hasFDerivAt (univ_mem)
  apply hP'.congr_of_eventuallyEq
  filter_upwards with c
  rw [curveIntegral_segment]
  unfold hq
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [sub_zero]
  rw [show (AffineMap.lineMap (0 : ℂ) c) r = r • c by simp [AffineMap.lineMap_apply]]

theorem aq_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => aq D p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ (uq D)) := (uq_smooth hD).fderiv_right (m := ∞) (by simp)
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => fderiv ℝ (uq D) p) := hd
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℂ => omega2L (fderiv ℝ (uq D) p (1, 0))) :=
    omega2L.contDiff.comp (h1.clm_apply contDiff_const)
  have hB : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (fderiv ℝ (uq D) p).comp (inr ℝ ℝ ℂ)) :=
    h1.clm_comp contDiff_const
  exact hA.clm_comp hB

/-- `(t, z) ↦ h^q_t(z)` is jointly `C^∞`. -/
theorem hq_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => hq D p.1 p.2) := by
  have hf : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℂ) => aq D q.2.1 (q.1 • q.2.2) q.2.2) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℂ) => aq D q.2.1 (q.1 • q.2.2)) :=
      (aq_smooth hD).comp (contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd))
    exact h1.clm_apply contDiff_snd.snd
  exact OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral hf

/-! ### The inverse `q̂_t⁻¹` (`thm:pln-isotopy` (d)) -/

theorem qhatInv_eq {t : ℝ} {z y : ℂ} (h : qhat D t z = y) : qhatInv D t y = z := by
  have hu : ∃! w, qhat D t w = y := ⟨z, h, fun w hw => (qhat_bijective hD t).1 (hw.trans h.symm)⟩
  unfold qhatInv
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact Explicit.the_eq hu h

theorem qhatInv_qhat (t : ℝ) (z : ℂ) : qhatInv D t (qhat D t z) = z := qhatInv_eq hD rfl

theorem qhat_qhatInv (t : ℝ) (y : ℂ) : qhat D t (qhatInv D t y) = y := by
  obtain ⟨z, rfl⟩ := (qhat_bijective hD t).2 y
  rw [qhatInv_qhat hD]

/-- **`thm:pln-isotopy` (d).** `(t, y) ↦ q̂_t⁻¹(y)` is jointly `C^∞`. -/
theorem qhatInv_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhatInv D p.1 p.2) := by
  have h := Inner.contDiffOn_param_inverse (G := qhat D) (inv := qhatInv D) (U := univ)
    isOpen_univ (qhat_smooth hD).contDiffOn (fun s _ => (qhat_bijective hD s).1)
    (fun s _ z => Inner.injective_of_det_ne_zero _ (by rw [qhat_symplectic hD]; exact one_ne_zero))
    (fun s _ y => qhat_qhatInv hD s y)
  rw [univ_prod_univ] at h
  exact contDiffOn_univ.mp h

theorem qhatInv_collar {t : ℝ} {y : ℂ} (hy : D.Psupp < π * ‖y‖ ^ 2) : qhatInv D t y = y :=
  qhatInv_eq hD (qhat_collar hD hy)

/-! ### Smoothness and support of `Q_t` -/

/-- **`prop:pln-hamiltonian`.** `Q` is jointly `C^∞`. -/
theorem Qham_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Qham D p.1 p.2) := by
  set F : ℝ × ℂ → ℝ := fun p => hq D p.1 p.2
  set g1 : ℝ × ℂ → ℝ × ℂ := fun p => (p.1, qhatInv D p.1 p.2)
  set g2 : ℝ × ℂ → ℝ × ℂ := fun p => (p.1, zbd D)
  have hF : ContDiff ℝ ∞ F := hq_smooth hD
  have h1 : ContDiff ℝ ∞ (F ∘ g1) := hF.comp (contDiff_fst.prodMk (qhatInv_smooth hD))
  have h2 : ContDiff ℝ ∞ (F ∘ g2) := hF.comp (contDiff_fst.prodMk contDiff_const)
  have he : (fun p : ℝ × ℂ => Qham D p.1 p.2) = fun p => -((F ∘ g1) p - (F ∘ g2) p) := by
    funext p; rfl
  rw [he]
  exact (h1.sub h2).neg

theorem qvel_collar {t : ℝ} {z : ℂ} (hz : D.Psupp < π * ‖z‖ ^ 2) : qvel D t z = 0 := by
  have h := qhat_hasDerivAt_time hD t z
  have hc : (fun s => qhat D s z) = fun _ => z := funext fun s => qhat_collar hD hz
  rw [hc] at h
  exact h.unique (hasDerivAt_const t z)

theorem qvel_time {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (z : ℂ) : qvel D t z = 0 := by
  have hd := qhat_hasDerivAt_time hD t z
  rcases ht with ht | ht
  · have hc : HasDerivWithinAt (fun s => qhat D s z) 0 (Iic t) t :=
      (hasDerivWithinAt_const t (Iic t) z).congr
        (fun s hs => by rw [qhat_of_nonpos hD (hs.trans ht)]; rfl)
        (by rw [qhat_of_nonpos hD ht]; rfl)
    exact (uniqueDiffWithinAt_Iic t).eq_deriv _ hd.hasDerivWithinAt hc
  · have hc : HasDerivWithinAt (fun s => qhat D s z) 0 (Ici t) t :=
      (hasDerivWithinAt_const t (Ici t) (qhat D 1 z)).congr
        (fun s hs => by rw [qhat_of_one_le hD (ht.trans hs)])
        (by rw [qhat_of_one_le hD ht])
    exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivWithinAt hc

theorem aq_eq_zero_of_qvel {t : ℝ} {z : ℂ} (h : qvel D t z = 0) : aq D t z = 0 := by
  ext w
  rw [aq_apply hD, h]
  simp [omega2]

omit hD in
/-- The collar `{π|z|² > P}` (`P ≥ 0`) is preconnected. -/
theorem isPreconnected_collar {P : ℝ} (hP : 0 ≤ P) :
    IsPreconnected {z : ℂ | P < π * ‖z‖ ^ 2} := by
  set r₀ := Real.sqrt (P / π)
  have key : ∀ r : ℝ, 0 ≤ r → (P < π * r ^ 2 ↔ r₀ < r) := by
    intro r hr
    rw [show r₀ < r ↔ Real.sqrt (P / π) < Real.sqrt (r ^ 2) by rw [Real.sqrt_sq hr],
      Real.sqrt_lt_sqrt_iff (div_nonneg hP Real.pi_pos.le), div_lt_iff₀ Real.pi_pos, mul_comm]
  have hset : {z : ℂ | P < π * ‖z‖ ^ 2} =
      (fun p : ℝ × ℝ => Inner.Rot p.2 (p.1 : ℂ)) '' (Ioi r₀ ×ˢ univ) := by
    ext z
    simp only [mem_ofPred_eq, mem_image, mem_prod, mem_Ioi, mem_univ, and_true]
    constructor
    · intro h
      exact ⟨(‖z‖, Complex.arg z), (key _ (norm_nonneg _)).mp h, Inner.Rot_arg z⟩
    · rintro ⟨p, hp, rfl⟩
      have hp0 : 0 ≤ p.1 := le_trans (Real.sqrt_nonneg _) hp.le
      rw [Inner.norm_Rot, Complex.norm_real, Real.norm_of_nonneg hp0]
      exact (key _ hp0).mpr hp
  rw [hset]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
    (Inner.contDiff_Rot.continuous.comp (continuous_snd.prodMk
      (Complex.continuous_ofReal.comp continuous_fst))).continuousOn

theorem zbd_collar : D.Psupp < π * ‖zbd D‖ ^ 2 := by
  have hP := Psupp_nonneg hD
  have hh := hD.Psupp_lt_h
  have hpbd : 0 ≤ pbd D / π := div_nonneg (by unfold pbd; linarith) Real.pi_pos.le
  unfold zbd
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hpbd,
    mul_div_cancel₀ _ Real.pi_ne_zero]
  unfold pbd; linarith

/-- `h^q_t` is constant on the collar. -/
theorem hq_collar {t : ℝ} {z : ℂ} (hz : D.Psupp < π * ‖z‖ ^ 2) : hq D t z = hq D t (zbd D) := by
  have hO : IsOpen {z : ℂ | D.Psupp < π * ‖z‖ ^ 2} := isOpen_lt continuous_const continuous_area
  apply hO.is_const_of_fderiv_eq_zero (isPreconnected_collar (Psupp_nonneg hD))
    (fun w _ => (hq_deriv hD t w).differentiableAt.differentiableWithinAt)
    (fun w hw => ?_) hz (zbd_collar hD)
  rw [(hq_deriv hD t w).fderiv]
  exact aq_eq_zero_of_qvel hD (qvel_collar hD hw)

/-- **`prop:pln-hamiltonian`, support.** `Q_t = 0` on `{π|y|² > P_supp}`, for all `t`. -/
theorem Qham_support {t : ℝ} {y : ℂ} (hy : D.Psupp < π * ‖y‖ ^ 2) : Qham D t y = 0 := by
  unfold Qham Hq
  rw [qhatInv_collar hD hy, hq_collar hD hy, sub_self, neg_zero]

/-- **`prop:pln-hamiltonian`.** `Q_t = 0` for `t ∉ (0,1)`. -/
theorem Qham_time {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (y : ℂ) : Qham D t y = 0 := by
  have hz : ∀ z, hq D t z = 0 := by
    intro z
    unfold hq
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun r _ => by
      rw [aq_eq_zero_of_qvel hD (qvel_time hD ht _)]; rfl)]
    simp
  unfold Qham Hq
  rw [hz, hz, sub_self, neg_zero]

/-! ### `Q_t` generates `q̂_t` (`qhat_hamiltonian`) -/

/-- **`prop:pln-hamiltonian`.** `ι_{X_t}ω₂ = dH^q_t = -dQ_t` with `X_t = (∂_t q̂_t) ∘ q̂_t⁻¹`:
`ω₂(∂_t q̂_t(z), v) = -dQ_t(q̂_t z)[v]`. -/
theorem qhat_omega (t : ℝ) (z v : ℂ) :
    omega2 (qvel D t z) v = -fderiv ℝ (Qham D t) (qhat D t z) v := by
  set y := qhat D t z
  have hinv : HasFDerivAt (qhatInv D t) (fderiv ℝ (qhatInv D t) y) y :=
    (((qhatInv_smooth hD).comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp) y).hasFDerivAt
  have hzy : qhatInv D t y = z := qhatInv_qhat hD t z
  have hH : HasFDerivAt (Hq D t) ((aq D t z).comp (fderiv ℝ (qhatInv D t) y)) y := by
    have h := (hq_deriv hD t (qhatInv D t y)).comp y hinv
    rw [hzy] at h
    exact h.sub_const _
  have hQ : HasFDerivAt (Qham D t) (-((aq D t z).comp (fderiv ℝ (qhatInv D t) y))) y := hH.neg
  rw [hQ.fderiv]
  simp only [ContinuousLinearMap.neg_apply, neg_neg, coe_comp, Function.comp_apply]
  rw [aq_apply hD]
  -- `Dq̂_t(z) ∘ D(q̂_t⁻¹)(y) = id`
  have hq := (qhat_slice_smooth hD t).differentiable (by simp)
  have hid : qhat D t ∘ qhatInv D t = id := funext fun w => qhat_qhatInv hD t w
  have hc := fderiv_comp y (hq (qhatInv D t y)) hinv.differentiableAt
  rw [hid, fderiv_id, hzy] at hc
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hc
  simp only [coe_id', id_eq, coe_comp, Function.comp_apply] at this
  rw [← this]

/-- **`prop:pln-hamiltonian`.** `∂_t q̂_t = X_{Q_t} ∘ q̂_t` with `ι_{X_Q}ω₂ = -dQ`. -/
theorem qhat_hamiltonian (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s => qhat D s z) (hamVF2 (Qham D t) (qhat D t z)) t := by
  have h := qhat_hasDerivAt_time hD t z
  rwa [eq_hamVF2 (qhat_omega hD t z)] at h

end ham

/-! ### The interface for `sec:shd-four` -/

/-- **Summary of `sec:pln` for `sec:shd-four`.** For an ordinary path satisfying the interface, the explicit
isotopy `q̂_t` and Hamiltonian `Q_t` satisfy: joint smoothness of `q̂`, `q̂⁻¹` and `Q`;
`det Dq̂_t = 1`; bijectivity; `q̂_t = id` and `Q_t = 0` on `{π|z|² > P_supp}` (with
`P_supp < h`); `Q_t = 0` for `t ∉ (0,1)`; `∂_t q̂_t = X_{Q_t} ∘ q̂_t` (`ι_{X_Q}ω₂ = -dQ`);
`q̂_0 = id`; and `q̂_1 = 𝔢_1` on `{π|z|² ≤ h - 4e}`. -/
theorem qhat_interface {D : PathData} (hD : OrdinaryPath D) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhat D p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhatInv D p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => Qham D p.1 p.2) ∧
    (∀ t z, LinearMap.det (fderiv ℝ (qhat D t) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
    (∀ t, Function.Bijective (qhat D t)) ∧
    D.Psupp < D.h ∧
    (∀ t z, D.Psupp < π * ‖z‖ ^ 2 → qhat D t z = z) ∧
    (∀ t y, D.Psupp < π * ‖y‖ ^ 2 → Qham D t y = 0) ∧
    (∀ t y, (t ≤ 0 ∨ 1 ≤ t) → Qham D t y = 0) ∧
    (∀ t z, HasDerivAt (fun s => qhat D s z) (hamVF2 (Qham D t) (qhat D t z)) t) ∧
    (∀ t z v, omega2 (hamVF2 (Qham D t) (qhat D t z)) v =
      -fderiv ℝ (Qham D t) (qhat D t z) v) ∧
    qhat D 0 = id ∧
    (∀ z, π * ‖z‖ ^ 2 ≤ D.h - 4 * D.e → qhat D 1 z = D.path 1 z) :=
  ⟨qhat_smooth hD, qhatInv_smooth hD, Qham_smooth hD, qhat_symplectic hD, qhat_bijective hD,
    hD.Psupp_lt_h, fun _ _ hz => qhat_collar hD hz, fun _ _ hy => Qham_support hD hy,
    fun _ y ht => Qham_time hD ht y, qhat_hamiltonian hD,
    fun t z v => by rw [← eq_hamVF2 (qhat_omega hD t z)]; exact qhat_omega hD t z v,
    qhat_zero hD, fun z hz => qhat_one_eq hD (hz.trans (pon_bounds hD).1.le)⟩

end SymplecticPacking.Qhat
