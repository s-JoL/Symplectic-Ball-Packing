import SymplecticPacking.General.Ham.Spec

/-!
# The radial source primitive

`sec:ham-hamiltonian`, formula (23): the radial source primitive `h_t(u) = ∫₀¹ a_t(ru)[u] dr` satisfies
`d_u h_t = a_t` on `B(ρ)`.

Proof: `a_t(y)[v] = ω₀(∂_t F(t,y), D_y F(t,y) v)` is a closed 1-form on the ball, because
`F_t^*ω₀ = ω₀` for every `t` (differentiate in `t`, use symmetry of second derivatives); then
apply Mathlib's Poincaré lemma for segments
(`Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter ContinuousLinearMap Problem
open scoped ContDiff Topology

/-! ### Partial derivatives of a jointly smooth family -/

variable {n : ℕ} {F : ℝ → E n → E n}

/-- The uncurried family. -/
def unc (F : ℝ → E n → E n) (p : ℝ × E n) : E n := F p.1 p.2

lemma hasFDerivAt_slice {t : ℝ} {y : E n} (h : DifferentiableAt ℝ (unc F) (t, y)) :
    HasFDerivAt (F t) ((fderiv ℝ (unc F) (t, y)).comp (inr ℝ ℝ (E n))) y :=
  h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)

lemma hasDerivAt_time {t : ℝ} {y : E n} (h : DifferentiableAt ℝ (unc F) (t, y)) :
    HasDerivAt (fun s => F s y) (fderiv ℝ (unc F) (t, y) (1, 0)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × E n)) ((1 : ℝ), (0 : E n)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact h.hasFDerivAt.comp_hasDerivAt t h1

/-- The candidate 1-form `A_t(y) = ω₀(D(t,y)(1,0), D(t,y)(0,·))`, `D = D(unc F)`. -/
def oneForm (F : ℝ → E n → E n) (t : ℝ) (y : E n) : E n →L[ℝ] ℝ :=
  (omega0L (fderiv ℝ (unc F) (t, y) (1, 0))).comp ((fderiv ℝ (unc F) (t, y)).comp (inr ℝ ℝ (E n)))

lemma sourceOneForm_eq {t : ℝ} {y : E n} (h : DifferentiableAt ℝ (unc F) (t, y)) (v : E n) :
    sourceOneForm F t y v = oneForm F t y v := by
  simp only [sourceOneForm, oneForm, (hasDerivAt_time h).deriv, (hasFDerivAt_slice h).fderiv,
    coe_comp, Function.comp_apply, omega0L_apply]

/-! ### Closedness -/

variable {ρ : ℝ}

/-- Hypotheses: `unc F` smooth near `{t} × B(ρ)` for all `t`, and `F s` symplectic on `B(ρ)`. -/
structure SympFamily (F : ℝ → E n → E n) (ρ : ℝ) : Prop where
  smooth : ∀ s, ∀ y ∈ ball (0 : E n) ρ, ContDiffAt ℝ ∞ (unc F) (s, y)
  sympl : ∀ s, ∀ y ∈ ball (0 : E n) ρ, IsSymplecticLinear (fderiv ℝ (F s) y)

lemma SympFamily.differentiableAt (hF : SympFamily F ρ) {s : ℝ} {y : E n}
    (hy : y ∈ ball (0 : E n) ρ) : DifferentiableAt ℝ (unc F) (s, y) :=
  (hF.smooth s y hy).differentiableAt (by simp)

lemma SympFamily.fderiv_differentiableAt (hF : SympFamily F ρ) {s : ℝ} {y : E n}
    (hy : y ∈ ball (0 : E n) ρ) : DifferentiableAt ℝ (fderiv ℝ (unc F)) (s, y) :=
  ((hF.smooth s y hy).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)

/-- Derivative of `oneForm` in `y`. -/
def dOneForm (F : ℝ → E n → E n) (t : ℝ) (y : E n) : E n →L[ℝ] E n →L[ℝ] ℝ :=
  let D := fderiv ℝ (unc F) (t, y)
  let S := fderiv ℝ (fderiv ℝ (unc F)) (t, y)
  { toFun := fun u =>
      (omega0L (S (0, u) (1, 0))).comp (D.comp (inr ℝ ℝ (E n))) +
        (omega0L (D (1, 0))).comp ((S (0, u)).comp (inr ℝ ℝ (E n)))
    map_add' := by
      intro u u'; ext v
      have e : ((0 : ℝ), u + u') = ((0 : ℝ), u) + ((0 : ℝ), u') := by simp
      simp only [e, map_add, add_apply, coe_comp, Function.comp_apply, omega0L_apply,
        omega0_add_left, omega0_add_right]
      ring
    map_smul' := by
      intro c u; ext v
      have e : ((0 : ℝ), c • u) = c • ((0 : ℝ), u) := by simp
      simp only [e, map_smul, smul_apply, coe_comp, Function.comp_apply, omega0L_apply,
        omega0_smul_left, omega0_smul_right, RingHom.id_apply, add_apply, smul_eq_mul]
      ring
    cont := by
      apply Continuous.add
      · exact (omega0L.continuous.comp ((apply ℝ (E n) ((1 : ℝ), (0 : E n))).continuous.comp
          (S.continuous.comp (continuous_const.prodMk continuous_id)))).clm_comp continuous_const
      · exact continuous_const.clm_comp
          ((S.continuous.comp (continuous_const.prodMk continuous_id)).clm_comp
            continuous_const) }

lemma hasFDerivAt_oneForm (hF : SympFamily F ρ) {t : ℝ} {y : E n} (hy : y ∈ ball (0 : E n) ρ) :
    HasFDerivAt (oneForm F t) (dOneForm F t y) y := by
  set D := fderiv ℝ (unc F)
  -- `y ↦ D (t, y)` has derivative `S ∘ inr`
  have hD : HasFDerivAt (fun z => D (t, z)) ((fderiv ℝ D (t, y)).comp (inr ℝ ℝ (E n))) y :=
    (hF.fderiv_differentiableAt hy).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  have h1 : HasFDerivAt (fun z => omega0L (D (t, z) (1, 0)))
      (omega0L.comp ((apply ℝ (E n) ((1 : ℝ), (0 : E n))).comp
        ((fderiv ℝ D (t, y)).comp (inr ℝ ℝ (E n))))) y :=
    omega0L.hasFDerivAt.comp y ((apply ℝ (E n) ((1 : ℝ), (0 : E n))).hasFDerivAt.comp y hD)
  have h2 : HasFDerivAt (fun z => (D (t, z)).comp (inr ℝ ℝ (E n)))
      ((compL ℝ (E n) (ℝ × E n) (E n)).flip (inr ℝ ℝ (E n)) |>.comp
        ((fderiv ℝ D (t, y)).comp (inr ℝ ℝ (E n)))) y :=
    ((compL ℝ (E n) (ℝ × E n) (E n)).flip (inr ℝ ℝ (E n))).hasFDerivAt.comp y hD
  have h3 := h1.clm_comp h2
  refine h3.congr_fderiv ?_
  ext u v
  simp only [dOneForm, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply, coe_comp,
    Function.comp_apply, inr_apply, omega0L_apply, D, compL_apply, flip_apply, apply_apply]
  ring

/-- **Closedness** of the source one-form. -/
theorem dOneForm_symm (hF : SympFamily F ρ) {t : ℝ} {y : E n} (hy : y ∈ ball (0 : E n) ρ)
    (u v : E n) : dOneForm F t y u v = dOneForm F t y v u := by
  set D := fderiv ℝ (unc F) (t, y)
  set S := fderiv ℝ (fderiv ℝ (unc F)) (t, y)
  have hsym : ∀ a b, S a b = S b a := fun a b =>
    (hF.smooth t y hy).isSymmSndFDerivAt (by simp) a b
  -- the symplectic identity, differentiated in time
  have hconst : ∀ s, Problem.omega0 (fderiv ℝ (unc F) (s, y) (0, u)) (fderiv ℝ (unc F) (s, y) (0, v)) =
      Problem.omega0 u v := by
    intro s
    have := hF.sympl s y hy u v
    rwa [(hasFDerivAt_slice (hF.differentiableAt (s := s) hy)).fderiv] at this
  have hcurve : HasDerivAt (fun s => fderiv ℝ (unc F) (s, y)) (S (1, 0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × E n)) ((1 : ℝ), (0 : E n)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (hF.fderiv_differentiableAt hy).hasFDerivAt.comp_hasDerivAt t h1
  have hderiv : HasDerivAt
      (fun s => omega0L (fderiv ℝ (unc F) (s, y) (0, u)) (fderiv ℝ (unc F) (s, y) (0, v)))
      (omega0L (S (1, 0) (0, u)) (D (0, v)) + omega0L (D (0, u)) (S (1, 0) (0, v))) t := by
    have hu := hcurve.clm_apply (hasDerivAt_const t ((0 : ℝ), u))
    have hv := hcurve.clm_apply (hasDerivAt_const t ((0 : ℝ), v))
    simp only [zero_apply, map_zero, add_zero] at hu hv
    have hw := (omega0L.hasFDerivAt.comp_hasDerivAt t hu).clm_apply hv
    simpa [add_comm] using hw
  have hzero : Problem.omega0 (S (1, 0) (0, u)) (D (0, v)) + Problem.omega0 (D (0, u)) (S (1, 0) (0, v)) = 0 := by
    have h0 : HasDerivAt
        (fun s => omega0L (fderiv ℝ (unc F) (s, y) (0, u)) (fderiv ℝ (unc F) (s, y) (0, v))) 0 t := by
      have : (fun s => omega0L (fderiv ℝ (unc F) (s, y) (0, u)) (fderiv ℝ (unc F) (s, y) (0, v)))
          = fun _ => Problem.omega0 u v := funext fun s => hconst s
      rw [this]; exact hasDerivAt_const t _
    simpa using hderiv.unique h0
  simp only [dOneForm, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply, coe_comp,
    Function.comp_apply, inr_apply, omega0L_apply]
  rw [hsym (0, u) (1, 0), hsym (0, v) (1, 0), hsym (0, u) (0, v)]
  rw [omega0_skew (D (0, u)) (S (1, 0) (0, v))] at hzero
  linarith

/-! ### The primitive -/

theorem hasFDerivAt_sourcePrimitive (hF : SympFamily F ρ) {t : ℝ} {b : E n}
    (hb : b ∈ ball (0 : E n) ρ) :
    HasFDerivAt (sourcePrimitive F t) (oneForm F t b) b := by
  have hconv : Convex ℝ (ball (0 : E n) ρ) := convex_ball 0 ρ
  have h0 : (0 : E n) ∈ ball (0 : E n) ρ := by
    rw [mem_ball_zero_iff] at hb ⊢; simpa using (norm_nonneg b).trans_lt hb
  have hP := hconv.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (fun x hx => (hasFDerivAt_oneForm hF (t := t) hx).hasFDerivWithinAt)
    (fun a ha x _ y _ => dOneForm_symm hF (t := t) ha x y) h0 hb
  have hP' := hP.hasFDerivAt (isOpen_ball.mem_nhds hb)
  apply hP'.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hb] with c hc
  rw [curveIntegral_segment]
  unfold sourcePrimitive
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le zero_le_one] at hr
  have hrc : r • c ∈ ball (0 : E n) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.1] at *
    calc r * ‖c‖ ≤ 1 * ‖c‖ := by gcongr; exact hr.2
      _ < ρ := by rw [one_mul]; exact hc
  simp only [AffineMap.lineMap_apply_zero, sub_zero]
  rw [show (AffineMap.lineMap (0 : E n) c) r = r • c by simp [AffineMap.lineMap_apply]]
  exact sourceOneForm_eq (hF.differentiableAt hrc) c

end SymplecticPacking.General.Ham
