import SymplecticPacking.Bundle.BaseData

/-!
# The base area forms and the torus primitive operator

`sec:fer` (`def:fer-kappa`, `lem:fer-kappa`, `def:fer-Pprim`, `lem:fer-Pprim`,
`def:fer-Delta`): the base area forms `χ`, `κ(p) = (1 − 3p)σ`, `κ₁(p) = e_h ν + H*(p) χ`,
the torus primitive operator `P_prim` and `α₁⁰ = P_prim(κ₁ − κ)`.

Two-forms are coefficients of `ν = du ∧ dv`. `AffineP` records affine dependence on `p`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Set Filter Topology MeasureTheory
open scoped ContDiff Real

/-! ### Affine dependence on `p` -/

/-- `f` is affine in `p`: `f(u, v, p) = f(u, v, 0) + p (f(u, v, 1) − f(u, v, 0))`. -/
def AffineP (f : Coef) : Prop := ∀ u v p, f u v p = f u v 0 + p * (f u v 1 - f u v 0)

lemma AffineP.of_eq {f : Coef} (a b : ℝ → ℝ → ℝ) (h : ∀ u v p, f u v p = a u v + p * b u v) :
    AffineP f := by
  intro u v p; rw [h, h u v 0, h u v 1]; ring

lemma AffineP.sub {f g : Coef} (hf : AffineP f) (hg : AffineP g) : AffineP (f - g) := by
  intro u v p; simp only [Pi.sub_apply]; rw [hf, hg]; ring

lemma AffineP.pu {f : Coef} (hf : AffineP f) {u v : ℝ}
    (h0 : DifferentiableAt ℝ (fun s => f s v 0) u) (h1 : DifferentiableAt ℝ (fun s => f s v 1) u)
    (p : ℝ) : pu f u v p = pu f u v 0 + p * (pu f u v 1 - pu f u v 0) := by
  simp only [Bundle.pu]
  have e : (fun s => f s v p) = fun s => f s v 0 + p * (f s v 1 - f s v 0) := funext fun s => hf s v p
  rw [e]; exact ((h0.hasDerivAt).add ((h1.hasDerivAt.sub h0.hasDerivAt).const_mul p)).deriv

lemma AffineP.pv {f : Coef} (hf : AffineP f) {u v : ℝ}
    (h0 : DifferentiableAt ℝ (fun t => f u t 0) v) (h1 : DifferentiableAt ℝ (fun t => f u t 1) v)
    (p : ℝ) : pv f u v p = pv f u v 0 + p * (pv f u v 1 - pv f u v 0) := by
  simp only [Bundle.pv]
  have e : (fun t => f u t p) = fun t => f u t 0 + p * (f u t 1 - f u t 0) := funext fun t => hf u t p
  rw [e]; exact ((h0.hasDerivAt).add ((h1.hasDerivAt.sub h0.hasDerivAt).const_mul p)).deriv

/-- Integrals of affine families are affine. -/
lemma integral_affine {g : ℝ → ℝ → ℝ} (hg : ∀ t p, g t p = g t 0 + p * (g t 1 - g t 0))
    {a b : ℝ} (h0 : IntervalIntegrable (fun t => g t 0) volume a b)
    (h1 : IntervalIntegrable (fun t => g t 1) volume a b) (p : ℝ) :
    ∫ t in a..b, g t p = (∫ t in a..b, g t 0) + p * ((∫ t in a..b, g t 1) - ∫ t in a..b, g t 0) := by
  have e : (fun t => g t p) = fun t => g t 0 + p * (g t 1 - g t 0) := funext fun t => hg t p
  rw [e, intervalIntegral.integral_add h0 ((h1.sub h0).const_mul p),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h1 h0]

/-! ### `χ` and the base area forms -/

/-- `χ = f'(s) ds ∧ β`, as a multiple of `ν` (extended periodically by zero). -/
def chiA (u v : ℝ) : ℝ := deriv stepA (Int.fract u) * bB v

lemma contDiff_deriv_stepA_fract : ContDiff ℝ ∞ (fun u => deriv stepA (Int.fract u)) :=
  contDiff_comp_fract contDiff_deriv_stepA (a := u0) (b := u1) (by norm_num [u0])
    (by norm_num [u1]) fun s hs => deriv_stepA_eq_zero fun h => hs (Ioo_subset_Icc_self h)

lemma contDiff_chiA : ContDiff ℝ ∞ (fun x : ℝ × ℝ => chiA x.1 x.2) :=
  (contDiff_deriv_stepA_fract.comp contDiff_fst).mul (contDiff_bB.comp contDiff_snd)

lemma chiA_nonneg (u v : ℝ) : 0 ≤ chiA u v := mul_nonneg (deriv_stepA_nonneg _) (bB_nonneg v)

lemma integral_deriv_stepA_fract : ∫ u in (0 : ℝ)..1, deriv stepA (Int.fract u) = 1 := by
  have e : ∫ u in (0 : ℝ)..1, deriv stepA (Int.fract u) = ∫ u in (0 : ℝ)..1, deriv stepA u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    rcases hu.2.lt_or_eq with h | h
    · rw [fract_of_mem_Ico ⟨hu.1, h⟩]
    · subst h
      simp only [Int.fract_one]
      rw [deriv_stepA_eq_zero (by norm_num [u0]), deriv_stepA_eq_zero (by norm_num [u1])]
  rw [e, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => contDiff_stepA.differentiable (by simp) x)
    (contDiff_deriv_stepA.continuous.intervalIntegrable _ _),
    stepA_eq_one (by norm_num [u1]), stepA_eq_zero (by norm_num [u0])]
  norm_num

/-- **`∫ χ = 1`** (`lem:fer-kappa`). -/
theorem integral_chi : torusInt chiA = 1 := by
  unfold torusInt chiA
  simp only [intervalIntegral.integral_mul_const, integral_deriv_stepA_fract, one_mul]
  exact integral_bB

/-- `κ(p) = (1 − 3p) σ`. -/
def kappa : Coef := fun u v p => (1 - 3 * p) * sigmaC u v

/-- `κ₁(p) = e_h ν + H*(p) χ`. -/
def kappa1 (P : Params) : Coef := fun u v p => P.eh + P.Hstar p * chiA u v

lemma integral_kappa (p : ℝ) : torusInt (fun u v => kappa u v p) = 3 * (1 - 3 * p) := by
  unfold torusInt kappa
  simp only [intervalIntegral.integral_const_mul]
  have := integral_sigma
  unfold torusInt at this
  rw [this]; ring

lemma contDiff_kappa (p : ℝ) : ContDiff ℝ ∞ (sl kappa p) :=
  contDiff_const.mul contDiff_sigmaC

lemma contDiff_kappa1 (P : Params) (p : ℝ) : ContDiff ℝ ∞ (sl (kappa1 P) p) :=
  contDiff_const.add (contDiff_const.mul contDiff_chiA)

lemma kappa_affine : AffineP kappa :=
  AffineP.of_eq (fun u v => sigmaC u v) (fun u v => -3 * sigmaC u v) fun u v p => by
    simp only [kappa]; ring

lemma kappa1_affine (P : Params) : AffineP (kappa1 P) :=
  AffineP.of_eq (fun u v => P.eh + (3 - P.eh) * chiA u v) (fun u v => -9 * chiA u v)
    fun u v p => by simp only [kappa1, Params.Hstar, Params.Hb]; ring

/-! ### The torus primitive operator (`def:fer-Pprim`) -/

/-- `𝔟₀(v) = ∫₀¹ 𝔟(u, v) du`. -/
def Pb0 (b : Coef) (v p : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, b u v p

/-- `A₀(u, v) = ∫₀ᵘ [𝔟(s, v) − 𝔟₀(v)] ds`. -/
def PA0 (b : Coef) (u v p : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, (b s v p - Pb0 b v p)

/-- `B₀(v) = ∫₀ᵛ 𝔟₀(t) dt`. -/
def PB0 (b : Coef) (v p : ℝ) : ℝ := ∫ t in (0 : ℝ)..v, Pb0 b t p

/-- **`P_prim(𝔟 ν) = A₀ dv − B₀ du`.** -/
def Pprim (b : Coef) : BForm := ⟨fun _ v p => -PB0 b v p, fun u v p => PA0 b u v p⟩

section Pprim

variable {b : Coef}

lemma continuous_Pb0 {p : ℝ} (hb : Continuous (sl b p)) : Continuous (fun v => Pb0 b v p) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun v u => b u v p) (hb.comp continuous_swap) 0 1

lemma contDiff_Pb0 {p : ℝ} (hb : ContDiff ℝ ∞ (sl b p)) : ContDiff ℝ ∞ (fun v => Pb0 b v p) :=
  contDiff_integral_const (P := ℝ) (g := fun x : ℝ × ℝ => b x.1 x.2 p)
    (hb.comp (contDiff_fst.prodMk contDiff_snd)) 0 1

lemma contDiff_PA0 {p : ℝ} (hb : ContDiff ℝ ∞ (sl b p)) :
    ContDiff ℝ ∞ (sl (fun u v p => PA0 b u v p) p) := by
  have := contDiff_primitive (P := ℝ × ℝ)
    (g := fun y : ℝ × (ℝ × ℝ) => b y.1 y.2.2 p - Pb0 b y.2.2 p)
    ((hb.comp (contDiff_fst.prodMk contDiff_snd.snd)).sub
      ((contDiff_Pb0 hb).comp contDiff_snd.snd)) (s := fun x => x.1) contDiff_fst
  exact this

lemma contDiff_PB0 {p : ℝ} (hb : ContDiff ℝ ∞ (sl b p)) :
    ContDiff ℝ ∞ (sl (fun _ v p => PB0 b v p) p) := by
  have := contDiff_primitive (P := ℝ) (g := fun y : ℝ × ℝ => Pb0 b y.1 p)
    ((contDiff_Pb0 hb).comp contDiff_fst) (s := id) contDiff_id
  exact this.comp contDiff_snd

lemma contDiff_Pprim_cu {p : ℝ} (hb : ContDiff ℝ ∞ (sl b p)) :
    ContDiff ℝ ∞ (sl (Pprim b).cu p) := (contDiff_PB0 hb).neg

lemma contDiff_Pprim_cv {p : ℝ} (hb : ContDiff ℝ ∞ (sl b p)) :
    ContDiff ℝ ∞ (sl (Pprim b).cv p) := contDiff_PA0 hb

/-- **`d_C P_prim(𝔟 ν) = 𝔟 ν`** (`lem:fer-Pprim`). -/
theorem d_Pprim {p : ℝ} (hb : Continuous (sl b p)) (u v : ℝ) : (Pprim b).dC u v p = b u v p := by
  have hs : Continuous (fun s => b s v p - Pb0 b v p) :=
    (hb.comp (continuous_id.prodMk continuous_const)).sub continuous_const
  have h1 := (hs.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h2 := ((continuous_Pb0 hb).integral_hasStrictDerivAt 0 v).hasDerivAt.neg
  simp only [BForm.dC, Pprim, Bundle.pu, Bundle.pv, PA0, PB0]
  rw [h1.deriv]
  rw [show (fun t => -∫ x in (0 : ℝ)..t, Pb0 b x p) = -fun t => ∫ x in (0 : ℝ)..t, Pb0 b x p
    from rfl, h2.deriv]
  ring

/-- **`A₀`, `B₀` are `1`-periodic** (`lem:fer-Pprim`), for periodic `𝔟` with `∫ 𝔟 ν = 0`. -/
theorem Pprim_periodic (hb : ∀ p, Continuous (sl b p)) (hper : CoefPeriodic b)
    (hmean : ∀ p, torusInt (fun u v => b u v p) = 0) : (Pprim b).Periodic := by
  have hb0per : ∀ v p, Pb0 b (v + 1) p = Pb0 b v p := fun v p => by
    simp only [Pb0, (hper _ v p).2]
  have hA0v : ∀ u v p, PA0 b u (v + 1) p = PA0 b u v p := fun u v p => by
    simp only [PA0, hb0per, (hper _ v p).2]
  have hA0u : ∀ u v p, PA0 b (u + 1) v p = PA0 b u v p := fun u v p => by
    have hs : Continuous (fun s => b s v p - Pb0 b v p) :=
      ((hb p).comp (continuous_id.prodMk continuous_const)).sub continuous_const
    have hpers : Function.Periodic (fun s => b s v p - Pb0 b v p) 1 := fun s => by
      simp only [(hper s v p).1]
    simp only [PA0]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable 0 u)
      (hs.intervalIntegrable u (u + 1)), hpers.intervalIntegral_add_eq u 0, zero_add]
    have hi : IntervalIntegrable (fun x => b x v p) volume 0 1 :=
      ((hb p).comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    have hz : ∫ x in (0 : ℝ)..1, (b x v p - Pb0 b v p) = 0 := by
      rw [intervalIntegral.integral_sub hi intervalIntegrable_const]; simp [Pb0]
    rw [hz, add_zero]
  have hB0v : ∀ v p, PB0 b (v + 1) p = PB0 b v p := fun v p => by
    have hc := continuous_Pb0 (hb p)
    have hper0 : Function.Periodic (fun t => Pb0 b t p) 1 := fun t => hb0per t p
    simp only [PB0]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 v)
      (hc.intervalIntegrable v (v + 1)), hper0.intervalIntegral_add_eq v 0, zero_add]
    have := hmean p
    unfold torusInt at this
    simp only [Pb0] at this ⊢
    rw [this, add_zero]
  intro u v p
  exact ⟨rfl, hA0u u v p, by simp only [Pprim]; rw [hB0v], hA0v u v p⟩

/-- `P_prim` preserves affine dependence on `p`. -/
theorem Pprim_affine (hb : AffineP b) (h0 : Continuous (sl b 0)) (h1 : Continuous (sl b 1)) :
    AffineP (Pprim b).cu ∧ AffineP (Pprim b).cv := by
  have hb0 : ∀ v p, Pb0 b v p = Pb0 b v 0 + p * (Pb0 b v 1 - Pb0 b v 0) := fun v p =>
    integral_affine (g := fun u p => b u v p) (fun u p => hb u v p)
      ((h0.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      ((h1.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _) p
  constructor
  · intro u v p
    simp only [Pprim, PB0]
    rw [integral_affine (g := fun t p => Pb0 b t p) (fun t p => hb0 t p)
      ((continuous_Pb0 h0).intervalIntegrable _ _) ((continuous_Pb0 h1).intervalIntegrable _ _) p]
    ring
  · intro u v p
    simp only [Pprim, PA0]
    refine integral_affine (g := fun s p => b s v p - Pb0 b v p) (fun s p => by
      rw [hb s v p, hb0 v p]; ring)
      (((h0.comp (continuous_id.prodMk continuous_const)).sub continuous_const).intervalIntegrable _ _)
      (((h1.comp (continuous_id.prodMk continuous_const)).sub continuous_const).intervalIntegrable _ _) p

end Pprim

/-! ### `α₁⁰` (`def:fer-Delta`) -/

/-- The exact base two-form `κ₁ − κ`. -/
def kdiff (P : Params) : Coef := kappa1 P - kappa

lemma contDiff_kdiff (P : Params) (p : ℝ) : ContDiff ℝ ∞ (sl (kdiff P) p) :=
  (contDiff_kappa1 P p).sub (contDiff_kappa p)

/-- The Gram determinant `‖f‖²‖g‖² − |⟨f, g⟩|²`. -/
def gram (f g : Fin 3 → ℂ) : ℝ :=
  normSq3 f * normSq3 g - ((herm3 f g).re ^ 2 + (herm3 f g).im ^ 2)

lemma gram_smul (e e' : ℂ) (f g : Fin 3 → ℂ) :
    gram (e • f) (e • g + e' • f) = ‖e‖ ^ 4 * gram f g := by
  unfold gram
  rw [lagrange3, lagrange3]
  have key : ∀ i j : Fin 3, (e • f) i * (e • g + e' • f) j - (e • f) j * (e • g + e' • f) i =
      e ^ 2 * (f i * g j - f j * g i) := by
    intro i j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [key, key, key]
  simp only [norm_mul, norm_pow, mul_pow]
  ring

lemma sigmaC_eq_gram (u v : ℝ) : sigmaC u v = tau.im * gram (Zraw (torusZ u v))
    (deriv Zraw (torusZ u v)) / (π * normSq3 (Zraw (torusZ u v)) ^ 2) := sigmaC_eq u v

lemma deriv_Zraw_add_tau (z : ℂ) : deriv Zraw (z + tau) = thetaFactor (π * z) ^ 3 • deriv Zraw z +
    deriv (fun w => thetaFactor (π * w) ^ 3) z • Zraw z := by
  have hE : DifferentiableAt ℂ (fun w => thetaFactor (π * w) ^ 3) z :=
    ((differentiable_thetaFactor.comp (differentiable_id.const_mul _)).pow 3) z
  have h : (fun w => Zraw (w + tau)) = fun w => thetaFactor (π * w) ^ 3 • Zraw w :=
    funext Zraw_add_tau
  rw [← deriv_comp_add_const, h]
  exact (hE.hasDerivAt.smul (differentiable_Zraw z).hasDerivAt).deriv

lemma deriv_Zraw_add_one (z : ℂ) : deriv Zraw (z + 1) = (-1 : ℂ) • deriv Zraw z +
    (0 : ℂ) • Zraw z := by
  have h : (fun w => Zraw (w + 1)) = fun w => (-1 : ℂ) • Zraw w := funext Zraw_add_one
  rw [← deriv_comp_add_const, h]
  exact ((differentiable_Zraw z).hasDerivAt.const_smul (-1 : ℂ)).deriv.trans (by simp)

lemma sigma_shift {f f' : Fin 3 → ℂ} (hf : f ≠ 0) {e e' : ℂ} (he : e ≠ 0) :
    tau.im * gram (e • f) (e • f' + e' • f) / (π * normSq3 (e • f) ^ 2) =
      tau.im * gram f f' / (π * normSq3 f ^ 2) := by
  rw [gram_smul, normSq3_smul]
  have h1 : 0 < ‖e‖ := norm_pos_iff.mpr he
  have h2 := normSq3_pos hf
  field_simp

/-- `σ` is `1`-periodic in `u` and `v`. -/
lemma sigmaC_periodic (u v : ℝ) : sigmaC (u + 1) v = sigmaC u v ∧ sigmaC u (v + 1) = sigmaC u v := by
  constructor
  · rw [sigmaC_eq_gram, sigmaC_eq_gram, torusZ_add_one_left, Zraw_add_one, deriv_Zraw_add_one]
    exact sigma_shift (Zraw_ne_zero _) (by norm_num)
  · rw [sigmaC_eq_gram, sigmaC_eq_gram, torusZ_add_one_right, Zraw_add_tau, deriv_Zraw_add_tau]
    exact sigma_shift (Zraw_ne_zero _) (pow_ne_zero 3 (thetaFactor_ne_zero _))

lemma chiA_periodic (u v : ℝ) : chiA (u + 1) v = chiA u v ∧ chiA u (v + 1) = chiA u v := by
  simp [chiA, Int.fract_add_one, bB_add_one]

attribute [local irreducible] sigmaC chiA in

/-- **`α₁⁰(p) = P_prim(κ₁(p) − κ(p))`** (`def:fer-Delta`). -/
def alpha10 (P : Params) : BForm := Pprim (kdiff P)

/-- `d_C α₁⁰ = κ₁ − κ`. -/
theorem d_alpha10 (P : Params) (u v p : ℝ) :
    (alpha10 P).dC u v p = kappa1 P u v p - kappa u v p :=
  d_Pprim (contDiff_kdiff P p).continuous u v

theorem alpha10_affine (P : Params) : AffineP (alpha10 P).cu ∧ AffineP (alpha10 P).cv :=
  Pprim_affine ((kappa1_affine P).sub kappa_affine) (contDiff_kdiff P 0).continuous
    (contDiff_kdiff P 1).continuous

end SymplecticPacking.Bundle
