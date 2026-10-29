import SymplecticPacking.Handle.SecondStage
import SymplecticPacking.Handle.MoserBoxConcat
import SymplecticPacking.Return.Central

/-!
# The deck maps of the cover of the normal bundle

`sec:shd-four` (`cons:shd4-moser`): the explicit deck maps of the cover `E4` of `N` and the invariance of
the base data (Supplement, four-dimensional handle).

From `Zunit_add_one_left` (`Z(u+1, v) = −Z`) and `Zunit_add_one_right`
(`Z(u, v+1) = φ(u, v) Z`, `φ = phaseV`, from `Zraw_automorphy`):
* `phaseV_eq`: `φ(u, v) = −exp(i(3π/2 − 6πu + 3πv))` (explicit), so
  `∂_u φ = −6πi φ`, `∂_v φ = 3πi φ`, `φ(u+1, v) = φ(u, v)`;
* `etaHu_add_one_right`, `etaHv_add_one_right`: `η_H(u, v+1) = η_H(u, v) − 3 du + (3/2) dv`;
  `etaHu_add_one_left`: `η_H(u+1, v) = η_H(u, v)`;
* the deck maps `TuE (x,y,u,v) = (−w, u+1, v)` and `TvE (w,u,v) = (φ(u,v)³ w, u, v+1)`
  (`w = x + iy`), as `DeckCore`s `deckU`, `deckV`;
* `pull1_TuE_betaLoc`: `Tu^* β = β`; `pull1_TvE_betaLoc`: `Tv^* β = β − 3 du + (3/2) dv` for the
  primitive `β = betaLoc` of `Ω₀` (`Return/Central.lean`); hence `Tu^* Ω₀ = Tv^* Ω₀ = Ω₀`
  (`pull2_Omega0loc_u`, `pull2_Omega0loc_v`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap _root_.Complex ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE Zunit phaseV autE tau tau_re thetaFactor torusZ etaHu etaHv
  dZu dZv herm3 Zunit_add_one_left Zunit_add_one_right etaExpr_smul Zunit_unit norm_phaseV
  conj_mul_self_of_norm_one hasDerivAt_Zunit_u hasDerivAt_Zunit_v dZu_eq dZv_eq)
open SymplecticPacking.Return (betaLoc fuC fvC)
open scoped ContDiff Real

attribute [local irreducible] etaHu etaHv

set_option synthInstance.maxHeartbeats 200000

/-! ### The explicit phase -/

/-- The angle of the phase: `φ(u, v) = −exp(i θ(u, v))`. -/
def phaseAng (u v : ℝ) : ℝ := 3 * π / 2 - 6 * π * u + 3 * π * v

theorem phaseV_eq (u v : ℝ) : phaseV u v = -cexp ((phaseAng u v : ℂ) * I) := by
  set E : ℂ := -(3 * π * I * tau) - 6 * π * I * (u + v * tau) with hE
  have he : autE u v = -cexp E := by
    simp only [autE, thetaFactor, torusZ]
    rw [neg_pow, ← Complex.exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (-(↑π * I * tau) - 2 * I * (↑π * (↑u + ↑v * tau))) = E := by
      rw [hE]; push_cast; ring
    rw [this]; ring
  have hsplit : cexp E = (Real.exp E.re : ℂ) * cexp ((E.im : ℂ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    exact (Complex.re_add_im E).symm
  have hn : ‖autE u v‖ = Real.exp E.re := by rw [he, norm_neg, Complex.norm_exp]
  have him : E.im = phaseAng u v := by
    rw [hE]
    simp only [sub_im, neg_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
      tau_re]
    unfold phaseAng
    have h3 : (3 : ℂ).re = 3 := rfl
    have h3' : (3 : ℂ).im = 0 := rfl
    have h6 : (6 : ℂ).re = 6 := rfl
    have h6' : (6 : ℂ).im = 0 := rfl
    simp only [h3, h3', h6, h6']
    ring
  rw [phaseV, hn, he, hsplit, him, Complex.real_smul]
  have hpos : (Real.exp E.re : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  push_cast
  field_simp

lemma hasDerivAt_phaseV_u (u v : ℝ) :
    HasDerivAt (fun s => phaseV s v) (-(6 * π * I) * phaseV u v) u := by
  have h : HasDerivAt (fun s : ℝ => ((phaseAng s v : ℝ) : ℂ) * I) (-(6 * π) * I) u := by
    have h1 : HasDerivAt (fun s : ℝ => phaseAng s v) (-(6 * π)) u := by
      unfold phaseAng
      simpa using ((hasDerivAt_id u).const_mul (6 * π)).const_sub (3 * π / 2) |>.add_const
        (3 * π * v)
    have := (h1.ofReal_comp).mul_const I
    simpa using this
  have := (h.cexp).neg
  convert this using 1
  · funext s; exact phaseV_eq s v
  · rw [phaseV_eq]; ring

lemma hasDerivAt_phaseV_v (u v : ℝ) :
    HasDerivAt (fun t => phaseV u t) ((3 * π * I) * phaseV u v) v := by
  have h : HasDerivAt (fun t : ℝ => ((phaseAng u t : ℝ) : ℂ) * I) ((3 * π) * I) v := by
    have h1 : HasDerivAt (fun t : ℝ => phaseAng u t) (3 * π) v := by
      unfold phaseAng
      simpa using ((hasDerivAt_id v).const_mul (3 * π)).const_add (3 * π / 2 - 6 * π * u)
    have := (h1.ofReal_comp).mul_const I
    simpa using this
  have := (h.cexp).neg
  convert this using 1
  · funext t; exact phaseV_eq u t
  · rw [phaseV_eq]; ring

lemma phaseV_add_int_left (u v : ℝ) (k : ℤ) : phaseV (u + k) v = phaseV u v := by
  rw [phaseV_eq, phaseV_eq]
  have : (phaseAng (u + k) v : ℂ) * I = (phaseAng u v : ℂ) * I + (-(3 * k) : ℤ) * (2 * π * I) := by
    unfold phaseAng; push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### `η_H` under the deck translations -/

lemma etaHu_add_one_right (u v : ℝ) : etaHu u (v + 1) = etaHu u v - 3 := by
  have hv1 : dZu u (v + 1) = (-(6 * π * I) * phaseV u v) • Zunit u v + phaseV u v • dZu u v := by
    rw [dZu]; simp only [Zunit_add_one_right]
    exact ((hasDerivAt_phaseV_u u v).smul (hasDerivAt_Zunit_u u v)).deriv.trans
      (by rw [dZu_eq]; abel)
  rw [etaHu, hv1, Zunit_add_one_right, etaExpr_smul (Zunit_unit u v) (norm_phaseV u v), ← etaHu]
  have : conj (phaseV u v) * (-(6 * π * I) * phaseV u v) = -(6 * π * I) := by
    rw [mul_left_comm, conj_mul_self_of_norm_one (norm_phaseV u v), mul_one]
  rw [this]
  simp only [neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_re]
  norm_num
  field_simp
  ring

lemma etaHv_add_one_right (u v : ℝ) : etaHv u (v + 1) = etaHv u v + 3 / 2 := by
  have hv1 : dZv u (v + 1) = ((3 * π * I) * phaseV u v) • Zunit u v + phaseV u v • dZv u v := by
    have h := ((hasDerivAt_phaseV_v u v).smul (hasDerivAt_Zunit_v u v))
    have h' : HasDerivAt (fun t => Zunit u (t + 1))
        (((3 * π * I) * phaseV u v) • Zunit u v + phaseV u v • dZv u v) v := by
      have e : (fun t => Zunit u (t + 1)) = fun t => phaseV u t • Zunit u t := by
        funext t; exact Zunit_add_one_right u t
      rw [e, dZv_eq]
      convert h using 1
      abel
    rw [dZv, ← deriv_comp_add_const]; exact h'.deriv
  rw [etaHv, hv1, Zunit_add_one_right, etaExpr_smul (Zunit_unit u v) (norm_phaseV u v), ← etaHv]
  have : conj (phaseV u v) * ((3 * π * I) * phaseV u v) = 3 * π * I := by
    rw [mul_left_comm, conj_mul_self_of_norm_one (norm_phaseV u v), mul_one]
  rw [this]
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_re]
  norm_num
  field_simp
  ring

lemma etaHu_add_one_left (u v : ℝ) : etaHu (u + 1) v = etaHu u v := by
  have hu2 : dZu (u + 1) v = (0 : ℂ) • Zunit u v + (-1 : ℂ) • dZu u v := by
    rw [zero_smul, zero_add]
    have h' : HasDerivAt (fun s => Zunit (s + 1) v) ((-1 : ℂ) • dZu u v) u := by
      have e : (fun s => Zunit (s + 1) v) = fun s => (-1 : ℂ) • Zunit s v := by
        funext s; exact Zunit_add_one_left s v
      rw [e, dZu_eq]
      exact (hasDerivAt_Zunit_u u v).const_smul (-1 : ℂ)
    rw [dZu, ← deriv_comp_add_const]; exact h'.deriv
  rw [etaHu, etaHu, hu2, Zunit_add_one_left, etaExpr_smul (Zunit_unit u v) (by simp)]
  simp

/-! ### The deck maps -/

/-- The fibre phase of the `v`-deck map: `c(u, v) = φ(u, v)³ = −exp(3iθ(u, v))`. -/
def cV (u v : ℝ) : ℂ := -cexp (((3 * phaseAng u v : ℝ) : ℂ) * I)

lemma cV_eq (u v : ℝ) : cV u v = phaseV u v ^ 3 := by
  rw [phaseV_eq, cV, neg_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf

lemma norm_cV (u v : ℝ) : ‖cV u v‖ = 1 := by
  rw [cV, norm_neg, Complex.norm_exp]; simp

lemma conj_mul_cV (u v : ℝ) : conj (cV u v) * cV u v = 1 := conj_mul_self_of_norm_one (norm_cV u v)

lemma cV_add_int_left (u v : ℝ) (k : ℤ) : cV (u + k) v = cV u v := by
  rw [cV_eq, cV_eq, phaseV_add_int_left]

lemma cV_re_im (u v : ℝ) : (cV u v).re ^ 2 + (cV u v).im ^ 2 = 1 := by
  have := norm_cV u v
  rw [← Complex.sq_norm_sub_sq_re] at *
  have h := Complex.sq_norm (cV u v)
  rw [this, Complex.normSq_apply] at h
  nlinarith [h]

/-- The `u`-deck map `(w, u, v) ↦ (−w, u + 1, v)`. -/
def TuE (X : E4) : E4 := mk (-wL X) (X 2 + 1) (X 3)
/-- Its inverse. -/
def TuInv (X : E4) : E4 := mk (-wL X) (X 2 - 1) (X 3)
/-- The `v`-deck map `(w, u, v) ↦ (φ(u, v)³ w, u, v + 1)`. -/
def TvE (X : E4) : E4 := mk (cV (X 2) (X 3) * wL X) (X 2) (X 3 + 1)
/-- Its inverse. -/
def TvInv (X : E4) : E4 := mk (conj (cV (X 2) (X 3 - 1)) * wL X) (X 2) (X 3 - 1)

/-- `c` as a function on `E4`, and its derivative `dc = c · i · (−18π du + 9π dv)`. -/
def cVE (X : E4) : ℂ := cV (X 2) (X 3)

def kV : E4 →L[ℝ] ℝ := (-(18 * π)) • dc 2 + (9 * π) • dc 3

lemma hasFDerivAt_cVE (X : E4) :
    HasFDerivAt cVE ((kV).smulRight (cVE X * I)) X := by
  have hθ : HasFDerivAt (fun Y : E4 => 3 * phaseAng (Y 2) (Y 3)) kV X := by
    have h : (fun Y : E4 => 3 * phaseAng (Y 2) (Y 3)) =
        fun Y => kV Y + 9 * π / 2 := by
      funext Y; simp only [phaseAng, kV, add_apply, smul_apply, smul_eq_mul]; rw [dc_apply,
        dc_apply]; ring
    rw [h]; exact kV.hasFDerivAt.add_const _
  have h1 : HasFDerivAt (fun Y : E4 => ((3 * phaseAng (Y 2) (Y 3) : ℝ) : ℂ) * I)
      ((ofRealCLM.comp kV).smulRight I) X := by
    have := (ofRealCLM.hasFDerivAt.comp X hθ).mul_const I
    refine this.congr_fderiv ?_
    ext v; simp [mul_comm]
  have h2 := (h1.cexp).neg
  unfold cVE cV
  convert h2 using 1
  ext v
  simp [Complex.real_smul]
  ring

lemma contDiff_cVE : ContDiff ℝ ∞ cVE := by
  have : cVE = fun Y : E4 => -cexp (((3 * phaseAng (Y 2) (Y 3) : ℝ) : ℂ) * I) := rfl
  rw [this]
  refine (Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp ?_).mul contDiff_const)).neg
  unfold phaseAng
  exact contDiff_const.mul ((contDiff_const.sub (contDiff_const.mul (dc 2).contDiff)).add
    (contDiff_const.mul (dc 3).contDiff))

lemma TvE_eq : TvE = fun X => mkL (cVE X * wL X, dc 2 X, dc 3 X + 1) := rfl

lemma contDiff_TvE : ContDiff ℝ ∞ TvE := by
  rw [TvE_eq]
  exact mkL.contDiff.comp ((contDiff_cVE.mul wL.contDiff).prodMk
    ((dc 2).contDiff.prodMk ((dc 3).contDiff.add contDiff_const)))

lemma contDiff_TvInv : ContDiff ℝ ∞ TvInv := by
  have : TvInv = fun X => mkL (conj (cVE (X - e 3)) * wL X, dc 2 X, dc 3 X - 1) := by
    funext X; simp [TvInv, cVE, mk]
  rw [this]
  have hc : ContDiff ℝ ∞ (fun X : E4 => conj (cVE (X - e 3))) :=
    (conjCLE.contDiff).comp (contDiff_cVE.comp (contDiff_id.sub contDiff_const))
  exact mkL.contDiff.comp ((hc.mul wL.contDiff).prodMk
    ((dc 2).contDiff.prodMk ((dc 3).contDiff.sub contDiff_const)))

lemma contDiff_TuE : ContDiff ℝ ∞ TuE := by
  have : TuE = fun X => mkL (-wL X, dc 2 X + 1, dc 3 X) := rfl
  rw [this]
  exact mkL.contDiff.comp (wL.contDiff.neg.prodMk
    (((dc 2).contDiff.add contDiff_const).prodMk (dc 3).contDiff))

lemma contDiff_TuInv : ContDiff ℝ ∞ TuInv := by
  have : TuInv = fun X => mkL (-wL X, dc 2 X - 1, dc 3 X) := rfl
  rw [this]
  exact mkL.contDiff.comp (wL.contDiff.neg.prodMk
    (((dc 2).contDiff.sub contDiff_const).prodMk (dc 3).contDiff))

lemma fderiv_TuE (X v : E4) : fderiv ℝ TuE X v = mk (-wL v) (v 2) (v 3) := by
  have : TuE = fun X => mkL (-wL X, dc 2 X + 1, dc 3 X) := rfl
  have h : HasFDerivAt TuE (mkL.comp ((-wL).prod ((dc 2).prod (dc 3)))) X := by
    rw [this]
    have h1 : HasFDerivAt (fun X : E4 => (-wL X, dc 2 X + 1, dc 3 X))
        ((-wL).prod ((dc 2).prod (dc 3))) X :=
      (-wL).hasFDerivAt.prodMk (((dc 2).hasFDerivAt.add_const 1).prodMk (dc 3).hasFDerivAt)
    exact mkL.hasFDerivAt.comp X h1
  rw [h.fderiv]; rfl

lemma fderiv_TvE (X v : E4) :
    fderiv ℝ TvE X v = mk (cVE X * wL v + kV v * (cVE X * I) * wL X) (v 2) (v 3) := by
  have h1 : HasFDerivAt (fun X : E4 => cVE X * wL X)
      (cVE X • wL + wL X • (kV.smulRight (cVE X * I))) X := by
    have := (hasFDerivAt_cVE X).mul wL.hasFDerivAt
    convert this using 1
  have h : HasFDerivAt TvE (mkL.comp ((cVE X • wL + wL X • (kV.smulRight (cVE X * I))).prod
      ((dc 2).prod (dc 3)))) X := by
    rw [TvE_eq]
    exact mkL.hasFDerivAt.comp X (h1.prodMk ((dc 2).hasFDerivAt.prodMk
      ((dc 3).hasFDerivAt.add_const 1)))
  rw [h.fderiv]
  simp only [comp_apply, prod_apply, add_apply, smul_apply, smulRight_apply, smul_eq_mul]
  rw [show mkL (_, dc 2 v, dc 3 v) = mk _ (v 2) (v 3) from rfl]
  congr 1
  rw [Complex.real_smul]; ring

/-- **The `u`-deck map** as a `DeckCore` (shift `(1, 0)`). -/
def deckU : DeckCore where
  T := TuE
  Tinv := TuInv
  smooth := contDiff_TuE
  smooth_inv := contDiff_TuInv
  left X := by simp [TuE, TuInv]
  right X := by simp [TuE, TuInv]
  m := 1
  n := 0
  shift2 X := by simp [TuE]
  shift3 X := by simp [TuE]
  pE_eq X := by simp [TuE, pE_eq]

/-- **The `v`-deck map** as a `DeckCore` (shift `(0, 1)`). -/
def deckV : DeckCore where
  T := TvE
  Tinv := TvInv
  smooth := contDiff_TvE
  smooth_inv := contDiff_TvInv
  left X := by
    simp only [TvE, TvInv, mk_apply2, mk_apply3, wL_mk, add_sub_cancel_right]
    rw [← mul_assoc, conj_mul_cV, one_mul, mk_wL]
  right X := by
    simp only [TvE, TvInv, mk_apply2, mk_apply3, wL_mk, sub_add_cancel]
    rw [← mul_assoc, mul_comm (cV _ _), conj_mul_cV, one_mul, mk_wL]
  m := 0
  n := 1
  shift2 X := by simp [TvE]
  shift3 X := by simp [TvE]
  pE_eq X := by simp [TvE, pE_eq, norm_cV]

/-! ### The primitive `β` of `Ω₀` under the deck maps -/

lemma betaLoc_apply (Y z : E4) : betaLoc Y z =
    (1 - 3 * pE Y) * etaHu (Y 2) (Y 3) * z 2 + (1 - 3 * pE Y) * etaHv (Y 2) (Y 3) * z 3 +
      1 / 2 * Y 0 * z 1 - 1 / 2 * Y 1 * z 0 := by
  simp only [betaLoc, fuC, fvC, add_apply, smul_apply, smul_eq_mul, dc_apply]; ring

lemma contDiff_betaLoc : ContDiff ℝ ∞ betaLoc := by
  have hu0 := Bundle.contDiff_etaHu
  have hv0 := Bundle.contDiff_etaHv
  have hu : ContDiff ℝ ∞ (fun X : E4 => etaHu (dc 2 X) (dc 3 X)) :=
    hu0.comp ((dc 2).contDiff.prodMk (dc 3).contDiff)
  have hv : ContDiff ℝ ∞ (fun X : E4 => etaHv (dc 2 X) (dc 3 X)) :=
    hv0.comp ((dc 2).contDiff.prodMk (dc 3).contDiff)
  have hp : ContDiff ℝ ∞ (fun X : E4 => 1 - 3 * pE X) := contDiff_const.sub
    (contDiff_const.mul contDiff_pE)
  have h1 : ContDiff ℝ ∞ (fun X : E4 => fuC (dc 2 X) (dc 3 X) (pE X) • dc 2) :=
    (hp.mul hu).smul contDiff_const
  have h2 : ContDiff ℝ ∞ (fun X : E4 => fvC (dc 2 X) (dc 3 X) (pE X) • dc 3) :=
    (hp.mul hv).smul contDiff_const
  have h3 : ContDiff ℝ ∞ (fun X : E4 => ((1 / 2 : ℝ) * dc 0 X) • dc 1) :=
    (contDiff_const.mul (dc 0).contDiff).smul contDiff_const
  have h4 : ContDiff ℝ ∞ (fun X : E4 => (-(1 / 2 : ℝ) * dc 1 X) • dc 0) :=
    (contDiff_const.mul (dc 1).contDiff).smul contDiff_const
  exact ((h1.add h2).add h3).add h4

/-- `Tu^* β = β`. -/
theorem pull1_TuE_betaLoc : pull1 TuE betaLoc = betaLoc := by
  funext X; ext v
  rw [Forms.pull1_apply, fderiv_TuE, betaLoc_apply, betaLoc_apply]
  have hp : pE (TuE X) = pE X := deckU.pE_eq X
  rw [hp]
  simp only [TuE, mk_apply0, mk_apply1, mk_apply2, mk_apply3, neg_re, neg_im, wL_re, wL_im,
    etaHu_add_one_left, Bundle.etaHv_add_one_left]
  ring

/-- `Tv^* β = β − 3 du + (3/2) dv`. -/
theorem pull1_TvE_betaLoc (X : E4) :
    pull1 TvE betaLoc X = betaLoc X + ((-3 : ℝ) • dc 2 + (3 / 2 : ℝ) • dc 3) := by
  ext v
  rw [Forms.pull1_apply, fderiv_TvE, add_apply, betaLoc_apply, betaLoc_apply]
  have hp : pE (TvE X) = pE X := deckV.pE_eq X
  rw [hp]
  have hn := cV_re_im (X 2) (X 3)
  have hpX : pE X = π * (X 0 ^ 2 + X 1 ^ 2) := by simp [pE]
  simp only [TvE, mk_apply0, mk_apply1, mk_apply2, mk_apply3, etaHu_add_one_right,
    etaHv_add_one_right, add_apply, smul_apply, smul_eq_mul, cVE, kV]
  simp only [mul_re, mul_im, add_re, add_im, wL_re, wL_im, I_re, I_im, ofReal_re, ofReal_im]
  simp only [dc_apply]
  rw [hpX]
  set cr := (cV (X 2) (X 3)).re
  set ci := (cV (X 2) (X 3)).im
  linear_combination (1 / 2 * (X 0 * v 1 - X 1 * v 0 +
    (-(18 * π) * v 2 + 9 * π * v 3) * (X 0 ^ 2 + X 1 ^ 2))) * hn

/-! ### Invariance of forms under the deck maps -/

open SymplecticPacking.Bundle (Omega0loc alpha1E alpha1 OmegaT AffineP sl Coef)

/-- If `T^*β = β + κ` with `κ` a constant covector, then `T^*(dβ) = dβ`. -/
theorem pull2_d1_of_pull1 {T : E4 → E4} (hT : ContDiff ℝ ∞ T) {β : Form1 E4}
    (hβ : ContDiff ℝ ∞ β) (κ : E4 →L[ℝ] ℝ) (h : ∀ X, pull1 T β X = β X + κ) (X : E4) :
    pull2 T (d1 β) X = d1 β X := by
  rw [← Forms.pull2_d1_apply (hT.contDiffAt.of_le (by simp))
    ((hβ.differentiable (by simp)) (T X))]
  have e : pull1 T β = (fun Y => β Y) + (fun _ => κ) := funext h
  rw [e, Forms.d1_add_apply ((hβ.differentiable (by simp)) X) (differentiableAt_const _),
    Bundle.d1_const]
  ext v w; simp

lemma Omega0loc_eq_d1 : Omega0loc = d1 betaLoc := funext fun X => (Return.d1_betaLoc X).symm

theorem pull2_Omega0loc_u (X : E4) : pull2 TuE Omega0loc X = Omega0loc X := by
  rw [Omega0loc_eq_d1]
  exact pull2_d1_of_pull1 contDiff_TuE contDiff_betaLoc 0 (fun X => by
    rw [pull1_TuE_betaLoc, add_zero]) X

theorem pull2_Omega0loc_v (X : E4) : pull2 TvE Omega0loc X = Omega0loc X := by
  rw [Omega0loc_eq_d1]
  exact pull2_d1_of_pull1 contDiff_TvE contDiff_betaLoc _ pull1_TvE_betaLoc X

/-- A horizontal one-form (only `du`, `dv` components) with `α(T X) = α(X)` is `T`-invariant. -/
lemma pull1_horizontal (T : DeckCore) {α : Form1 E4}
    (hα : ∀ Y v, α Y v = α Y (e 2) * v 2 + α Y (e 3) * v 3) {X : E4} (h : α (T.T X) = α X) :
    pull1 T.T α X = α X := by
  ext v
  rw [Forms.pull1_apply, hα, h, (T.dT_base X v).1, (T.dT_base X v).2, ← hα]

lemma contDiff_coef {f : Coef} (hf : AffineP f) (h0 : ContDiff ℝ ∞ (sl f 0))
    (h1 : ContDiff ℝ ∞ (sl f 1)) : ContDiff ℝ ∞ (fun X : E4 => f (dc 2 X) (dc 3 X) (pE X)) := by
  have e : (fun X : E4 => f (dc 2 X) (dc 3 X) (pE X)) = fun X =>
      sl f 0 (dc 2 X, dc 3 X) + pE X * (sl f 1 (dc 2 X, dc 3 X) - sl f 0 (dc 2 X, dc 3 X)) := by
    funext X; rw [hf]; rfl
  rw [e]
  have hp : ContDiff ℝ ∞ (fun X : E4 => (dc 2 X, dc 3 X)) := (dc 2).contDiff.prodMk (dc 3).contDiff
  exact (h0.comp hp).add (contDiff_pE.mul ((h1.comp hp).sub (h0.comp hp)))

/-- `Ω₀` is preserved by both deck maps. -/
lemma pull2_Omega0loc_deck (T : DeckCore) (hT : T = deckU ∨ T = deckV) (X : E4) :
    pull2 T.T Omega0loc X = Omega0loc X := by
  rcases hT with rfl | rfl
  · exact pull2_Omega0loc_u X
  · exact pull2_Omega0loc_v X

end SymplecticPacking.Handle
