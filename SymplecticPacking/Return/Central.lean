import SymplecticPacking.Bundle.OmegaT
import SymplecticPacking.Return.OmegaE

/-!
# The central identity in the coordinate model

`sec:rtc`, Proposition prop:rtc-central in the coordinate model: `ι^*(Ω_E|X₀) = Ω₀`.

Coordinates on `E4`: `(x, y, u, v)` = indices `(0, 1, 2, 3)` (as in `Bundle/OmegaT.lean`).
* `Ncoord (x, y, u, v) = (Zunit u v, x + i y)`: unit representatives of `N` in the frame `Zunit`.
* `pull1_injection_lamE`: on `{p < d_n}`, `(ι ∘ Ncoord)^* λ_E = (1 − 3p) Zunit^* η_H + ½(x dy − y dx)`
  (Lemma lem:rtc-dc together with `ι^*(d_n |W|²/(1+|W|²)) = p`).
* `d1_betaLoc`: `d((1 − 3p) η + ½(x dy − y dx)) = Ω₀` (`Omega0loc`), using `d(Zunit^* η_H) = σ`.
* `injection_pullback`: `pull2 (ι ∘ Ncoord) Ω_E = Omega0loc` on `{p < d_n}`.
-/

noncomputable section

namespace SymplecticPacking.Return

open _root_.Complex ComplexConjugate ContinuousLinearMap Filter Topology
open SymplecticPacking.Forms (Form1 Form2 d0 d1 pull1 pull2 pull1_apply pull2_d1_apply wedge
  wedge_apply)
open SymplecticPacking.Bundle (Zunit normSq3_Zunit etaHu etaHv sigmaC pE dpE aloc Omega0loc
  hasFDerivAt_pE hasFDerivAt_lift ZΦ D1 D2 diff_ZΦ etaHu_eq etaHv_eq sigFu sigFv
  hasDerivAt_etaHu_v hasDerivAt_etaHv_u sigmaC_eq' herm3_swap contDiff_etaHu contDiff_etaHv
  AffineP Coef pu pv pp sl)
open scoped Real ContDiff

/-! ### The coordinate model of `N` -/

/-- `w = x + i y` as a real-linear map `E4 → ℂ`. -/
def fibreCLM : E4 →L[ℝ] ℂ :=
  ofRealCLM.comp (Forms.dc 0) + (I • ofRealCLM).comp (Forms.dc 1)

lemma fibreCLM_apply (X : E4) : fibreCLM X = (X 0 : ℂ) + (X 1 : ℂ) * I := by
  simp [fibreCLM, mul_comm]

/-- Unit representatives of `N`: `(x, y, u, v) ↦ (Zunit u v, x + i y)`. -/
def Ncoord (X : E4) : C3 × ℂ := (Zunit (X 2) (X 3), (X 0 : ℂ) + (X 1 : ℂ) * I)

lemma nsq_Zunit (u v : ℝ) : nsq (Zunit u v) = 1 := by
  rw [nsq_eq_sum_norm]; exact normSq3_Zunit u v

lemma pN_fibre (X : E4) : pN ((X 0 : ℂ) + (X 1 : ℂ) * I) = pE X := by
  simp [pN, pE, Complex.normSq_apply]; ring

/-- The fibre factor `c = √π/√(d_n − p)`. -/
def cF (dn : ℝ) (X : E4) : ℝ := Real.sqrt π / Real.sqrt (dn - pE X)

/-- The composite `ι ∘ Ncoord` in explicit form. -/
def PhiN (dn : ℝ) (X : E4) : C3 × ℂ := (Zunit (X 2) (X 3), (cF dn X : ℂ) * fibreCLM X)

lemma injection_Ncoord (dn : ℝ) : (fun X => injection dn (Ncoord X)) = PhiN dn := by
  funext X
  simp only [injection, Ncoord, PhiN, injW, pN_fibre, cF, fibreCLM_apply]

/-! ### Derivatives -/

/-- `(u, v)` as a linear map. -/
def pr23 : E4 →L[ℝ] ℝ × ℝ := (Forms.dc 2).prod (Forms.dc 3)

lemma Zpart_eq : (fun Y : E4 => Zunit (Y 2) (Y 3)) = ZΦ ∘ pr23 := by
  funext Y; simp [pr23, ZΦ]

lemma hasFDerivAt_Zpart (X : E4) :
    HasFDerivAt (fun Y : E4 => Zunit (Y 2) (Y 3)) ((fderiv ℝ ZΦ (X 2, X 3)).comp pr23) X := by
  rw [Zpart_eq]
  have h : pr23 X = (X 2, X 3) := by simp [pr23]
  have := (diff_ZΦ (pr23 X)).hasFDerivAt.comp X pr23.hasFDerivAt
  rwa [h] at this

lemma contDiff_Zpart : ContDiff ℝ ∞ (fun Y : E4 => Zunit (Y 2) (Y 3)) := by
  rw [Zpart_eq]; exact Bundle.contDiff_ZΦ.comp pr23.contDiff

lemma fderivZ_pair (x : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ ZΦ x (a, b) = a • D1 x + b • D2 x := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul]; rfl

lemma contDiff_pE {n : WithTop ℕ∞} : ContDiff ℝ n pE := by
  unfold pE
  exact contDiff_const.mul (((Forms.dc 0).contDiff.pow 2).add ((Forms.dc 1).contDiff.pow 2))

lemma contDiffAt_cF {dn : ℝ} {X : E4} (hX : pE X < dn) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (cF dn) X := by
  have h1 : ContDiffAt ℝ n (fun Y => dn - pE Y) X := contDiffAt_const.sub contDiff_pE.contDiffAt
  have hpos : 0 < dn - pE X := by linarith
  exact contDiffAt_const.div (h1.sqrt hpos.ne') (Real.sqrt_pos.mpr hpos).ne'

lemma contDiffAt_PhiN {dn : ℝ} {X : E4} (hX : pE X < dn) :
    ContDiffAt ℝ 2 (PhiN dn) X := by
  have hW : ContDiffAt ℝ 2 (fun Y => (cF dn Y : ℂ) * fibreCLM Y) X :=
    (ofRealCLM.contDiff.contDiffAt.comp X (contDiffAt_cF hX)).mul fibreCLM.contDiff.contDiffAt
  exact ((contDiff_Zpart.of_le (by simp)).contDiffAt).prodMk hW

lemma fderiv_PhiN {dn : ℝ} {X : E4} (hX : pE X < dn) (w : E4) :
    fderiv ℝ (PhiN dn) X w =
      (w 2 • D1 (X 2, X 3) + w 3 • D2 (X 2, X 3),
        (cF dn X : ℂ) * fibreCLM w + fibreCLM X * (fderiv ℝ (cF dn) X w : ℂ)) := by
  have hc : DifferentiableAt ℝ (cF dn) X := (contDiffAt_cF hX (n := 1)).differentiableAt one_ne_zero
  have hW : HasFDerivAt (fun Y => (cF dn Y : ℂ) * fibreCLM Y)
      ((cF dn X : ℂ) • fibreCLM + fibreCLM X • ofRealCLM.comp (fderiv ℝ (cF dn) X)) X :=
    (ofRealCLM.hasFDerivAt.comp X hc.hasFDerivAt).mul fibreCLM.hasFDerivAt
  have h := (hasFDerivAt_Zpart X).prodMk hW
  rw [show PhiN dn = fun Y => (Zunit (Y 2) (Y 3), (cF dn Y : ℂ) * fibreCLM Y) from rfl, h.fderiv]
  simp only [prod_apply, comp_apply, add_apply, smul_apply, smul_eq_mul, ofRealCLM_apply]
  refine Prod.ext ?_ rfl
  simp only [pr23, prod_apply]
  rw [fderivZ_pair]
  simp

/-! ### The pulled-back primitive -/

/-- `(1 − 3p) η_u`. -/
def fuC : Coef := fun u v p => (1 - 3 * p) * etaHu u v
/-- `(1 − 3p) η_v`. -/
def fvC : Coef := fun u v p => (1 - 3 * p) * etaHv u v

/-- The primitive `β = (1 − 3p) Zunit^* η_H + ½ (x dy − y dx)` of `Ω₀`. -/
def betaLoc : Form1 E4 := fun X =>
  fuC (Forms.dc 2 X) (Forms.dc 3 X) (pE X) • Forms.dc 2 +
    fvC (Forms.dc 2 X) (Forms.dc 3 X) (pE X) • Forms.dc 3 +
    ((1 / 2 : ℝ) * Forms.dc 0 X) • Forms.dc 1 + (-(1 / 2 : ℝ) * Forms.dc 1 X) • Forms.dc 0

lemma herm_D_im (Z : C3) (a b : ℝ) (A B : C3) :
    (herm Z (a • A + b • B)).im = a * (herm Z A).im + b * (herm Z B).im := by
  simp only [herm, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Complex.real_smul, add_im, add_re, mul_im,
    mul_re, ofReal_re, ofReal_im, conj_re, conj_im]
  ring

/-- **Lemma lem:rtc-dc pulled back by `ι ∘ Ncoord`**: on `{p < d_n}`,
`(ι ∘ Ncoord)^* λ_E = (1 − 3p) Zunit^* η_H + ½ (x dy − y dx)`. -/
theorem pull1_injection_lamE {dn : ℝ} {X : E4} (hX : pE X < dn) :
    pull1 (fun Y => injection dn (Ncoord Y)) (lamE dn) X = betaLoc X := by
  rw [injection_Ncoord]
  ext w
  rw [pull1_apply, fderiv_PhiN hX, PhiN, dc_log_one_add dn (nsq_Zunit _ _)]
  simp only [betaLoc, fuC, fvC, add_apply, smul_apply, smul_eq_mul, PiLp.proj_apply]
  have hp0 : 0 ≤ pE X := by unfold pE; positivity
  have hd : 0 < dn - pE X := by linarith
  have hdn : 0 < dn := by linarith
  set c := cF dn X with hc_def
  set r := fderiv ℝ (cF dn) X w
  have hc2 : c ^ 2 = π / (dn - pE X) := by
    rw [hc_def, cF, div_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hd.le]
  have hU : normSq (fibreCLM X) = pE X / π := by
    rw [fibreCLM_apply, ← pN_fibre, pN]; field_simp
  have hW : normSq ((c : ℂ) * fibreCLM X) = c ^ 2 * (pE X / π) := by
    rw [normSq_mul, normSq_ofReal, hU]; ring
  have hIm : (conj ((c : ℂ) * fibreCLM X) * ((c : ℂ) * fibreCLM w + fibreCLM X * (r : ℂ))).im =
      c ^ 2 * (X 0 * w 1 - X 1 * w 0) := by
    simp only [fibreCLM_apply, map_mul, map_add, conj_ofReal, mul_im, mul_re, add_re, add_im,
      ofReal_re, ofReal_im, conj_re, conj_im, I_re, I_im]
    ring
  rw [hW, hIm, etaH, herm_D_im, etaHu_eq, etaHv_eq]
  have e1 : (herm (Zunit (X 2) (X 3)) (D1 (X 2, X 3))).im =
      (Bundle.herm3 (ZΦ (X 2, X 3)) (D1 (X 2, X 3))).im := rfl
  have e2 : (herm (Zunit (X 2) (X 3)) (D2 (X 2, X 3))).im =
      (Bundle.herm3 (ZΦ (X 2, X 3)) (D2 (X 2, X 3))).im := rfl
  rw [e1, e2, hc2]
  generalize (Bundle.herm3 (ZΦ (X 2, X 3)) (D1 (X 2, X 3))).im = A
  generalize (Bundle.herm3 (ZΦ (X 2, X 3)) (D2 (X 2, X 3))).im = B
  have hπ := Real.pi_pos
  field_simp
  ring

/-! ### `dβ = Ω₀` -/

lemma fuC_affine : AffineP fuC :=
  AffineP.of_eq (fun u v => etaHu u v) (fun u v => -3 * etaHu u v) fun u v p => by
    simp only [fuC]; ring

lemma fvC_affine : AffineP fvC :=
  AffineP.of_eq (fun u v => etaHv u v) (fun u v => -3 * etaHv u v) fun u v p => by
    simp only [fvC]; ring

lemma contDiff_sl_fuC (p : ℝ) : ContDiff ℝ ∞ (sl fuC p) :=
  contDiff_const.mul contDiff_etaHu

lemma contDiff_sl_fvC (p : ℝ) : ContDiff ℝ ∞ (sl fvC p) :=
  contDiff_const.mul contDiff_etaHv

lemma pv_fuC (u v p : ℝ) : pv fuC u v p = (1 - 3 * p) * sigFu u v :=
  ((hasDerivAt_etaHu_v u v).const_mul (1 - 3 * p)).deriv

lemma pu_fvC (u v p : ℝ) : pu fvC u v p = (1 - 3 * p) * sigFv u v :=
  ((hasDerivAt_etaHv_u u v).const_mul (1 - 3 * p)).deriv

lemma hasDerivAt_affine_p (a p : ℝ) : HasDerivAt (fun q : ℝ => (1 - 3 * q) * a) (-3 * a) p := by
  simpa using (((hasDerivAt_id p).const_mul 3).const_sub 1).mul_const a

lemma pp_fuC (u v p : ℝ) : pp fuC u v p = -3 * etaHu u v := (hasDerivAt_affine_p _ p).deriv

lemma pp_fvC (u v p : ℝ) : pp fvC u v p = -3 * etaHv u v := (hasDerivAt_affine_p _ p).deriv

lemma sigFv_sub_sigFu (u v : ℝ) : sigFv u v - sigFu u v = sigmaC u v := by
  rw [sigmaC_eq', sigFv, sigFu, herm3_swap (D1 (u, v))]
  simp only [add_im, conj_im]
  field_simp
  ring

lemma hasFDerivAt_half (i : Fin 4) (a : ℝ) (X : E4) :
    HasFDerivAt (fun Y : E4 => a * Forms.dc i Y) (a • Forms.dc i) X :=
  ((Forms.dc i).hasFDerivAt).const_mul a

/-- `dβ = Ω₀`. -/
theorem d1_betaLoc (X : E4) : d1 betaLoc X = Omega0loc X := by
  have hA := hasFDerivAt_lift fuC_affine (contDiff_sl_fuC 0) (contDiff_sl_fuC 1) X
  have hB := hasFDerivAt_lift fvC_affine (contDiff_sl_fvC 0) (contDiff_sl_fvC 1) X
  have hC := hasFDerivAt_half 0 (1 / 2) X
  have hD := hasFDerivAt_half 1 (-(1 / 2)) X
  have e : betaLoc =
      (fun Y => fuC (Forms.dc 2 Y) (Forms.dc 3 Y) (pE Y) • (fun _ => Forms.dc 2) Y) +
      (fun Y => fvC (Forms.dc 2 Y) (Forms.dc 3 Y) (pE Y) • (fun _ => Forms.dc 3) Y) +
      (fun Y => ((1 / 2 : ℝ) * Forms.dc 0 Y) • (fun _ => Forms.dc 1) Y) +
      (fun Y => (-(1 / 2 : ℝ) * Forms.dc 1 Y) • (fun _ => Forms.dc 0) Y) := rfl
  have dA := hA.differentiableAt.smul_const (Forms.dc 2)
  have dB := hB.differentiableAt.smul_const (Forms.dc 3)
  have dC := hC.differentiableAt.smul_const (Forms.dc 1)
  have dD := hD.differentiableAt.smul_const (Forms.dc 0)
  rw [e, Forms.d1_add_apply ((dA.add dB).add dC) dD, Forms.d1_add_apply (dA.add dB) dC,
    Forms.d1_add_apply dA dB,
    Forms.d1_mul_apply hA.differentiableAt (differentiableAt_const _),
    Forms.d1_mul_apply hB.differentiableAt (differentiableAt_const _),
    Forms.d1_mul_apply hC.differentiableAt (differentiableAt_const _),
    Forms.d1_mul_apply hD.differentiableAt (differentiableAt_const _),
    Bundle.d1_const, Bundle.d1_const, Bundle.d1_const, Bundle.d1_const]
  simp only [d0, hA.fderiv, hB.fderiv, hC.fderiv, hD.fderiv, pv_fuC, pu_fvC, pp_fuC, pp_fvC]
  have hs := sigFv_sub_sigFu (Forms.dc 2 X) (Forms.dc 3 X)
  ext v w
  simp only [Omega0loc, aloc, dpE, add_apply, smul_apply, wedge_apply, smul_eq_mul,
    zero_apply, mul_zero, add_zero]
  rw [← hs]
  ring

/-! ### Proposition prop:rtc-central -/

/-- **Proposition prop:rtc-central** (coordinate model): on `{p < d_n}`,
`(ι ∘ Ncoord)^* Ω_E = Ω₀ = ω_V + (1 − 3p)σ + dp ∧ a_loc`. -/
theorem injection_pullback {dn : ℝ} {X : E4} (hX : pE X < dn) :
    pull2 (fun Y => injection dn (Ncoord Y)) (OmegaE dn) X = Omega0loc X := by
  have hΦ : ContDiffAt ℝ 2 (fun Y => injection dn (Ncoord Y)) X := by
    rw [injection_Ncoord]; exact contDiffAt_PhiN hX
  have hx : 0 < nsq (injection dn (Ncoord X)).1 := by
    simp [injection, Ncoord, nsq_Zunit]
  rw [OmegaE, ← pull2_d1_apply hΦ (differentiableAt_lamE dn hx), ← d1_betaLoc]
  have hev : pull1 (fun Y => injection dn (Ncoord Y)) (lamE dn) =ᶠ[𝓝 X] betaLoc := by
    have hcont : ContinuousAt pE X := (hasFDerivAt_pE X).continuousAt
    filter_upwards [hcont.eventually_lt continuousAt_const hX] with Y hY
    exact pull1_injection_lamE hY
  have h := hev.fderiv_eq (𝕜 := ℝ)
  simp only [Forms.d1, h]

end SymplecticPacking.Return
