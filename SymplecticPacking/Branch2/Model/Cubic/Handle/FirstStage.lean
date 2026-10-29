import SymplecticPacking.Handle.FirstStage
import SymplecticPacking.Branch2.Model.Cubic.Handle.Frame
import SymplecticPacking.Branch2.Model.Cubic.Handle.Enlarged

/-!
# The first stage of the handle

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`cons:shd4-eta`, `lem:shd4-eta`, `prop:shd4-second`) and fact (F1):
the first stage `Ω^{(1)}_λ = Ω₁ + dη_λ`.

Local forms (coordinates `(x, y, s, t)` of the `𝒜⁺`-frame, `Handle/Twist.lean`):
* `gsmE P = γ_sm = e_h (s − 1/6) dt`, `fHbE P = f(s) H*(p) β`, `GbE G = G(s, w) β`, `β = b(t) dt`;
* `Omega1Loc P = ω_V + d(γ_sm + f H*(p) β)`; `OmegaT_one_frameA` is (F1):
  `chartA^* Ω₁ = Omega1Loc P` over `𝒜`;
* `OmegaPreG P G = dγ_sm + ω_V + d(G β)`; `OmegaPreG_split` (`prop:shd4-second`): it is the
  split form `ω_V + (e_h + b ∂_sG) ν + b d_wG ∧ dt`, and `OmegaPreG_nondeg`: it is
  nondegenerate where `∂_s G ≥ 0`.
* `etaLoc P λ = (Q^λ_s ∘ q_{λ f(s)}) ds + f(s)[H*(p(q_λ⁻¹ q_{λ f(s)} w)) − H*(p(w))] β`.

Global forms (the `Zunit`-frame coordinates of `Bundle/OmegaT.lean`):
* `eta P λ` is the zero extension of `etaLoc P λ` from `𝒜` (transported by `chartInv`);
* `firstStage P λ = Ω₁ + dη_λ` with `Ω₁ = OmegaT P 1`.

Results: `eta_support`, `eta_eventually_zero`, `eta_smooth` (jointly in `(λ, X)`), `eta_zero`,
`eta_horizontal`, `firstStage_eq_loc`, `firstStage_eq` (lem:shd4-eta),
`firstStage_nondeg` (nondegeneracy on `{p < h + 2δ_m}`, `λ ∈ [0, 1]`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus lambdaCu lambdaCv pp contDiff_stepA contDiff_bB contDiff_deriv_stepA)
open SymplecticPacking.Bundle.Cubic (kappaT kappa1 alpha1 OmegaT OmegaT_split)
open SymplecticPacking.Qhat.Cubic (qhatP qhatInvP QhamP Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

attribute [local irreducible] Bundle.frameA Bundle.Zunit lambdaCu lambdaCv Bundle.etaHu
  Bundle.etaHv Bundle.sigmaC

variable (P : Branch2.VCubic)

/-! ### Generic helpers -/

/-- Bound used for positivity: twisting keeps `H*` nonnegative on `{p < h + 2δ_m}`. -/
lemma Hstar_twist_nonneg {w : ℂ} (hw : π * ‖w‖ ^ 2 < P.h + 2 * deltam P) (τ τ' : ℝ) :
    0 ≤ P.Hstar (π * ‖qhatInvP P τ (qhatP P τ' w)‖ ^ 2) := by
  rcases le_or_gt (π * ‖w‖ ^ 2) P.h with h | h
  · have h1 := qhatP_mem_closedDisk P (Psupp_lt_h P).le τ' h
    have h2 := qhatInvP_mem_closedDisk P (Psupp_lt_h P).le τ h1
    have := P.Hstar_ge h2; linarith [P.g_pos]
  · have hs : Psupp P < π * ‖w‖ ^ 2 := (Psupp_lt_h P).trans h
    rw [qhatP_collar P hs, qhatInvP_collar P hs]
    exact (Hstar_pos_of P hw).le

lemma twist_bound {w : ℂ} (hw : π * ‖w‖ ^ 2 < P.h + 2 * deltam P) (τ : ℝ) :
    π * ‖qhatP P τ w‖ ^ 2 < P.h + 2 * deltam P := by
  rcases le_or_gt (π * ‖w‖ ^ 2) P.h with h | h
  · have := qhatP_mem_closedDisk P (Psupp_lt_h P).le τ h; linarith [deltam_pos P]
  · rw [qhatP_collar P ((Psupp_lt_h P).trans h)]; exact hw

/-! ### Local forms -/

/-- `γ_sm = e_h (s − 1/6) dt` (`Bundle.Cubic.gammaSm`). -/
def gsmE : Form1 E4 := fun X => (P.eh * (X 2 - 1 / 6)) • dc 3

/-- `f(s) H*(p) β`. -/
def fHbE : Form1 E4 := fun X => (stepA (X 2) * P.Hstar (pE X) * bB (X 3)) • dc 3

/-- **Fact (F1)**: `Ω₁ = ω_V + d(γ_sm + f(s) H*(p) β)` in the `𝒜⁺`-frame. -/
def Omega1Loc : Form2 E4 := fun X => omegaV X + d1 (fun Y => gsmE P Y + fHbE P Y) X

/-- `dγ_sm + ω_V + d(G β)`; `Ω_pre = OmegaPreG P G_f` (`prop:shd4-third`). -/
def OmegaPreG (G : ℝ → ℂ → ℝ) : Form2 E4 := fun X => d1 (gsmE P) X + omegaV X + d1 (GbE G) X

lemma hasFDerivAt_gsm_coef (X : E4) :
    HasFDerivAt (fun Y : E4 => P.eh * (Y 2 - 1 / 6)) (P.eh • dc 2) X := by
  have := ((dc 2).hasFDerivAt (x := X)).sub_const (1 / 6 : ℝ) |>.const_mul P.eh
  exact this

lemma d1_gsmE (X : E4) : d1 (gsmE P) X = P.eh • wedge (dc 2) (dc 3) := by
  have h := d1_smul_const_form (L := dc 3) (hasFDerivAt_gsm_coef P X).differentiableAt
  rw [show gsmE P = fun Y => (P.eh * (Y 2 - 1 / 6)) • dc 3 from rfl, h,
    (hasFDerivAt_gsm_coef P X).fderiv]
  ext v w; simp [wedge_apply]; ring

/-- The coefficient of `γ_sm + f H* β`. -/
def c1coef (X : E4) : ℝ := P.eh * (X 2 - 1 / 6) + stepA (X 2) * P.Hstar (pE X) * bB (X 3)

lemma hasFDerivAt_Hstar_pE (X : E4) :
    HasFDerivAt (fun Y => P.Hstar (pE Y)) ((-9 : ℝ) • dpE X) X := by
  have h := ((Bundle.hasFDerivAt_pE X).const_mul (-9 : ℝ)).const_add (3 - P.eh)
  refine (h.congr_fderiv rfl).congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
  simp only [Branch2.CubicData.Hstar, Branch2.CubicData.Hb]; ring

lemma hasFDerivAt_c1coef (X : E4) : HasFDerivAt (c1coef P)
    ((P.eh + deriv stepA (X 2) * P.Hstar (pE X) * bB (X 3)) • dc 2 +
      (stepA (X 2) * (-9) * bB (X 3)) • dpE X +
      (stepA (X 2) * P.Hstar (pE X) * deriv bB (X 3)) • dc 3) X := by
  have hf : HasFDerivAt (fun Y : E4 => stepA (Y 2)) (deriv stepA (X 2) • dc 2) X :=
    ((contDiff_stepA.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt X (dc 2).hasFDerivAt
  have hb : HasFDerivAt (fun Y : E4 => bB (Y 3)) (deriv bB (X 3) • dc 3) X :=
    ((contDiff_bB.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt X (dc 3).hasFDerivAt
  have h := (hasFDerivAt_gsm_coef P X).add ((hf.mul (hasFDerivAt_Hstar_pE P X)).mul hb)
  refine h.congr_fderiv ?_
  ext v; simp [smul_eq_mul]; ring

/-- `Omega1Loc` is the split form `ω_V + (e_h + f' H* b) ν + dp ∧ (−9 f b dt)`. -/
theorem Omega1Loc_split (X : E4) : Omega1Loc P X = splitForm (2 * π * X 0) (2 * π * X 1) 0
    (-9 * stepA (X 2) * bB (X 3)) (P.eh + P.Hstar (pE X) * (deriv stepA (X 2) * bB (X 3))) := by
  have e : (fun Y => gsmE P Y + fHbE P Y) = fun Y => c1coef P Y • dc 3 := by
    funext Y; simp only [gsmE, fHbE, c1coef, add_smul]
  rw [Omega1Loc, e, d1_smul_const_form (hasFDerivAt_c1coef P X).differentiableAt,
    (hasFDerivAt_c1coef P X).fderiv]
  ext v w
  simp [omegaV, splitForm, wedge_apply, dpE, dc_apply, smul_eq_mul]
  ring

/-- `α₁` over `𝒜` is affine in `p` with explicit coefficients (from `Bundle.Cubic.alpha1_annulus`). -/
lemma alpha1_cu_annulus {u : ℝ} (hu : u ∈ annulus) (v q : ℝ) :
    (alpha1 P).cu u v q = -lambdaCu u v + 3 * lambdaCu u v * q := by
  have h := (Bundle.Cubic.alpha1_annulus P hu v q).1
  simp only [Bundle.Cubic.Gamma1, Bundle.BForm.add_cu, Pi.add_apply, Bundle.BForm.pmul, Bundle.aA,
    Bundle.lambdaC, Bundle.ofUV, Bundle.Cubic.gammaSm, Bundle.Cubic.fHbeta] at h
  linarith

lemma alpha1_cv_annulus {u : ℝ} (hu : u ∈ annulus) (v q : ℝ) :
    (alpha1 P).cv u v q = P.eh * (u - 1 / 6) + stepA u * (3 - P.eh) * bB v - lambdaCv u v +
      (3 * lambdaCv u v - 9 * stepA u * bB v) * q := by
  have h := (Bundle.Cubic.alpha1_annulus P hu v q).2
  simp only [Bundle.Cubic.Gamma1, Bundle.BForm.add_cv, Pi.add_apply, Bundle.BForm.pmul, Bundle.aA,
    Bundle.lambdaC, Bundle.ofUV, Bundle.Cubic.gammaSm, Bundle.Cubic.fHbeta, Branch2.CubicData.Hstar, Branch2.CubicData.Hb] at h
  linarith

/-- **Fact (F1)** (`lem:fer-alpha1`, identity (2)): over `𝒜`, in the `𝒜⁺`-frame,
`Ω₁ = ω_V + d(γ_sm + f(s) H*(p) β)`. -/
theorem OmegaT_one_frameA {X : E4} (hX : X 2 ∈ annulus) :
    pull2 chartA (OmegaT P 1) X = Omega1Loc P X := by
  have hb : X ∈ bandE := annulus_subset_annulusPlus hX
  rw [OmegaT_frameA P 1 hb, Omega1Loc_split,
    pp_affine (fun q => alpha1_cu_annulus P hX (X 3) q),
    pp_affine (fun q => alpha1_cv_annulus P hX (X 3) q)]
  simp only [kappaT, kappa1, Bundle.chiA_band (annulus_subset_annulusPlus hX)]
  congr 1 <;> ring

/-! ### The square of a twisted form (`prop:shd4-second`) -/

/-- The twisted pre-form is a split form: `dγ_sm + ω_V + d(Gβ) = ω_V + (e_h + b ∂_sG) ν +
b d_wG ∧ dt`. -/
theorem OmegaPreG_split {G : ℝ → ℂ → ℝ} {X : E4}
    (hG : DifferentiableAt ℝ (fun z : ℝ × ℂ => G z.1 z.2) (X 2, wL X)) :
    OmegaPreG P G X = splitForm (bB (X 3) * fderiv ℝ (fun y => G (X 2) y) (wL X) 1)
      (bB (X 3) * fderiv ℝ (fun y => G (X 2) y) (wL X) Complex.I) 0 1
      (P.eh + bB (X 3) * deriv (fun σ => G σ (wL X)) (X 2)) := by
  have hc := hasFDerivAt_GbE_coef hG
  have hd : d1 (GbE G) X = wedge (bB (X 3) • (fderiv ℝ (fun z : ℝ × ℂ => G z.1 z.2)
      (X 2, wL X)).comp ((dc 2).prod wL) + G (X 2) (wL X) • (deriv bB (X 3) • dc 3)) (dc 3) := by
    rw [show GbE G = fun Y => (G (Y 2) (wL Y) * bB (Y 3)) • dc 3 from rfl,
      d1_smul_const_form hc.differentiableAt, hc.fderiv]
  have hlin : ∀ v : E4, fderiv ℝ (fun z : ℝ × ℂ => G z.1 z.2) (X 2, wL X) (v 2, wL v) =
      v 2 * deriv (fun σ => G σ (wL X)) (X 2) +
        (v 0 * fderiv ℝ (fun y => G (X 2) y) (wL X) 1 +
          v 1 * fderiv ℝ (fun y => G (X 2) y) (wL X) Complex.I) := by
    intro v
    rw [fderiv_prod_apply hG, wL_decomp v, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
  ext v w
  simp only [OmegaPreG, add_apply, d1_gsmE, hd, omegaV_apply, wedge_apply, smul_apply,
    comp_apply, prod_apply, smul_eq_mul, dc_apply, hlin, splitForm, zero_smul, one_smul,
    zero_add]
  simp only [Qhat.omega2, wL_re, wL_im]
  ring

/-- Nondegeneracy of the twisted pre-form where `∂_s G ≥ 0`. -/
theorem OmegaPreG_nondeg {G : ℝ → ℂ → ℝ} {X : E4}
    (hG : DifferentiableAt ℝ (fun z : ℝ × ℂ => G z.1 z.2) (X 2, wL X))
    (hmono : 0 ≤ deriv (fun σ => G σ (wL X)) (X 2)) :
    ∀ v, (∀ w, OmegaPreG P G X v w = 0) → v = 0 := by
  rw [OmegaPreG_split P hG]
  refine Forms.splitForm_nondeg (ne_of_gt ?_)
  have := mul_nonneg (Bundle.bB_nonneg (X 3)) hmono
  have : 0 < P.eh := (Bundle.Cubic.kappa_pos P).2.2
  linarith

/-! ### The first-stage primitive (`cons:shd4-eta`) -/

/-- The `β`-coefficient of `η_λ`: `f(s)[H*(p(q_λ⁻¹ q_{λ f(s)} w)) − H*(p(w))] b(t)`. -/
def etaCoef (lam : ℝ) (X : E4) : ℝ :=
  stepA (X 2) * (P.Hstar (π * ‖qhatInvP P lam (qhatP P (lam * stepA (X 2)) (wL X))‖ ^ 2) -
    P.Hstar (pE X)) * bB (X 3)

/-- **The first-stage primitive on `𝒜 × ℂ`** (`cons:shd4-eta`):
`η_λ = (Q^λ_s ∘ q_{λ f(s)}) ds + f(s)[H*(p(q_λ⁻¹ q_{λ f(s)} w)) − H*(p(w))] β`. -/
def etaLoc (lam : ℝ) : Form1 E4 := fun X => PhiS P lam X • dc 2 + etaCoef P lam X • dc 3

open Classical in
/-- **The first-stage primitive on `N`**: the zero extension of `η_λ` from `𝒜`, in the global
`Zunit`-frame (the local form is transported by `chartInv`; it has only base components). -/
def eta (lam : ℝ) : Form1 E4 := fun X =>
  if X 2 ∈ annulus then etaLoc P lam (chartInv X) else 0

/-- **The first stage** `Ω^{(1)}_λ = Ω₁ + dη_λ` (`cons:shd4-eta`). -/
def firstStage (lam : ℝ) : Form2 E4 := fun X => OmegaT P 1 X + d1 (eta P lam) X

theorem contDiff_etaCoef_joint : ContDiff ℝ ∞ (fun z : ℝ × E4 => etaCoef P z.1 z.2) := by
  have e : (fun z : ℝ × E4 => etaCoef P z.1 z.2) = fun z => stepA (z.2 2) *
      (P.Hstar (π * ‖qqInv P (z.1, qq P (z.1 * stepA (z.2 2), wL z.2))‖ ^ 2) -
        P.Hstar (pE z.2)) * bB (z.2 3) := rfl
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × E4 => z.1 * stepA (z.2 2)) :=
    contDiff_fst.mul (contDiff_stepA.comp ((dc 2).contDiff.comp contDiff_snd))
  have h2 : ContDiff ℝ ∞ (fun z : ℝ × E4 => qq P (z.1 * stepA (z.2 2), wL z.2)) :=
    (contDiff_qq P).comp (h1.prodMk (wL.contDiff.comp contDiff_snd))
  have h3 : ContDiff ℝ ∞ (fun z : ℝ × E4 => qqInv P (z.1, qq P (z.1 * stepA (z.2 2), wL z.2))) :=
    (contDiff_qqInv P).comp (contDiff_fst.prodMk h2)
  rw [e]
  exact ((contDiff_stepA.comp ((dc 2).contDiff.comp contDiff_snd)).mul
    (((contDiff_Hstar P).comp (contDiff_fibreArea.comp h3)).sub
      ((contDiff_Hstar P).comp (contDiff_pE.comp contDiff_snd)))).mul
    (contDiff_bB.comp ((dc 3).contDiff.comp contDiff_snd))

theorem contDiff_etaLoc_joint : ContDiff ℝ ∞ (fun z : ℝ × E4 => etaLoc P z.1 z.2) :=
  (contDiff_smul_dc_joint (contDiff_PhiS_joint P) 2).add
    (contDiff_smul_dc_joint (contDiff_etaCoef_joint P) 3)

theorem contDiff_etaLoc (lam : ℝ) : ContDiff ℝ ∞ (etaLoc P lam) := by
  have h : ContDiff ℝ ∞ (fun X => etaLoc P (lam, X).1 (lam, X).2) :=
    (contDiff_etaLoc_joint P).comp (contDiff_const.prodMk contDiff_id)
  exact h

/-- `η_λ` vanishes over the collars `s ≤ u₀` and `s ≥ u₁` (`lem:shd4-eta`, support). -/
theorem etaLoc_eq_zero_of_s (lam : ℝ) {X : E4} (hX : X 2 ≤ u0 ∨ u1 ≤ X 2) :
    etaLoc P lam X = 0 := by
  have hd : deriv stepA (X 2) = 0 := Bundle.deriv_stepA_eq_zero fun h => by
    rcases hX with hX | hX
    · exact absurd h.1 (not_lt.mpr hX)
    · exact absurd h.2 (not_lt.mpr hX)
  have hPhi : PhiS P lam X = 0 := by simp [PhiS, Qs, hd]
  have hc : etaCoef P lam X = 0 := by
    rcases hX with hX | hX
    · simp [etaCoef, Bundle.stepA_eq_zero hX]
    · rw [etaCoef, Bundle.stepA_eq_one hX, mul_one, qhatInvP_qhatP, ← pE_eq, sub_self, mul_zero,
        zero_mul]
  simp [etaLoc, hPhi, hc]

/-- `η_λ` vanishes on `{p > P_supp}` (`lem:shd4-eta`, support). -/
theorem etaLoc_eq_zero_of_p (lam : ℝ) {X : E4} (hX : Psupp P < pE X) : etaLoc P lam X = 0 := by
  rw [pE_eq] at hX
  have hq : qhatP P (lam * stepA (X 2)) (wL X) = wL X := qhatP_collar P hX
  have hPhi : PhiS P lam X = 0 := by
    simp only [PhiS, Qs, hq, QhamP_collar P hX, mul_zero]
  have hc : etaCoef P lam X = 0 := by
    rw [etaCoef, hq, qhatInvP_collar P hX, ← pE_eq, sub_self, mul_zero, zero_mul]
  simp [etaLoc, hPhi, hc]

/-- `η₀ = 0`. -/
theorem etaLoc_zero : etaLoc P 0 = 0 := by
  funext X
  have hPhi : PhiS P 0 X = 0 := by simp [PhiS, Qs]
  have hc : etaCoef P 0 X = 0 := by
    rw [etaCoef, zero_mul, qhatInvP_qhatP, ← pE_eq, sub_self, mul_zero, zero_mul]
  simp [etaLoc, hPhi, hc]

lemma eta_eq_zero_of_s (lam : ℝ) {X : E4} (hX : X 2 ≤ u0 ∨ u1 ≤ X 2) : eta P lam X = 0 := by
  unfold eta
  split_ifs with h
  · exact etaLoc_eq_zero_of_s P lam (by simpa using hX)
  · rfl

/-- **`η_λ` vanishes near every point outside `[u₀, u₁] × ℝ × D̄(P_supp)`**. -/
theorem eta_eventually_zero (lam : ℝ) {X : E4} (hX : X 2 ∉ Icc u0 u1 ∨ Psupp P < pE X) :
    eta P lam =ᶠ[𝓝 X] fun _ => 0 := by
  rcases hX with hX | hX
  · have hX' : X 2 < u0 ∨ u1 < X 2 := by
      simp only [mem_Icc, not_and_or, not_le] at hX; exact hX
    filter_upwards [isOpen_collarE.mem_nhds hX'] with Y hY
    exact eta_eq_zero_of_s P lam (hY.imp le_of_lt le_of_lt)
  · filter_upwards [(isOpen_lt continuous_const contDiff_pE.continuous).mem_nhds hX] with Y hY
    unfold eta
    split_ifs with h
    · exact etaLoc_eq_zero_of_p P lam (by
        rw [pE_chartInv (annulus_subset_annulusPlus h)]; exact hY)
    · rfl

/-- **Support of `η_λ`** (`lem:shd4-eta`): `supp η_λ ⊆ [u₀, u₁] × ℝ × D̄(P_supp)`. -/
theorem eta_support (lam : ℝ) {X : E4} (hX : eta P lam X ≠ 0) :
    X 2 ∈ Icc u0 u1 ∧ pE X ≤ Psupp P := by
  by_contra h
  rw [not_and_or, not_le] at h
  exact hX ((eta_eventually_zero P lam h).self_of_nhds)

/-- **`η_λ` is a smooth one-form on `N`, smooth in `λ`** (`lem:shd4-eta`). -/
theorem eta_smooth : ContDiff ℝ ∞ (fun z : ℝ × E4 => eta P z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨lam, X⟩
  by_cases hX : X 2 ∈ annulus
  · have hev : (fun z : ℝ × E4 => eta P z.1 z.2) =ᶠ[𝓝 (lam, X)]
        fun z => etaLoc P z.1 (chartInv z.2) := by
      filter_upwards [(isOpen_annulusE.preimage continuous_snd).mem_nhds hX] with z hz
      have hz' : z.2 2 ∈ annulus := hz
      rw [eta, if_pos hz']
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h2 : ContDiffAt ℝ ∞ (fun z : ℝ × E4 => chartInv z.2) (lam, X) :=
      ContDiffAt.comp (g := chartInv) (f := Prod.snd) (lam, X)
        (contDiffAt_chartInv (annulus_subset_annulusPlus hX)) contDiffAt_snd
    have hin : ContDiffAt ℝ ∞ (fun z : ℝ × E4 => (z.1, chartInv z.2)) (lam, X) :=
      contDiffAt_fst.prodMk h2
    have hc : ContDiffAt ℝ ∞ (fun z : ℝ × E4 => etaLoc P z.1 z.2) (lam, chartInv X) :=
      (contDiff_etaLoc_joint P).contDiffAt
    exact hc.comp (lam, X) hin
  · have hX' : X 2 < u0 ∨ u1 < X 2 := by
      simp only [annulus, mem_Ioo, not_and_or, not_lt] at hX
      rcases hX with h | h
      · left; linarith [show (1 / 8 : ℝ) < u0 by norm_num [u0]]
      · right; linarith [show u1 < (5 / 24 : ℝ) by norm_num [u1]]
    have hev : (fun z : ℝ × E4 => eta P z.1 z.2) =ᶠ[𝓝 (lam, X)] fun _ => 0 := by
      filter_upwards [(isOpen_collarE.preimage continuous_snd).mem_nhds hX'] with z hz
      exact eta_eq_zero_of_s P z.1 (hz.imp le_of_lt le_of_lt)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiff_eta (lam : ℝ) : ContDiff ℝ ∞ (eta P lam) := by
  have h : ContDiff ℝ ∞ (fun X => eta P (lam, X).1 (lam, X).2) :=
    (eta_smooth P).comp (contDiff_const.prodMk contDiff_id)
  exact h

/-- **`η₀ = 0`** (`lem:shd4-eta`). -/
theorem eta_zero : eta P 0 = 0 := by
  funext X; simp [eta, etaLoc_zero]

/-- **`η_λ` is horizontal** (`lem:shd4-eta`): it has only `du`, `dv` components. -/
theorem eta_horizontal (lam : ℝ) (X v : E4) : eta P lam X v =
    eta P lam X (e 2) * v 2 + eta P lam X (e 3) * v 3 := by
  unfold eta
  split_ifs
  · simp [etaLoc, dc_apply]
  · simp

/-! ### The first-stage identity (`lem:shd4-eta` (c)) -/

/-- `𝒟_λ^*(G β) = (G ∘ 𝒟_λ) β`. -/
lemma pull1_Dlam_GbE (lam : ℝ) (G : ℝ → ℂ → ℝ) :
    pull1 (Dlam P lam) (GbE G) = fun Y =>
      (G (Y 2) (qhatP P (lam * stepA (Y 2)) (wL Y)) * bB (Y 3)) • dc 3 := by
  funext Y; ext v
  simp [GbE, dc_apply, dc3_fderiv_Dlam]

lemma pull1_Dlam_gsmE (lam : ℝ) : pull1 (Dlam P lam) (gsmE P) = gsmE P := by
  funext Y; ext v
  simp [gsmE, dc_apply, dc3_fderiv_Dlam]

lemma contDiff_gsmE : ContDiff ℝ ∞ (gsmE P) :=
  contDiff_smul_dc (contDiff_const.mul ((dc 2).contDiff.sub contDiff_const)) 3

lemma contDiff_fHbE : ContDiff ℝ ∞ (fHbE P) :=
  contDiff_smul_dc (((contDiff_stepA.comp (dc 2).contDiff).mul
    ((contDiff_Hstar P).comp contDiff_pE)).mul (contDiff_bB.comp (dc 3).contDiff)) 3

lemma contDiff_Glam (lam : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × ℂ => Glam P lam z.1 z.2) :=
  (contDiff_stepA.comp contDiff_fst).mul ((contDiff_Hstar P).comp
    (contDiff_fibreArea.comp ((contDiff_qhatInvP P lam).comp contDiff_snd)))

lemma pull2_Dlam_d1 (lam : ℝ) {α : Form1 E4} (hα : ContDiff ℝ ∞ α) (X : E4) :
    pull2 (Dlam P lam) (d1 α) X = d1 (pull1 (Dlam P lam) α) X :=
  (Forms.pull2_d1_apply ((contDiff_Dlam P lam).contDiffAt.of_le (by simp))
    (hα.differentiable (by simp) _)).symm

/-- `𝒟_λ^* dγ_sm = dγ_sm`. -/
lemma pull2_Dlam_gsm (lam : ℝ) (X : E4) : pull2 (Dlam P lam) (d1 (gsmE P)) X = d1 (gsmE P) X := by
  rw [pull2_Dlam_d1 P lam (contDiff_gsmE P), pull1_Dlam_gsmE]

/-- **The first-stage identity in the local model** (lem:shd4-eta):
`Ω₁ + dη_λ = dγ_sm + 𝒟_λ^*[ω_V + d(G_λ β)]` on `𝒜 × ℂ` (coordinates of the `𝒜⁺`-frame). -/
theorem firstStage_eq_loc (lam : ℝ) (X : E4) :
    Omega1Loc P X + d1 (etaLoc P lam) X =
      d1 (gsmE P) X + pull2 (Dlam P lam) (fun Y => omegaV Y + d1 (GbE (Glam P lam)) Y) X := by
  have hGb := contDiff_GbE (contDiff_Glam P lam)
  rw [show (fun Y => omegaV Y + d1 (GbE (Glam P lam)) Y) = omegaV + d1 (GbE (Glam P lam))
    from rfl, pull2_add, suspension, pull2_Dlam_d1 P lam hGb, pull1_Dlam_GbE]
  set GD : Form1 E4 := fun Y =>
    (Glam P lam (Y 2) (qhatP P (lam * stepA (Y 2)) (wL Y)) * bB (Y 3)) • dc 3
  have hGD : ContDiff ℝ ∞ GD := by
    have := (contDiff_GbE (contDiff_Glam P lam)).comp (contDiff_Dlam P lam)
    have e : GD = fun Y => GbE (Glam P lam) (Dlam P lam Y) := by
      funext Y; simp [GD, GbE]
    rw [e]; exact this
  have hPhi : ContDiff ℝ ∞ (fun Y => PhiS P lam Y • dc 2) := contDiff_smul_dc (contDiff_PhiS P lam) 2
  have hL : d1 (fun Y => gsmE P Y + fHbE P Y) X + d1 (etaLoc P lam) X =
      d1 (fun Y => gsmE P Y + fHbE P Y + etaLoc P lam Y) X := by
    have := d1_add3 (X := X) (contDiff_gsmE P) (contDiff_fHbE P) (contDiff_etaLoc P lam)
    rw [this, show (fun Y => gsmE P Y + fHbE P Y) = gsmE P + fHbE P from rfl,
      Forms.d1_add_apply ((contDiff_gsmE P).differentiable (by simp) X)
      ((contDiff_fHbE P).differentiable (by simp) X)]
  have hR : d1 (gsmE P) X + d1 (fun Y => PhiS P lam Y • dc 2) X + d1 GD X =
      d1 (fun Y => gsmE P Y + PhiS P lam Y • dc 2 + GD Y) X :=
    (d1_add3 (contDiff_gsmE P) hPhi hGD).symm
  have hforms : (fun Y => gsmE P Y + fHbE P Y + etaLoc P lam Y) =
      fun Y => gsmE P Y + PhiS P lam Y • dc 2 + GD Y := by
    funext Y; ext v
    simp only [gsmE, fHbE, etaLoc, etaCoef, GD, Glam, add_apply, smul_apply, smul_eq_mul]
    ring
  have key : d1 (fun Y => gsmE P Y + fHbE P Y) X + d1 (etaLoc P lam) X =
      d1 (gsmE P) X + d1 (fun Y => PhiS P lam Y • dc 2) X + d1 GD X := by
    rw [hL, hforms, hR]
  ext v w
  have h2 := congrArg (fun L : E4 →L[ℝ] E4 →L[ℝ] ℝ => L v w) key
  simp only [add_apply] at h2
  simp only [Omega1Loc, add_apply]
  linarith

/-- `chartA^* η_λ = η_λ^{loc}` over `𝒜`. -/
lemma pull1_chartA_eta (lam : ℝ) {X : E4} (hX : X 2 ∈ annulus) :
    pull1 chartA (eta P lam) =ᶠ[𝓝 X] etaLoc P lam := by
  filter_upwards [isOpen_annulusE.mem_nhds hX] with Y hY
  have hb : Y ∈ bandE := annulus_subset_annulusPlus hY
  ext v
  have hc : chartA Y 2 ∈ annulus := by rw [chartA_apply2]; exact hY
  rw [Forms.pull1_apply, eta, if_pos hc, chartInv_chartA hb]
  simp only [etaLoc, add_apply, smul_apply, dc_apply, fderiv_chartA_2 hb, fderiv_chartA_3 hb]

/-- **The first-stage identity** (`lem:shd4-eta` (c)): over `𝒜`, in the
`𝒜⁺`-frame, `Ω₁ + dη_λ = dγ_sm + 𝒟_λ^*[ω_V + d(G_λ β)]`. -/
theorem firstStage_eq (lam : ℝ) {X : E4} (hX : X 2 ∈ annulus) :
    pull2 chartA (firstStage P lam) X =
      d1 (gsmE P) X + pull2 (Dlam P lam) (fun Y => omegaV Y + d1 (GbE (Glam P lam)) Y) X := by
  have hb : X ∈ bandE := annulus_subset_annulusPlus hX
  rw [show firstStage P lam = OmegaT P 1 + d1 (eta P lam) from rfl, pull2_add,
    OmegaT_one_frameA P hX,
    ← Forms.pull2_d1_apply ((contDiffAt_chartA hb).of_le (by simp))
      ((contDiff_eta P lam).differentiable (by simp) _),
    d1_congr (pull1_chartA_eta P lam hX), firstStage_eq_loc]

/-- The same identity with the pre-form: `chartA^* Ω^{(1)}_λ = 𝒟_λ^*[dγ_sm + ω_V + d(G_λβ)]`. -/
theorem firstStage_eq_pre (lam : ℝ) {X : E4} (hX : X 2 ∈ annulus) :
    pull2 chartA (firstStage P lam) X = pull2 (Dlam P lam) (OmegaPreG P (Glam P lam)) X := by
  rw [firstStage_eq P lam hX, ← pull2_Dlam_gsm P lam X, ← pull2_add]
  congr 1
  funext Y
  ext v w
  simp only [OmegaPreG, Pi.add_apply, add_apply]
  ring

/-! ### The first stage is symplectic (`prop:shd4-second`) -/

/-- `∂_s G_λ = f'(s) H*(p(q_λ⁻¹ w))`. -/
lemma deriv_Glam (lam s : ℝ) (w : ℂ) :
    deriv (fun σ => Glam P lam σ w) s =
      deriv stepA s * P.Hstar (π * ‖qhatInvP P lam w‖ ^ 2) :=
  ((contDiff_stepA.differentiable (by simp) s).hasDerivAt.mul_const _).deriv

/-- **The first stage is symplectic** (`prop:shd4-second`): for `λ ∈ [0, 1]`,
`Ω^{(1)}_λ` is nondegenerate at every point of `{p < h + 2δ_m}`. -/
theorem firstStage_nondeg {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) {X : E4}
    (hp : pE X < P.h + 2 * deltam P) : ∀ v, (∀ w, firstStage P lam X v w = 0) → v = 0 := by
  by_cases hX : X 2 ∈ Icc u0 u1
  · have hA : X 2 ∈ annulus := ⟨by linarith [hX.1, show (1 / 8 : ℝ) < u0 by norm_num [u0]],
      by linarith [hX.2, show u1 < (5 / 24 : ℝ) by norm_num [u1]]⟩
    have hb : X ∈ bandE := annulus_subset_annulusPlus hA
    set Y := chartInv X
    have hYb : Y ∈ bandE := chartInv_mem_band hb
    have hYA : Y 2 ∈ annulus := by simpa [Y] using hA
    have hXY : chartA Y = X := chartA_chartInv hb
    have hpY : π * ‖wL Y‖ ^ 2 < P.h + 2 * deltam P := by
      rw [← pE_eq, pE_chartInv hb]; exact hp
    have hloc : ∀ v, (∀ w, pull2 chartA (firstStage P lam) Y v w = 0) → v = 0 := by
      rw [firstStage_eq_pre P lam hYA]
      refine nondeg_pull2_of_inj (fderiv_Dlam_injective P lam Y) ?_
      refine OmegaPreG_nondeg P ((contDiff_Glam P lam).differentiable (by simp) _) ?_
      rw [deriv_Glam, Dlam_apply2, wL_Dlam]
      exact mul_nonneg (Bundle.deriv_stepA_nonneg _) (Hstar_twist_nonneg P hpY _ _)
    have := nondeg_of_pull2_surj (fderiv_chartA_surj hYb) hloc
    rwa [hXY] at this
  · have hd : d1 (eta P lam) X = 0 := d1_eq_zero_of (eta_eventually_zero P lam (Or.inl hX))
    have he : firstStage P lam X = OmegaT P 1 X := by
      show OmegaT P 1 X + d1 (eta P lam) X = _
      rw [hd]; ext v w; simp
    rw [he]
    exact Bundle.Cubic.OmegaT_nondeg' P ⟨zero_le_one, le_rfl⟩ (deltam_one_sub P hp).2
      (Hstar_pos_of P hp).le

end SymplecticPacking.Handle.Cubic
