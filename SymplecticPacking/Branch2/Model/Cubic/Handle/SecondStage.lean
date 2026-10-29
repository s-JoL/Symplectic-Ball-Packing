import SymplecticPacking.Handle.SecondStage
import SymplecticPacking.Branch2.Model.Cubic.Handle.FirstStage

/-!
# The second stage of the handle and the final form

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`cons:shd4-xi`, `lem:shd4-xi`,
`prop:shd4-third`): the second stage and the final form.

* `xiA P = 𝒟^*[(G_f − G₁)β] = ((G_f − G₁) ∘ 𝒟) β` on `𝒜 × ℂ` (local `𝒜⁺`-frame coordinates),
  `𝒟 = Dlam P 1`, `G₁ = Glam P 1`;
* `JbE P = J(p) β` — a global form (no frame is involved: `p` is global, `β` a base form);
* `xi P = J(p) π^*β + ext₀(ξ_𝒜 − J(p) β)` on `N` (global `Zunit`-frame coordinates);
* `secondStage P τ = Ω^{(1)}_1 + τ dξ`, `OmegaFinal P = Ω^{(2)}_1 = Ω₀ + dα₁ + dη₁ + dξ`;
* `OmegaPre P = dγ_sm + ω_V + d(G_f β)` and the exported identity
  `OmegaFinal_eq_pullback`: `chartA^* Ω_final = 𝒟^* Ω_pre` on `𝒜 × ℂ`, `𝒟` a diffeomorphism of
  `𝒜 × ℂ` preserving base points and mapping `𝒜 × {p < h}` onto itself.
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus pp contDiff_stepA contDiff_bB bpoints)
open SymplecticPacking.Bundle.Cubic (OmegaT OmegaT_split)
open SymplecticPacking.Qhat.Cubic (qhatP qhatInvP QhamP Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

attribute [local irreducible] Bundle.frameA Bundle.Zunit Bundle.lambdaCu Bundle.lambdaCv
  Bundle.etaHu Bundle.etaHv Bundle.sigmaC

variable (P : Branch2.VCubic)

/-! ### The second-stage primitive (`cons:shd4-xi`) -/

/-- `G_f − G₁`. -/
def Gdiff (s : ℝ) (w : ℂ) : ℝ := Gf P s w - Glam P 1 s w

/-- **`ξ_𝒜 = 𝒟^*[(G_f − G₁)β] = ((G_f − G₁) ∘ 𝒟) β`** on `𝒜 × ℂ`. -/
def xiA : Form1 E4 := fun X => (Gdiff P (X 2) (wL (Dlam P 1 X)) * bB (X 3)) • dc 3

/-- `J(p) π^*β`, a global one-form. -/
def JbE : Form1 E4 := fun X => (P.J (pE X) * bB (X 3)) • dc 3

open Classical in
/-- **The second-stage primitive on `N`**: `ξ = J(p) π^*β + ext₀(ξ_𝒜 − J(p) β)`. -/
def xi : Form1 E4 := fun X =>
  JbE P X + if X 2 ∈ annulus then xiA P (chartInv X) - JbE P (chartInv X) else 0

/-- **The second stage** `Ω^{(2)}_τ = Ω^{(1)}_1 + τ dξ` (`cons:shd4-xi`). -/
def secondStage (τ : ℝ) : Form2 E4 := fun X => firstStage P 1 X + τ • d1 (xi P) X

/-- **The final form** `Ω_final = Ω^{(2)}_1 = Ω₀ + dα₁ + dη₁ + dξ`. -/
def OmegaFinal : Form2 E4 := secondStage P 1

/-- **`Ω_pre = dγ_sm + ω_V + d(G_f β)`** (`prop:shd4-third`), in the `𝒜⁺`-frame. -/
def OmegaPre : Form2 E4 := OmegaPreG P (Gf P)

/-- `Ĝ_τ = (1 − τ) G₁ + τ G_f`. -/
def Ghat (τ s : ℝ) (w : ℂ) : ℝ := (1 - τ) * Glam P 1 s w + τ * Gf P s w

/-! ### `ξ` is global (`lem:shd4-xi`) -/

lemma contDiff_Gdiff : ContDiff ℝ ∞ (fun z : ℝ × ℂ => Gdiff P z.1 z.2) :=
  (contDiff_Gf P).sub (contDiff_Glam P 1)

lemma xiA_eq_pull : xiA P = pull1 (Dlam P 1) (GbE (Gdiff P)) := by
  rw [pull1_Dlam_GbE]; funext Y; simp [xiA, Dlam]

lemma contDiff_xiA : ContDiff ℝ ∞ (xiA P) := by
  have h := (contDiff_GbE (contDiff_Gdiff P)).comp (contDiff_Dlam P 1)
  have e : xiA P = fun Y => GbE (Gdiff P) (Dlam P 1 Y) := by funext Y; simp [xiA, GbE]
  rw [e]; exact h

lemma contDiff_JbE : ContDiff ℝ ∞ (JbE P) :=
  contDiff_smul_dc (((contDiff_J P).comp contDiff_pE).mul (contDiff_bB.comp (dc 3).contDiff)) 3

/-- **`ξ_𝒜 = J(p) β` on both collars** (`lem:shd4-xi`): the cancellation `q⁻¹q = id`. -/
theorem xi_collar {Y : E4} (hY : Y 2 ≤ u0 ∨ u1 ≤ Y 2) : xiA P Y = JbE P Y := by
  rcases hY with hY | hY
  · have hf : stepA (Y 2) = 0 := Bundle.stepA_eq_zero hY
    have hD : wL (Dlam P 1 Y) = wL Y := by rw [wL_Dlam, hf, mul_zero, qhatP_zero]; rfl
    have hlow : Y 2 ≤ layerLeft P 1 := hY.trans (u0_lt_layerLeft_one P).le
    simp only [xiA, JbE, Gdiff, hD, Gf_low P hlow, Glam, hf, zero_mul, sub_zero, pE_eq]
  · have hf : stepA (Y 2) = 1 := Bundle.stepA_eq_one hY
    have hD : wL (Dlam P 1 Y) = qhatP P 1 (wL Y) := by rw [wL_Dlam, hf, mul_one]
    have hup : layerRight P (Nlayers P) ≤ Y 2 := (layerRight_N_lt_u1 P).le.trans hY
    simp only [xiA, JbE, Gdiff, hD, Gf_up P hup, Glam, hf, one_mul, qhatInvP_qhatP, pE_eq]
    rfl

lemma xi_eq_of_not_annulus {X : E4} (h : X 2 ∉ annulus) : xi P X = JbE P X := by
  simp [xi, h]

lemma xi_eq_of_annulus {X : E4} (h : X 2 ∈ annulus) :
    xi P X = xiA P (chartInv X) := by
  have hb : X ∈ bandE := annulus_subset_annulusPlus h
  have hJ : JbE P (chartInv X) = JbE P X := by simp [JbE, pE_chartInv hb]
  simp only [xi, if_pos h, hJ]
  abel

lemma xi_eq_JbE_of_s {X : E4} (hX : X 2 ≤ u0 ∨ u1 ≤ X 2) : xi P X = JbE P X := by
  by_cases h : X 2 ∈ annulus
  · rw [xi_eq_of_annulus P h, xi_collar P (by simpa using hX)]
    simp [JbE, pE_chartInv (annulus_subset_annulusPlus h)]
  · exact xi_eq_of_not_annulus P h

/-- Off `[u₀, u₁]`, `ξ = J(p) β` near every point. -/
theorem xi_eventually_JbE {X : E4} (hX : X 2 ∉ Icc u0 u1) : xi P =ᶠ[𝓝 X] JbE P := by
  have hX' : X 2 < u0 ∨ u1 < X 2 := by
    simp only [mem_Icc, not_and_or, not_le] at hX; exact hX
  filter_upwards [isOpen_collarE.mem_nhds hX'] with Y hY
  exact xi_eq_JbE_of_s P (hY.imp le_of_lt le_of_lt)

/-- **`ξ` is a smooth one-form on `N`** (`lem:shd4-xi`). -/
theorem xi_smooth : ContDiff ℝ ∞ (xi P) := by
  rw [contDiff_iff_contDiffAt]
  intro X
  by_cases hX : X 2 ∈ annulus
  · have hev : xi P =ᶠ[𝓝 X] fun Y => xiA P (chartInv Y) := by
      filter_upwards [isOpen_annulusE.mem_nhds hX] with Y hY
      exact xi_eq_of_annulus P hY
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hc : ContDiffAt ℝ ∞ (xiA P) (chartInv X) := (contDiff_xiA P).contDiffAt
    exact hc.comp X (contDiffAt_chartInv (annulus_subset_annulusPlus hX))
  · have hX' : X 2 ∉ Icc u0 u1 := fun h => hX ⟨by
      linarith [h.1, show (1 / 8 : ℝ) < u0 by norm_num [u0]],
      by linarith [h.2, show u1 < (5 / 24 : ℝ) by norm_num [u1]]⟩
    exact (contDiff_JbE P).contDiffAt.congr_of_eventuallyEq (xi_eventually_JbE P hX')

/-- **`ξ` is horizontal**: it is a multiple of `dv`. -/
theorem xi_horizontal (X : E4) : ∃ c : ℝ, xi P X = c • dc 3 := by
  by_cases h : X 2 ∈ annulus
  · rw [xi_eq_of_annulus P h]; exact ⟨_, rfl⟩
  · rw [xi_eq_of_not_annulus P h]; exact ⟨_, rfl⟩

/-- **`ξ` is toric on `{p > P_supp}`** (`lem:shd4-xi`): there `ξ = c(u, p) b(v) dv`. -/
theorem xi_toric_near_boundary : ∃ c : ℝ → ℝ → ℝ, ∀ X : E4, Psupp P < pE X →
    xi P X = (c (X 2) (pE X) * bB (X 3)) • dc 3 := by
  classical
  refine ⟨fun u p => if u ∈ annulus then
    (P.J p + ∑ i ∈ Finset.Icc 1 P.k, rhoLayer P i u * P.hi i p +
      rhoLayer P (Nlayers P) u * (P.K p - P.J p - ∑ i ∈ Finset.Icc 1 P.k, P.hi i p)) -
      stepA u * P.Hstar p else P.J p, fun X hX => ?_⟩
  by_cases h : X 2 ∈ annulus
  · have hb : X ∈ bandE := annulus_subset_annulusPlus h
    rw [xi_eq_of_annulus P h]
    set Y := chartInv X
    have hpY : Psupp P < π * ‖wL Y‖ ^ 2 := by rw [← pE_eq, pE_chartInv hb]; exact hX
    have hD : wL (Dlam P 1 Y) = wL Y := by rw [wL_Dlam, qhatP_collar P hpY]
    have hq : qhatInvP P 1 (wL Y) = wL Y := qhatInvP_collar P hpY
    have hY2 : Y 2 = X 2 := chartInv_apply2 X
    have hY3 : Y 3 = X 3 := chartInv_apply3 X
    have hp : π * ‖wL Y‖ ^ 2 = pE X := by rw [← pE_eq, pE_chartInv hb]
    simp only [xiA, hD, Gdiff, Gf, Rstar, Glam, hq, hY2, hY3, hp, if_pos h]
  · rw [xi_eq_of_not_annulus P h]
    simp [JbE, h]

/-! ### The second stage on `𝒜` and off it (`prop:shd4-third`) -/

lemma pull1_chartA_xi {X : E4} (hX : X 2 ∈ annulus) : pull1 chartA (xi P) =ᶠ[𝓝 X] xiA P := by
  filter_upwards [isOpen_annulusE.mem_nhds hX] with Y hY
  have hb : Y ∈ bandE := annulus_subset_annulusPlus hY
  have hc : chartA Y 2 ∈ annulus := by rw [chartA_apply2]; exact hY
  ext v
  rw [Forms.pull1_apply, xi_eq_of_annulus P hc, chartInv_chartA hb]
  simp only [xiA, smul_apply, dc_apply, fderiv_chartA_3 hb]

lemma GbE_Ghat (τ : ℝ) : GbE (Ghat P τ) = GbE (Glam P 1) + τ • GbE (Gdiff P) := by
  funext Y; ext v
  simp only [GbE, Ghat, Gdiff, Pi.add_apply, Pi.smul_apply, add_apply, smul_apply, smul_eq_mul]
  ring

lemma OmegaPreG_Ghat (τ : ℝ) (Y : E4) :
    OmegaPreG P (Glam P 1) Y + τ • d1 (GbE (Gdiff P)) Y = OmegaPreG P (Ghat P τ) Y := by
  have h1 := (contDiff_GbE (contDiff_Glam P 1)).differentiable (by simp) Y
  have h2 : DifferentiableAt ℝ (τ • GbE (Gdiff P)) Y :=
    ((contDiff_GbE (contDiff_Gdiff P)).const_smul τ).differentiable (by simp) Y
  have hd : d1 (GbE (Ghat P τ)) Y = d1 (GbE (Glam P 1)) Y + τ • d1 (GbE (Gdiff P)) Y := by
    rw [GbE_Ghat, Forms.d1_add_apply h1 h2, Forms.d1_smul_const]; rfl
  ext v w
  have h := congrArg (fun L : E4 →L[ℝ] E4 →L[ℝ] ℝ => L v w) hd
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  simp only [OmegaPreG, add_apply, smul_apply, smul_eq_mul, h]
  ring

/-- **The second stage on `𝒜`** (lem:shd4-xi): over `𝒜`, in the `𝒜⁺`-frame,
`Ω^{(2)}_τ = 𝒟^*[dγ_sm + ω_V + d(Ĝ_τ β)]`, `Ĝ_τ = (1 − τ)G₁ + τG_f`. -/
theorem secondStage_eq_on_A (τ : ℝ) {X : E4} (hX : X 2 ∈ annulus) :
    pull2 chartA (secondStage P τ) X = pull2 (Dlam P 1) (OmegaPreG P (Ghat P τ)) X := by
  have hb : X ∈ bandE := annulus_subset_annulusPlus hX
  have hxi : pull2 chartA (d1 (xi P)) X = d1 (xiA P) X := by
    rw [← Forms.pull2_d1_apply ((contDiffAt_chartA hb).of_le (by simp))
      ((xi_smooth P).differentiable (by simp) _)]
    exact d1_congr (pull1_chartA_xi P hX)
  rw [show secondStage P τ = firstStage P 1 + τ • d1 (xi P) from rfl, pull2_add, pull2_smul,
    firstStage_eq_pre P 1 hX, hxi, xiA_eq_pull,
    ← pull2_Dlam_d1 P 1 (contDiff_GbE (contDiff_Gdiff P)), ← pull2_smul, ← pull2_add]
  congr 1
  funext Y
  exact OmegaPreG_Ghat P τ Y

lemma Ghat_one : Ghat P 1 = Gf P := by funext s w; simp [Ghat]

lemma hasFDerivAt_J_pE (X : E4) :
    HasFDerivAt (fun Y => P.J (pE Y)) (deriv P.J (pE X) • dpE X) X :=
  ((contDiff_J P).differentiable (by simp) (pE X)).hasDerivAt.comp_hasFDerivAt X
    (Bundle.hasFDerivAt_pE X)

lemma d1_JbE (X : E4) :
    d1 (JbE P) X = (deriv P.J (pE X) * bB (X 3)) • wedge (dpE X) (dc 3) := by
  have hb : HasFDerivAt (fun Y : E4 => bB (Y 3)) (deriv bB (X 3) • dc 3) X :=
    ((contDiff_bB.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt X (dc 3).hasFDerivAt
  have h : HasFDerivAt (fun Y => P.J (pE Y) * bB (Y 3)) _ X := (hasFDerivAt_J_pE P X).mul hb
  rw [show JbE P = fun Y => (P.J (pE Y) * bB (Y 3)) • dc 3 from rfl,
    d1_smul_const_form h.differentiableAt, h.fderiv]
  ext v w
  simp only [wedge_apply, add_apply, smul_apply, smul_eq_mul, dc_apply]
  ring

/-- **The second stage off `𝒜`** (`prop:shd4-third`): off `[u₀, u₁]`,
`Ω^{(2)}_τ = Ω₁ + τ J'(p) dp ∧ β`. -/
theorem secondStage_off (τ : ℝ) {X : E4} (hX : X 2 ∉ Icc u0 u1) :
    secondStage P τ X = OmegaT P 1 X + (τ * (deriv P.J (pE X) * bB (X 3))) • wedge (dpE X) (dc 3) := by
  have hd : d1 (eta P 1) X = 0 := d1_eq_zero_of (eta_eventually_zero P 1 (Or.inl hX))
  have hx : d1 (xi P) X = d1 (JbE P) X := d1_congr (xi_eventually_JbE P hX)
  show OmegaT P 1 X + d1 (eta P 1) X + τ • d1 (xi P) X = _
  rw [hd, hx, d1_JbE]
  ext v w
  simp [smul_eq_mul, mul_assoc]

/-- **The second stage is symplectic** (`prop:shd4-third`): for `τ ∈ [0, 1]`,
`Ω^{(2)}_τ` is nondegenerate at every point of `{p < h + 2δ_m}`. -/
theorem secondStage_nondeg {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {X : E4}
    (hp : pE X < P.h + 2 * deltam P) : ∀ v, (∀ w, secondStage P τ X v w = 0) → v = 0 := by
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
    have hG : ContDiff ℝ ∞ (fun z : ℝ × ℂ => Ghat P τ z.1 z.2) :=
      (contDiff_const.mul (contDiff_Glam P 1)).add (contDiff_const.mul (contDiff_Gf P))
    have hloc : ∀ v, (∀ w, pull2 chartA (secondStage P τ) Y v w = 0) → v = 0 := by
      rw [secondStage_eq_on_A P τ hYA]
      refine nondeg_pull2_of_inj (fderiv_Dlam_injective P 1 Y) ?_
      refine OmegaPreG_nondeg P (hG.differentiable (by simp) _) ?_
      rw [Dlam_apply2, wL_Dlam]
      set s := Y 2
      set w' := qhatP P (1 * stepA s) (wL Y)
      have hw' : π * ‖w'‖ ^ 2 < P.h + 2 * deltam P := twist_bound P hpY _
      have h1 : HasDerivAt (fun σ => Glam P 1 σ w')
          (deriv stepA s * P.Hstar (π * ‖qhatInvP P 1 w'‖ ^ 2)) s :=
        (contDiff_stepA.differentiable (by simp) s).hasDerivAt.mul_const _
      have h2 : HasDerivAt (fun σ => Gf P σ w') (deriv (fun σ => Gf P σ w') s) s :=
        (hasDerivAt_Gf P s w').differentiableAt.hasDerivAt
      have h3 : HasDerivAt (fun σ => (1 - τ) * Glam P 1 σ w' + τ * Gf P σ w') _ s :=
        (h1.const_mul (1 - τ)).add (h2.const_mul τ)
      rw [show (fun σ => Ghat P τ σ w') = fun σ => (1 - τ) * Glam P 1 σ w' + τ * Gf P σ w'
        from rfl, h3.deriv]
      refine add_nonneg (mul_nonneg (by linarith [hτ.2]) (mul_nonneg
        (Bundle.deriv_stepA_nonneg _) (Hstar_twist_nonneg P hpY _ _))) (mul_nonneg hτ.1 ?_)
      exact Gf_mono P (deltam_residual P hw').1.le s
    have := nondeg_of_pull2_surj (fderiv_chartA_surj hYb) hloc
    rwa [hXY] at this
  · rw [secondStage_off P τ hX]
    have hsplit : OmegaT P 1 X + (τ * (deriv P.J (pE X) * bB (X 3))) • wedge (dpE X) (dc 3) =
        splitForm (2 * π * dc 0 X) (2 * π * dc 1 X)
          (-3 * Bundle.etaHu (dc 2 X) (dc 3 X) + 1 * pp (Bundle.Cubic.alpha1 P).cu (dc 2 X) (dc 3 X) (pE X))
          (-3 * Bundle.etaHv (dc 2 X) (dc 3 X) + 1 * pp (Bundle.Cubic.alpha1 P).cv (dc 2 X) (dc 3 X) (pE X) +
            τ * (deriv P.J (pE X) * bB (X 3)))
          (Bundle.Cubic.kappaT P 1 (dc 2 X) (dc 3 X) (pE X)) := by
      rw [OmegaT_split]
      ext v w
      simp only [splitForm, add_apply, smul_apply, wedge_apply, smul_eq_mul, dpE]
      ring
    rw [hsplit]
    exact Forms.splitForm_nondeg (deltam_kappaT P ⟨zero_le_one, le_rfl⟩ _ _ hp).ne'

/-! ### The final form over the annulus (`prop:shd4-third`) -/

/-- The inverse twist `𝒟_λ⁻¹(s, t, w) = (s, t, q_{λ f(s)}⁻¹(w))`. -/
def DlamInv (lam : ℝ) (X : E4) : E4 := mk (qhatInvP P (lam * stepA (X 2)) (wL X)) (X 2) (X 3)

lemma DlamInv_Dlam (lam : ℝ) (X : E4) : DlamInv P lam (Dlam P lam X) = X := by
  conv_rhs => rw [← mk_wL X]
  simp [DlamInv, Dlam, qhatInvP_qhatP]

lemma Dlam_DlamInv (lam : ℝ) (X : E4) : Dlam P lam (DlamInv P lam X) = X := by
  conv_rhs => rw [← mk_wL X]
  simp [DlamInv, Dlam, qhatP_qhatInvP]

lemma contDiff_DlamInv (lam : ℝ) : ContDiff ℝ ∞ (DlamInv P lam) := by
  have h : ContDiff ℝ ∞ (fun X : E4 => mkL (qqInv P (lam * stepA (X 2), wL X), dc 2 X, dc 3 X)) :=
    mkL.contDiff.comp (((contDiff_qqInv P).comp ((contDiff_tau lam).prodMk wL.contDiff)).prodMk
      ((dc 2).contDiff.prodMk (dc 3).contDiff))
  exact h

/-- **The final form over the annulus** (`prop:shd4-third`): with
`Ω_pre = dγ_sm + ω_V + d(G_f β)` (in the `𝒜⁺`-frame, `G_f` and `p` evaluated at the target point),
* `Ω_final = 𝒟^* Ω_pre` on `𝒜 × ℂ` (the left side transported to the `𝒜⁺`-frame by `chartA`);
* `𝒟 = 𝒟₁` is a diffeomorphism of `𝒜 × ℂ` (smooth, with smooth inverse `DlamInv P 1`) which
  preserves base points and maps `𝒜 × {p < h}` onto itself. -/
theorem OmegaFinal_eq_pullback :
    (∀ X : E4, X 2 ∈ annulus →
      pull2 chartA (OmegaFinal P) X = pull2 (Dlam P 1) (OmegaPre P) X) ∧
    ContDiff ℝ ∞ (Dlam P 1) ∧ ContDiff ℝ ∞ (DlamInv P 1) ∧
    (∀ X, DlamInv P 1 (Dlam P 1 X) = X) ∧ (∀ X, Dlam P 1 (DlamInv P 1 X) = X) ∧
    (∀ X, Dlam P 1 X 2 = X 2 ∧ Dlam P 1 X 3 = X 3) ∧
    Dlam P 1 '' {X : E4 | X 2 ∈ annulus ∧ pE X < P.h} = {X : E4 | X 2 ∈ annulus ∧ pE X < P.h} := by
  have hpD : ∀ lam X, pE (Dlam P lam X) = π * ‖qhatP P (lam * stepA (X 2)) (wL X)‖ ^ 2 :=
    fun lam X => by rw [pE_eq, wL_Dlam]
  refine ⟨fun X hX => ?_, contDiff_Dlam P 1, contDiff_DlamInv P 1, DlamInv_Dlam P 1,
    Dlam_DlamInv P 1, fun X => ⟨Dlam_apply2 P 1 X, Dlam_apply3 P 1 X⟩, ?_⟩
  · rw [OmegaFinal, secondStage_eq_on_A P 1 hX, Ghat_one]; rfl
  · ext Y
    constructor
    · rintro ⟨X, ⟨hX2, hXp⟩, rfl⟩
      refine ⟨by rw [Dlam_apply2]; exact hX2, ?_⟩
      rw [hpD]
      exact qhatP_mem_openDisk P (Psupp_lt_h P) _ (by rw [← pE_eq]; exact hXp)
    · rintro ⟨hY2, hYp⟩
      refine ⟨DlamInv P 1 Y, ⟨by simpa [DlamInv] using hY2, ?_⟩, Dlam_DlamInv P 1 Y⟩
      rw [DlamInv, pE_mk]
      exact qhatInvP_mem_openDisk P (Psupp_lt_h P) _ (by rw [← pE_eq]; exact hYp)

end SymplecticPacking.Handle.Cubic
