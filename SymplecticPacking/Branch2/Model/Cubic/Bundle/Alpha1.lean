import SymplecticPacking.Bundle.Alpha1
import SymplecticPacking.Branch2.Model.Cubic.Bundle.Pprim

/-!
# The global primitive `α₁` and its properties

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Bundle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:fer` (`def:fer-Delta`, `lem:fer-Delta`, `def:fer-FA`, `lem:fer-FA`,
`cons:fer-alpha1`, `lem:fer-alpha1`): the annular difference `Δ`, its core period `c(p)`,
the annular primitive `F_𝒜`, and the global primitive `α₁` with its three properties:
* `alpha1_curvature`: `d_C α₁ = κ₁ − κ` (everywhere on the cover);
* `alpha1_annulus`: over `𝒜`, `Γ₁ = γ_σ + p a_𝒜 + α₁ = γ_sm + f H* β` (eq:fer-Gamma1);
* `alpha1_fibre_zero`: both coefficients of `α₁` vanish at the three points `b_j`, for every `p`.

`Δ`, `F_𝒜` are defined by their formulas on all of `ℝ³` but only used (and only meaningful) on
the band `𝒜⁺ × ℝ` (`bandSet`), where `Z₀ ≠ 0`. `ζ_𝒜 F_𝒜` is extended by zero via `Int.fract`.
-/

noncomputable section

namespace SymplecticPacking.Bundle.Cubic

open Set Filter Topology MeasureTheory
open scoped ContDiff Real

attribute [local irreducible] lambdaCu lambdaCv sigmaC etaHu etaHv

/-! ### Generic base-form calculus -/

namespace BForm

end BForm

/-! ### The band `𝒜⁺ × ℝ` -/

/-! ### The annular difference `Δ` (`def:fer-Delta`) -/

/-- `γ_sm = e_h (u − 1/6) dv`. -/
def gammaSm (P : Branch2.VCubic) : BForm := ⟨fun _ _ _ => 0, fun u _ _ => P.eh * (u - 1 / 6)⟩

/-- `f(s) H*(p) β`. -/
def fHbeta (P : Branch2.VCubic) : BForm := ⟨fun _ _ _ => 0, fun u v p => stepA u * P.Hstar p * bB v⟩

/-- **`Δ = γ_σ + p a_𝒜 + α₁⁰ − γ_sm − f H* β`** (with `γ_σ = λ_C`). -/
def DeltaA (P : Branch2.VCubic) : BForm :=
  lambdaC + BForm.pmul (fun p => p) aA + alpha10 P - gammaSm P - fHbeta P

lemma DeltaA_cu (P : Branch2.VCubic) (u v p : ℝ) :
    (DeltaA P).cu u v p = (1 - 3 * p) * lambdaCu u v + (alpha10 P).cu u v p := by
  simp only [DeltaA, BForm.sub_cu, BForm.add_cu, BForm.pmul, aA, lambdaC, gammaSm, fHbeta, ofUV,
    Pi.add_apply, Pi.sub_apply]
  ring

lemma DeltaA_cv (P : Branch2.VCubic) (u v p : ℝ) :
    (DeltaA P).cv u v p = (1 - 3 * p) * lambdaCv u v + (alpha10 P).cv u v p -
      P.eh * (u - 1 / 6) - stepA u * P.Hstar p * bB v := by
  simp only [DeltaA, BForm.sub_cv, BForm.add_cv, BForm.pmul, aA, lambdaC, gammaSm, fHbeta, ofUV,
    Pi.add_apply, Pi.sub_apply]
  ring

lemma smooth_alpha10 (P : Branch2.VCubic) (p : ℝ) : (alpha10 P).Smooth p :=
  ⟨contDiff_Pprim_cu (contDiff_kdiff P p), contDiff_Pprim_cv (contDiff_kdiff P p)⟩

lemma smooth_gammaSm (P : Branch2.VCubic) (p : ℝ) : (gammaSm P).Smooth p :=
  ⟨contDiff_const, contDiff_const.mul (contDiff_fst.sub contDiff_const)⟩

lemma smooth_fHbeta (P : Branch2.VCubic) (p : ℝ) : (fHbeta P).Smooth p :=
  ⟨contDiff_const, ((contDiff_stepA.comp contDiff_fst).mul contDiff_const).mul
    (contDiff_bB.comp contDiff_snd)⟩

lemma smoothOn_DeltaA (P : Branch2.VCubic) (p : ℝ) : (DeltaA P).SmoothOn p bandSet :=
  ((((smoothOn_lambdaC p).add ((smoothOn_lambdaC p).pmul (fun _ => -3) |>.pmul (fun p => p))).add
    ((smooth_alpha10 P p).smoothOn _)).sub ((smooth_gammaSm P p).smoothOn _)).sub
    ((smooth_fHbeta P p).smoothOn _)

lemma dC_gammaSm (P : Branch2.VCubic) (u v p : ℝ) : (gammaSm P).dC u v p = P.eh := by
  simp only [BForm.dC, gammaSm, pu, pv, deriv_const, sub_zero]
  have : HasDerivAt (fun s : ℝ => P.eh * (s - 1 / 6)) P.eh u := by
    simpa using ((hasDerivAt_id u).sub_const (1 / 6 : ℝ)).const_mul P.eh
  exact this.deriv

lemma dC_fHbeta (P : Branch2.VCubic) (u v p : ℝ) :
    (fHbeta P).dC u v p = deriv stepA u * P.Hstar p * bB v := by
  simp only [BForm.dC, fHbeta, pu, pv, deriv_const, sub_zero]
  have : HasDerivAt (fun s : ℝ => stepA s * P.Hstar p * bB v)
      (deriv stepA u * P.Hstar p * bB v) u :=
    ((contDiff_stepA.differentiable (by simp) u).hasDerivAt.mul_const _).mul_const _
  exact this.deriv

/-- **`Δ` is `d_C`-closed on `𝒜⁺`** (`lem:fer-Delta`). -/
theorem DeltaA_closed (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (v p : ℝ) :
    (DeltaA P).dC u v p = 0 := by
  have hx : (u, v) ∈ bandSet := ⟨hu, mem_univ _⟩
  have hL := (smoothOn_lambdaC p).diffAt isOpen_bandSet hx
  have hLa := ((smoothOn_lambdaC p).pmul (fun _ => -3) |>.pmul (fun p => p)).diffAt isOpen_bandSet hx
  have h0 := ((smooth_alpha10 P p).smoothOn univ).diffAt isOpen_univ (mem_univ (u, v))
  have hg := ((smooth_gammaSm P p).smoothOn univ).diffAt isOpen_univ (mem_univ (u, v))
  have hf := ((smooth_fHbeta P p).smoothOn univ).diffAt isOpen_univ (mem_univ (u, v))
  have hs1 := ((smoothOn_lambdaC p).add ((smoothOn_lambdaC p).pmul (fun _ => -3)
    |>.pmul (fun p => p))).diffAt isOpen_bandSet hx
  have hs2 := (((smoothOn_lambdaC p).add ((smoothOn_lambdaC p).pmul (fun _ => -3)
    |>.pmul (fun p => p))).add ((smooth_alpha10 P p).smoothOn _)).diffAt isOpen_bandSet hx
  have hs3 := ((((smoothOn_lambdaC p).add ((smoothOn_lambdaC p).pmul (fun _ => -3)
    |>.pmul (fun p => p))).add ((smooth_alpha10 P p).smoothOn _)).sub
    ((smooth_gammaSm P p).smoothOn _)).diffAt isOpen_bandSet hx
  rw [show DeltaA P = lambdaC + BForm.pmul (fun p => p) (BForm.pmul (fun _ => -3) lambdaC) +
    alpha10 P - gammaSm P - fHbeta P from rfl]
  rw [BForm.dC_sub hs3 hf, BForm.dC_sub hs2 hg, BForm.dC_add hs1 h0, BForm.dC_add hL hLa,
    BForm.dC_pmul, BForm.dC_pmul, dC_lambdaC_band hu, d_alpha10, dC_gammaSm, dC_fHbeta]
  simp only [kappa1, kappa, chiA_band hu]
  ring

/-! ### Periodicity of `Δ` in `v` on the band -/

lemma DeltaA_periodic_v (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (v p : ℝ) :
    (DeltaA P).cu u (v + 1) p = (DeltaA P).cu u v p ∧
      (DeltaA P).cv u (v + 1) p = (DeltaA P).cv u v p := by
  have hL := lambdaC_descends (Zunit_zero_ne_zero_of_mem hu v)
  have hA := alpha10_periodic P u v p
  rw [DeltaA_cu, DeltaA_cu, DeltaA_cv, DeltaA_cv, hL.2.2.1, hL.2.2.2, hA.2.2.1, hA.2.2.2,
    bB_add_one]
  exact ⟨rfl, rfl⟩

/-! ### The core period (`def:fer-Delta`, `lem:fer-Delta`) -/

/-- **The core period** `c(p) = ∮_{u = 1/6} Δ`. -/
def corePeriod (P : Branch2.VCubic) (p : ℝ) : ℝ := ∫ w in (0 : ℝ)..1, (DeltaA P).cv (1 / 6) w p

lemma DeltaA_smoothAt (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (v p : ℝ) :
    ContDiffAt ℝ ∞ (sl (DeltaA P).cu p) (u, v) ∧ ContDiffAt ℝ ∞ (sl (DeltaA P).cv p) (u, v) :=
  ⟨(smoothOn_DeltaA P p).1.contDiffAt (isOpen_bandSet.mem_nhds ⟨hu, mem_univ _⟩),
    (smoothOn_DeltaA P p).2.contDiffAt (isOpen_bandSet.mem_nhds ⟨hu, mem_univ _⟩)⟩

/-- Closedness in the form `∂_s Δ_v = ∂_v Δ_s` on the band. -/
lemma DeltaA_closed' (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (v p : ℝ) :
    pu (DeltaA P).cv u v p = pv (DeltaA P).cu u v p := by
  have := DeltaA_closed P hu v p
  simp only [BForm.dC] at this
  linarith

lemma continuous_DeltaA_cv_v (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (p : ℝ) :
    Continuous (fun w => (DeltaA P).cv u w p) :=
  continuous_iff_continuousAt.mpr fun w =>
    ((DeltaA_smoothAt P hu w p).2.continuousAt.comp
      ((continuous_const.prodMk continuous_id).continuousAt (x := w)) : _)

lemma continuous_pv_DeltaA_cu (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulusPlus) (p : ℝ) :
    Continuous (fun w => pv (DeltaA P).cu u w p) :=
  continuous_iff_continuousAt.mpr fun w =>
    ((contDiffAt_pv_infty (DeltaA_smoothAt P hu w p).1).continuousAt.comp
      ((continuous_const.prodMk continuous_id).continuousAt (x := w)) : _)

/-- `s ↦ ∫₀ᵇ Δ_v(s, w) dw` has derivative `Δ_s(s, b) − Δ_s(s, 0)` on the band. -/
lemma hasDerivAt_integral_DeltaA_cv (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (b p : ℝ) :
    HasDerivAt (fun s' => ∫ w in (0 : ℝ)..b, (DeltaA P).cv s' w p)
      ((DeltaA P).cu s b p - (DeltaA P).cu s 0 p) s := by
  have hg : ContDiffOn ℝ 1 (sl (DeltaA P).cv p) (annulusPlus ×ˢ univ) :=
    (smoothOn_DeltaA P p).2.of_le (by exact_mod_cast le_top)
  have h := hasDerivAt_integral_param isOpen_Ioo hg hs 0 b
  have e : ∫ w in (0 : ℝ)..b, fderiv ℝ (sl (DeltaA P).cv p) (s, w) (1, 0) =
      ∫ w in (0 : ℝ)..b, pv (DeltaA P).cu s w p := by
    refine intervalIntegral.integral_congr fun w _ => ?_
    rw [← pu_eq ((DeltaA_smoothAt P hs w p).2.differentiableAt (by simp)), DeltaA_closed' P hs]
  rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun w _ => hasDerivAt_pv ((DeltaA_smoothAt P hs w p).1.differentiableAt (by simp)))
    ((continuous_pv_DeltaA_cu P hs p).intervalIntegrable _ _)] at h
  exact h

/-- **The core period does not depend on the circle** (`lem:fer-Delta`). -/
theorem corePeriod_indep (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (p : ℝ) :
    ∫ w in (0 : ℝ)..1, (DeltaA P).cv s w p = corePeriod P p := by
  have hd : ∀ x ∈ uIcc (1 / 6 : ℝ) s,
      HasDerivAt (fun s' => ∫ w in (0 : ℝ)..1, (DeltaA P).cv s' w p) 0 x := by
    intro x hx
    have hxA : x ∈ annulusPlus := (ordConnected_Ioo).uIcc_subset one_sixth_mem hs hx
    have := hasDerivAt_integral_DeltaA_cv P hxA 1 p
    have hper := (DeltaA_periodic_v P hxA 0 p).1
    rw [zero_add] at hper
    rwa [hper, sub_self] at this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at this
  unfold corePeriod
  linarith

lemma DeltaA_affine (P : Branch2.VCubic) : AffineP (DeltaA P).cu ∧ AffineP (DeltaA P).cv := by
  obtain ⟨h1, h2⟩ := alpha10_affine P
  constructor
  · intro u v p
    rw [DeltaA_cu, DeltaA_cu, DeltaA_cu, h1 u v p]; ring
  · intro u v p
    rw [DeltaA_cv, DeltaA_cv, DeltaA_cv, h2 u v p]
    simp only [Branch2.CubicData.Hstar, Branch2.CubicData.Hb]; ring

/-- **`c` is affine in `p`** (`lem:fer-Delta`). -/
theorem corePeriod_affine (P : Branch2.VCubic) (p : ℝ) :
    corePeriod P p = corePeriod P 0 + p * (corePeriod P 1 - corePeriod P 0) :=
  integral_affine (g := fun w p => (DeltaA P).cv (1 / 6) w p)
    (fun w p => (DeltaA_affine P).2 (1 / 6) w p)
    ((continuous_DeltaA_cv_v P one_sixth_mem 0).intervalIntegrable _ _)
    ((continuous_DeltaA_cv_v P one_sixth_mem 1).intervalIntegrable _ _) p

attribute [local irreducible] DeltaA

/-! ### The annular primitive `F_𝒜` (`def:fer-FA`, `lem:fer-FA`) -/

/-- **`F_𝒜(s, v, p) = ∫_{1/6}^s D_s(t, 0, p) dt + ∫₀^v D_v(s, w, p) dw`**, where
`Δ − c(p) β = D_s ds + D_v dv` (so `D_s = Δ_s`, `D_v = Δ_v − c(p) b(v)`). -/
def FA (P : Branch2.VCubic) (s v p : ℝ) : ℝ :=
  (∫ t in (1 / 6 : ℝ)..s, (DeltaA P).cu t 0 p) +
    ∫ w in (0 : ℝ)..v, ((DeltaA P).cv s w p - corePeriod P p * bB w)

lemma continuousOn_DeltaA_cu_u (P : Branch2.VCubic) (v p : ℝ) :
    ContinuousOn (fun t => (DeltaA P).cu t v p) annulusPlus := by
  have h : ContinuousOn (sl (DeltaA P).cu p) bandSet := (smoothOn_DeltaA P p).1.continuousOn
  exact h.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ⟨ht, mem_univ _⟩

lemma hasDerivAt_FA_v (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    HasDerivAt (fun t => FA P s t p) ((DeltaA P).cv s v p - corePeriod P p * bB v) v := by
  have hc : Continuous (fun w => (DeltaA P).cv s w p - corePeriod P p * bB w) :=
    (continuous_DeltaA_cv_v P hs p).sub (continuous_cb _)
  exact (hc.integral_hasStrictDerivAt 0 v).hasDerivAt.const_add _

lemma hasDerivAt_FA_u (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    HasDerivAt (fun s' => FA P s' v p) ((DeltaA P).cu s v p) s := by
  have h1 := hasDerivAt_integral_Ioo (continuousOn_DeltaA_cu_u P 0 p) one_sixth_mem hs
  have h2 := (hasDerivAt_integral_DeltaA_cv P hs v p).sub_const
    (corePeriod P p * ∫ w in (0 : ℝ)..v, bB w)
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
  simp only [FA, Pi.add_apply]
  rw [intervalIntegral.integral_sub ((continuous_DeltaA_cv_v P hs' p).intervalIntegrable _ _)
    ((continuous_cb _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

/-- **`d_C F_𝒜 = Δ − c(p) β`** on `𝒜⁺` (`lem:fer-FA`). -/
theorem d_FA (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    pu (FA P) s v p = (DeltaA P).cu s v p ∧
      pv (FA P) s v p = (DeltaA P).cv s v p - corePeriod P p * bB v :=
  ⟨(hasDerivAt_FA_u P hs v p).deriv, (hasDerivAt_FA_v P hs v p).deriv⟩

/-- **`F_𝒜` is `1`-periodic in `v`** on `𝒜⁺` (`lem:fer-FA`). -/
theorem FA_periodic (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    FA P s (v + 1) p = FA P s v p := by
  set D : ℝ → ℝ := fun w => (DeltaA P).cv s w p - corePeriod P p * bB w with hD
  have hc : Continuous D :=
    (continuous_DeltaA_cv_v P hs p).sub (continuous_cb _)
  have hper : Function.Periodic D 1 := fun w => by
    simp only [hD, (DeltaA_periodic_v P hs w p).2, bB_add_one]
  have h01 : ∫ w in (0 : ℝ)..1, D w = 0 := by
    simp only [hD]
    rw [intervalIntegral.integral_sub ((continuous_DeltaA_cv_v P hs p).intervalIntegrable _ _)
      ((continuous_cb _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, corePeriod_indep P hs, integral_bB]
    ring
  simp only [FA]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 v)
    (hc.intervalIntegrable v (v + 1)), hper.intervalIntegral_add_eq v 0, zero_add, h01, add_zero]

/-- `F_𝒜` is smooth on the band. -/
theorem contDiffOn_FA (P : Branch2.VCubic) (p : ℝ) : ContDiffOn ℝ ∞ (sl (FA P) p) bandSet := by
  have h1 : ContDiffOn ℝ ∞ (fun t => (DeltaA P).cu t 0 p) annulusPlus :=
    (smoothOn_DeltaA P p).1.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun t ht => ⟨ht, mem_univ _⟩
  have hT1 := (contDiffOn_integral_Ioo h1 one_sixth_mem).comp contDiff_fst.contDiffOn
    (s := bandSet) fun x hx => hx.1
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (DeltaA P).cv x.1 x.2 p - corePeriod P p * bB x.2)
      (annulusPlus ×ˢ univ) :=
    (smoothOn_DeltaA P p).2.sub (contDiffOn_const.mul (contDiff_bB.comp contDiff_snd).contDiffOn)
  have hT2 := contDiffOn_param_primitive isOpen_Ioo hg
  exact hT1.add hT2

lemma FA_affine (P : Branch2.VCubic) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    FA P s v p = FA P s v 0 + p * (FA P s v 1 - FA P s v 0) := by
  have hc : ∀ q, ContinuousOn (fun t => (DeltaA P).cu t 0 q) (uIcc (1 / 6) s) := fun q =>
    (continuousOn_DeltaA_cu_u P 0 q).mono ((ordConnected_Ioo).uIcc_subset one_sixth_mem hs)
  have hd : ∀ q, Continuous (fun w => (DeltaA P).cv s w q - corePeriod P q * bB w) := fun q =>
    (continuous_DeltaA_cv_v P hs q).sub (continuous_cb _)
  have e1 := integral_affine (g := fun t q => (DeltaA P).cu t 0 q)
    (fun t q => (DeltaA_affine P).1 t 0 q) (hc 0).intervalIntegrable (hc 1).intervalIntegrable p
  have e2 := integral_affine (g := fun w q => (DeltaA P).cv s w q - corePeriod P q * bB w)
    (fun w q => by rw [(DeltaA_affine P).2 s w q, corePeriod_affine P q]; ring)
    ((hd 0).intervalIntegrable _ _) ((hd 1).intervalIntegrable _ _) p (a := 0) (b := v)
  simp only [FA]
  rw [e1, e2]; ring

/-! ### `ζ_𝒜 F_𝒜`, extended by zero -/

/-- `ζ_𝒜 F_𝒜`, extended by zero outside `𝒜⁺` (periodically in `u`). -/
def zetaFA (P : Branch2.VCubic) (u v p : ℝ) : ℝ :=
  if 1 / 12 < Int.fract u ∧ Int.fract u < 1 / 4 then zetaA u * FA P (Int.fract u) v p else 0

lemma zetaFA_eq_zero {P : Branch2.VCubic} {u : ℝ} (h : Int.fract u ∉ Icc (9 / 96 : ℝ) (23 / 96)) (v p : ℝ) :
    zetaFA P u v p = 0 := by
  have : zetaA u = 0 := zetaA_eq_zero fun h' => h (Ioo_subset_Icc_self h')
  simp [zetaFA, this]

/-- `ζ_𝒜 F_𝒜` is smooth on the whole cover. -/
theorem contDiff_zetaFA (P : Branch2.VCubic) (p : ℝ) : ContDiff ℝ ∞ (sl (zetaFA P) p) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases hx : 1 / 12 < Int.fract x₀.1 ∧ Int.fract x₀.1 < 1 / 4
  · have h0 : Int.fract x₀.1 ≠ 0 := by linarith [hx.1]
    obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((⌊x₀.1⌋ : ℤ) : ℝ) := ⟨_, rfl⟩
    have hev1 := (continuous_fst.tendsto x₀).eventually (fract_eventually_of_not_int h0)
    rw [← hn] at hev1
    have hmem : x₀.1 - n ∈ annulusPlus := by
      show x₀.1 - n ∈ Ioo _ _
      rw [show x₀.1 - n = Int.fract x₀.1 by rw [hn, Int.fract]]; exact hx
    have hev2 : ∀ᶠ x in 𝓝 x₀, x.1 - n ∈ annulusPlus :=
      ((continuous_fst.sub continuous_const).tendsto x₀).eventually (isOpen_Ioo.mem_nhds hmem)
    have hev : sl (zetaFA P) p =ᶠ[𝓝 x₀] fun x => zetaA0 (x.1 - n) * FA P (x.1 - n) x.2 p := by
      filter_upwards [hev1, hev2] with x hx1 hx2
      simp only [sl, zetaFA, zetaA, hx1]
      rw [if_pos (show 1 / 12 < x.1 - n ∧ x.1 - n < 1 / 4 from hx2)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hs : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1 - n, x.2) : ℝ × ℝ)) :=
      (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    refine (contDiff_zetaA0.comp (contDiff_fst.sub contDiff_const)).contDiffAt.mul ?_
    exact ((contDiffOn_FA P p).contDiffAt (isOpen_bandSet.mem_nhds ⟨hmem, mem_univ _⟩)).comp x₀
      hs.contDiffAt
  · have hx' : Int.fract x₀.1 ∉ Icc (9 / 96 : ℝ) (23 / 96) := fun h =>
      hx ⟨by linarith [h.1], by linarith [h.2]⟩
    have hev : sl (zetaFA P) p =ᶠ[𝓝 x₀] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto x₀).eventually
        (eventually_fract_notMem (by norm_num) (by norm_num) hx')] with x hx
      exact zetaFA_eq_zero hx _ _
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Over `𝒜`, `ζ_𝒜 F_𝒜 = F_𝒜` near every point. -/
lemma zetaFA_eventually_eq (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulus) (v p : ℝ) :
    sl (zetaFA P) p =ᶠ[𝓝 (u, v)] sl (FA P) p := by
  have hU : Ioo (11 / 96 : ℝ) (21 / 96) ∈ 𝓝 u :=
    isOpen_Ioo.mem_nhds ⟨by linarith [hu.1], by linarith [hu.2]⟩
  filter_upwards [(continuous_fst.tendsto (u, v)).eventually hU] with x hx
  have hfr : Int.fract x.1 = x.1 := fract_of_mem_Ico ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [sl, zetaFA, hfr]
  rw [if_pos ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    zetaA_eq_one ⟨hx.1.le, hx.2.le⟩, one_mul]

lemma zetaFA_periodic (P : Branch2.VCubic) : CoefPeriodic (zetaFA P) := by
  intro u v p
  constructor
  · simp only [zetaFA, zetaA, Int.fract_add_one]
  · simp only [zetaFA]
    split_ifs with h
    · rw [FA_periodic P h]
    · rfl

lemma zetaFA_affine (P : Branch2.VCubic) : AffineP (zetaFA P) := by
  intro u v p
  simp only [zetaFA]
  split_ifs with h
  · rw [FA_affine P h]; ring
  · ring

/-! ### The global primitive `α₁` (`cons:fer-alpha1`) -/

/-- **`α₁^pre = α₁⁰ − c(p) β − d_C(ζ_𝒜 F_𝒜)`.** -/
def alpha1pre (P : Branch2.VCubic) : BForm :=
  alpha10 P - BForm.pmul (corePeriod P) betaB - dCf (zetaFA P)

/-- `A_j(p)`: the `dx_j`-coefficient of `α₁^pre` at `b_j`. -/
def Ajet (P : Branch2.VCubic) (j : Fin 3) (p : ℝ) : ℝ := (alpha1pre P).cu (bpoints j).1 (bpoints j).2 p

/-- `B_j(p)`: the `dy_j`-coefficient of `α₁^pre` at `b_j`. -/
def Bjet (P : Branch2.VCubic) (j : Fin 3) (p : ℝ) : ℝ := (alpha1pre P).cv (bpoints j).1 (bpoints j).2 p

/-- The cut-off linear function `ζ_j (A_j x_j + B_j y_j)`. -/
def jetFn (P : Branch2.VCubic) (j : Fin 3) (u v p : ℝ) : ℝ :=
  zetaJ j u v * (Ajet P j p * centred (bpoints j).1 u + Bjet P j p * centred (bpoints j).2 v)

/-- `Σ_j ζ_j (A_j x_j + B_j y_j)`. -/
def jetSum (P : Branch2.VCubic) (u v p : ℝ) : ℝ := ∑ j : Fin 3, jetFn P j u v p

/-- **The global primitive** (eq:fer-alpha1):
`α₁ = α₁⁰ − c(p) β − d_C(ζ_𝒜 F_𝒜) − Σ_j d_C[ζ_j (A_j(p) x_j + B_j(p) y_j)]`. -/
def alpha1 (P : Branch2.VCubic) : BForm := alpha1pre P - dCf (jetSum P)

lemma smooth_alpha1pre (P : Branch2.VCubic) (p : ℝ) : (alpha1pre P).Smooth p :=
  ((smooth_alpha10 P p).sub (smooth_betaB _ p)).sub (smooth_dCf (contDiff_zetaFA P p))

lemma contDiff_jetFn (P : Branch2.VCubic) (j : Fin 3) (p : ℝ) : ContDiff ℝ ∞ (sl (jetFn P j) p) := by
  have := contDiff_centred_cut (H := fun y => Ajet P j p * y.1 + Bjet P j p * y.2)
    ((contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd))
    (bpoints j).1 (bpoints j).2
  exact this

lemma contDiff_jetSum (P : Branch2.VCubic) (p : ℝ) : ContDiff ℝ ∞ (sl (jetSum P) p) := by
  have : sl (jetSum P) p = fun x => ∑ j : Fin 3, sl (jetFn P j) p x := rfl
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_jetFn P j p

/-- `α₁` is smooth. -/
theorem smooth_alpha1 (P : Branch2.VCubic) (p : ℝ) : (alpha1 P).Smooth p :=
  (smooth_alpha1pre P p).sub (smooth_dCf (contDiff_jetSum P p))

/-- **`d_C α₁ = κ₁ − κ`** (`lem:fer-alpha1`(i)). -/
theorem alpha1_curvature (P : Branch2.VCubic) (u v p : ℝ) :
    (alpha1 P).dC u v p = kappa1 P u v p - kappa u v p := by
  have d := fun (α : BForm) (h : α.Smooth p) => (h.smoothOn univ).diffAt isOpen_univ (mem_univ (u, v))
  show (alpha1pre P - dCf (jetSum P)).dC u v p = _
  rw [BForm.dC_sub (d _ (smooth_alpha1pre P p)) (d _ (smooth_dCf (contDiff_jetSum P p))),
    dC_dCf_of_smooth (contDiff_jetSum P p)]
  show (alpha10 P - BForm.pmul (corePeriod P) betaB - dCf (zetaFA P)).dC u v p - 0 = _
  rw [BForm.dC_sub (d _ ((smooth_alpha10 P p).sub (smooth_betaB _ p)))
      (d _ (smooth_dCf (contDiff_zetaFA P p))),
    dC_dCf_of_smooth (contDiff_zetaFA P p),
    BForm.dC_sub (d _ (smooth_alpha10 P p)) (d _ (smooth_betaB _ p)), BForm.dC_pmul,
    supports.2.1.1, d_alpha10]
  ring

/-- Over `𝒜` all the jet corrections vanish near every point. -/
lemma jetSum_eventually_zero (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulus) (v p : ℝ) :
    sl (jetSum P) p =ᶠ[𝓝 (u, v)] fun _ => 0 := by
  filter_upwards [(continuous_fst.tendsto (u, v)).eventually (isOpen_Ioo.mem_nhds hu)] with x hx
  simp only [sl, jetSum, jetFn]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : zetaJ j x.1 x.2 = 0 := by
    by_contra h
    apply u_far_annulus (zetaJ_ne_zero h).1
    rw [fract_of_mem_Ico ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [this, zero_mul]

/-- `Γ₁ = γ_σ + p a_𝒜 + α₁`. -/
def Gamma1 (P : Branch2.VCubic) : BForm := lambdaC + BForm.pmul (fun p => p) aA + alpha1 P

/-- **The annulus normal form** (eq:fer-Gamma1, `lem:fer-alpha1`(ii)): over `𝒜`, in the
frame of `def:fer-frame`, `Γ₁ = γ_σ + p a_𝒜 + α₁ = γ_sm + f(s) H*(p) β`. -/
theorem alpha1_annulus (P : Branch2.VCubic) {u : ℝ} (hu : u ∈ annulus) (v p : ℝ) :
    (Gamma1 P).cu u v p = (gammaSm P + fHbeta P).cu u v p ∧
      (Gamma1 P).cv u v p = (gammaSm P + fHbeta P).cv u v p := by
  have huA : u ∈ annulusPlus := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hJ := jetSum_eventually_zero P hu v p
  have hZ := zetaFA_eventually_eq P hu v p
  obtain ⟨hFu, hFv⟩ := d_FA P huA v p
  have e1 : pu (zetaFA P) u v p = (DeltaA P).cu u v p := by rw [pu_congr hZ, hFu]
  have e2 : pv (zetaFA P) u v p = (DeltaA P).cv u v p - corePeriod P p * bB v := by
    rw [pv_congr hZ, hFv]
  simp only [Gamma1, alpha1, alpha1pre, BForm.add_cu, BForm.add_cv, BForm.sub_cu, BForm.sub_cv,
    Pi.add_apply, Pi.sub_apply, dCf, BForm.pmul, betaB, aA, lambdaC, ofUV, gammaSm, fHbeta]
  rw [e1, e2, pu_const_zero hJ, pv_const_zero hJ, DeltaA_cu, DeltaA_cv]
  constructor <;> ring

/-- Near `b_j`, the jet sum is the linear function `A_j (u − u_j) + B_j (v − v_j)`. -/
lemma jetSum_near_bpoint (P : Branch2.VCubic) (j : Fin 3) (p : ℝ) :
    sl (jetSum P) p =ᶠ[𝓝 (bpoints j)] fun x =>
      Ajet P j p * (x.1 - (bpoints j).1) + Bjet P j p * (x.2 - (bpoints j).2) := by
  have hc0 : ∀ e : ℝ, centred e e = 0 := fun e => by
    rw [centred, sub_self, zero_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]; ring
  have hfl : ∀ e : ℝ, ⌊e - e + 1 / 2⌋ = 0 := fun e => by
    rw [sub_self, zero_add, Int.floor_eq_zero_iff]; constructor <;> norm_num
  have hcu := centred_eventually (c := (bpoints j).1) (x₀ := (bpoints j).1) (by rw [hc0]; norm_num)
  have hcv := centred_eventually (c := (bpoints j).2) (x₀ := (bpoints j).2) (by rw [hc0]; norm_num)
  rw [hfl] at hcu hcv
  have hcu' := (continuous_fst.tendsto (bpoints j)).eventually hcu
  have hcv' := (continuous_snd.tendsto (bpoints j)).eventually hcv
  have hsmall : ∀ᶠ x : ℝ × ℝ in 𝓝 (bpoints j),
      (x.1 - (bpoints j).1) ^ 2 + (x.2 - (bpoints j).2) ^ 2 < (1 / 200 : ℝ) ^ 2 := by
    have hcont : Continuous (fun x : ℝ × ℝ => (x.1 - (bpoints j).1) ^ 2 + (x.2 - (bpoints j).2) ^ 2) := by fun_prop
    have := hcont.tendsto (bpoints j)
    simp only [sub_self] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hcu', hcv', hsmall] with x hx1 hx2 hx3
  simp only [Int.cast_zero, sub_zero] at hx1 hx2
  have hj1 : zetaJ j x.1 x.2 = 1 := by
    rw [zetaJ]; apply diskCut_eq_one; rw [hx1, hx2]; exact hx3.le
  have habs : |centred (bpoints j).1 x.1| < 1 / 100 := by
    rw [hx1, abs_lt]
    constructor <;> nlinarith [sq_nonneg (x.2 - (bpoints j).2), sq_abs (x.1 - (bpoints j).1)]
  have hk : ∀ k, k ≠ j → zetaJ k x.1 x.2 = 0 := by
    intro k hk
    by_contra h
    have := u_far_other (Ne.symm hk) habs
    linarith [(zetaJ_ne_zero h).1]
  simp only [sl, jetSum]
  rw [Finset.sum_eq_single j (fun k _ hk' => by simp [jetFn, hk k hk'])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp only [jetFn, hj1, one_mul, hx1, hx2]

/-- **`α₁` vanishes at `b_j` for every `p`** (`lem:fer-alpha1`(iii)): both base
coefficients are zero, so `α₁` is the zero covector at every point of the fibre `N_{b_j}`. -/
theorem alpha1_fibre_zero (P : Branch2.VCubic) (j : Fin 3) (p : ℝ) :
    (alpha1 P).cu (bpoints j).1 (bpoints j).2 p = 0 ∧
      (alpha1 P).cv (bpoints j).1 (bpoints j).2 p = 0 := by
  have hJ := jetSum_near_bpoint P j p
  have hu : pu (jetSum P) (bpoints j).1 (bpoints j).2 p = Ajet P j p := by
    rw [pu_congr' (x := bpoints j) (g := fun u v _ => Ajet P j p * (u - (bpoints j).1) +
      Bjet P j p * (v - (bpoints j).2)) hJ]
    simp only [pu]
    have : HasDerivAt (fun s => Ajet P j p * (s - (bpoints j).1) +
        Bjet P j p * ((bpoints j).2 - (bpoints j).2)) (Ajet P j p) (bpoints j).1 := by
      simpa using (((hasDerivAt_id _).sub_const _).const_mul (Ajet P j p)).add_const
        (Bjet P j p * ((bpoints j).2 - (bpoints j).2))
    exact this.deriv
  have hv : pv (jetSum P) (bpoints j).1 (bpoints j).2 p = Bjet P j p := by
    rw [pv_congr' (x := bpoints j) (g := fun u v _ => Ajet P j p * (u - (bpoints j).1) +
      Bjet P j p * (v - (bpoints j).2)) hJ]
    simp only [pv]
    have : HasDerivAt (fun t => Ajet P j p * ((bpoints j).1 - (bpoints j).1) +
        Bjet P j p * (t - (bpoints j).2)) (Bjet P j p) (bpoints j).2 := by
      simpa using (((hasDerivAt_id _).sub_const _).const_mul (Bjet P j p)).const_add
        (Ajet P j p * ((bpoints j).1 - (bpoints j).1))
    exact this.deriv
  simp only [alpha1, BForm.sub_cu, BForm.sub_cv, Pi.sub_apply, dCf]
  rw [hu, hv]
  exact ⟨sub_eq_zero.mpr rfl, sub_eq_zero.mpr rfl⟩

/-! ### `α₁` is affine in `p` and periodic -/

lemma alpha1pre_affine (P : Branch2.VCubic) : AffineP (alpha1pre P).cu ∧ AffineP (alpha1pre P).cv := by
  obtain ⟨h1, h2⟩ := alpha10_affine P
  have hz := zetaFA_affine P
  constructor
  · intro u v p
    simp only [alpha1pre, BForm.sub_cu, Pi.sub_apply, BForm.pmul, betaB, dCf]
    rw [h1 u v p, hz.pu (diffAt_u (contDiff_zetaFA P 0) u v) (diffAt_u (contDiff_zetaFA P 1) u v)]
    ring
  · intro u v p
    simp only [alpha1pre, BForm.sub_cv, Pi.sub_apply, BForm.pmul, betaB, dCf]
    rw [h2 u v p, hz.pv (diffAt_v (contDiff_zetaFA P 0) u v) (diffAt_v (contDiff_zetaFA P 1) u v),
      corePeriod_affine P p]
    ring

lemma jetSum_affine (P : Branch2.VCubic) : AffineP (jetSum P) := by
  intro u v p
  simp only [jetSum, jetFn, Ajet, Bjet, Fin.sum_univ_three]
  rw [(alpha1pre_affine P).1 _ _ p, (alpha1pre_affine P).2 _ _ p,
    (alpha1pre_affine P).1 (bpoints 1).1 _ p, (alpha1pre_affine P).2 (bpoints 1).1 _ p,
    (alpha1pre_affine P).1 (bpoints 2).1 _ p, (alpha1pre_affine P).2 (bpoints 2).1 _ p]
  ring

/-- **`α₁` is affine in `p`** (`lem:fer-alpha1`(i)). -/
theorem alpha1_affine (P : Branch2.VCubic) : AffineP (alpha1 P).cu ∧ AffineP (alpha1 P).cv := by
  have hJ := jetSum_affine P
  constructor
  · intro u v p
    simp only [alpha1, BForm.sub_cu, Pi.sub_apply, dCf]
    rw [(alpha1pre_affine P).1 u v p, hJ.pu (diffAt_u (contDiff_jetSum P 0) u v)
      (diffAt_u (contDiff_jetSum P 1) u v)]
    ring
  · intro u v p
    simp only [alpha1, BForm.sub_cv, Pi.sub_apply, dCf]
    rw [(alpha1pre_affine P).2 u v p, hJ.pv (diffAt_v (contDiff_jetSum P 0) u v)
      (diffAt_v (contDiff_jetSum P 1) u v)]
    ring

lemma jetSum_periodic (P : Branch2.VCubic) : CoefPeriodic (jetSum P) := by
  intro u v p
  simp [jetSum, jetFn, zetaJ_periodic, centred_add_one]

/-- **`α₁` is a one-form on the torus**: `1`-periodic in `u` and `v` (`lem:fer-alpha1`(i)). -/
theorem alpha1_periodic (P : Branch2.VCubic) : (alpha1 P).Periodic := by
  intro u v p
  have hA := alpha10_periodic P u v p
  have hz1 := pu_periodic (zetaFA_periodic P) u v p
  have hz2 := pv_periodic (zetaFA_periodic P) u v p
  have hj1 := pu_periodic (jetSum_periodic P) u v p
  have hj2 := pv_periodic (jetSum_periodic P) u v p
  simp only [alpha1, alpha1pre, BForm.sub_cu, BForm.sub_cv, Pi.sub_apply, BForm.pmul, betaB, dCf]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hz1.1, hz1.2, hz2.1, hz2.2, hj1.1, hj1.2, hj2.1, hj2.2,
    bB_add_one]
  exact ⟨rfl, rfl, rfl, rfl⟩

end SymplecticPacking.Bundle.Cubic
