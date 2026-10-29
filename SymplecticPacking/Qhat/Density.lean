import Mathlib
import SymplecticPacking.Qhat.Constants

/-!
# The density family and the maps `f_s`

`sec:pll-data`: the density family (`def:pll-density`), positivity and
area growth (`lem:pll-density-area`), and the fixed-`s` part of `lem:pln-energy`
(each `f_s`, `s ∈ [0, 1]`, is a symplectic `C^∞` injection, linear near `0`; `f₀ = 𝐋`, `f₁ = f`).
Joint smoothness in `(s, z)` is in `Qhat/DensitySmooth.lean`.

For a fixed `s` we apply the normalisation API of `Inner/Normalize.lean` to the constant family
`JsC s = fun _ => J_s` (parameter `0 ∈ (-1, 1)`); all normalisation maps of `J_s` at `s` are
definitionally those of `JsC s` at `0`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### Definitions (`def:pll-density`) -/

/-- `X_s(u) = (1 - s) a₀ u + s X̃(u)`. -/
def Xs (s u : ℝ) : ℝ := (1 - s) * a0 P * u + s * Inner.Xtilde P u

/-- `Y_s(v) = (1 - s) b₀ v + s Ỹ(v)`. -/
def Ys (s v : ℝ) : ℝ := (1 - s) * b0 P * v + s * Inner.Ytilde P v

/-- `J_s(u, v) = X_s'(u) Y_s'(v)` (written out; see `Js_eq_deriv`). -/
def Js (s : ℝ) (w : ℂ) : ℝ :=
  ((1 - s) * a0 P + s * deriv (Inner.Xtilde P) w.re) *
    ((1 - s) * b0 P + s * deriv (Inner.Ytilde P) w.im)

/-- `F_s = (X_s, Y_s)`. -/
def Fs (s : ℝ) (w : ℂ) : ℂ := (Xs P s w.re : ℂ) + (Ys P s w.im : ℂ) * I

/-- `f_s = F_s ∘ T_s⁻¹ ∘ D_s` (normalisations built from `J_s`). -/
def fs (s : ℝ) (z : ℂ) : ℂ := Fs P s (Inner.TrotInv (Js P) s (Inner.Darea (Js P) s z))

/-- `𝐋 = diag(c_x, c_y)`. -/
def Lmap (z : ℂ) : ℂ := (Inner.cx P * z.re : ℝ) + (Inner.cy P * z.im : ℝ) * I

/-- `𝓐_s(E) = π ∫₀^E J̄_s`. -/
abbrev As (s E : ℝ) : ℝ := Inner.Acal (Js P) s E

/-- `E_s = 𝓐_s⁻¹`. -/
abbrev Es (s I : ℝ) : ℝ := Inner.Einv (Js P) s I

/-- The constant family `t ↦ J_s` (for the fixed-`s` normalisation API). -/
def JsC (s : ℝ) : ℝ → ℂ → ℝ := fun _ => Js P s

/-! ### Elementary properties -/

lemma Xtilde_hasDerivAt (u : ℝ) :
    HasDerivAt (Inner.Xtilde P) (deriv (Inner.Xtilde P) u) u :=
  ((Inner.Xtilde_smooth P).differentiable (by simp) u).hasDerivAt

lemma Ytilde_hasDerivAt (v : ℝ) :
    HasDerivAt (Inner.Ytilde P) (deriv (Inner.Ytilde P) v) v :=
  ((Inner.Ytilde_smooth P).differentiable (by simp) v).hasDerivAt

lemma Xs_hasDerivAt (s u : ℝ) :
    HasDerivAt (Xs P s) ((1 - s) * a0 P + s * deriv (Inner.Xtilde P) u) u := by
  have := ((hasDerivAt_id u).const_mul ((1 - s) * a0 P)).add
    ((Xtilde_hasDerivAt P u).const_mul s)
  rw [show (1 - s) * a0 P + s * deriv (Inner.Xtilde P) u =
    (1 - s) * a0 P * 1 + s * deriv (Inner.Xtilde P) u by ring]
  exact this

lemma Ys_hasDerivAt (s v : ℝ) :
    HasDerivAt (Ys P s) ((1 - s) * b0 P + s * deriv (Inner.Ytilde P) v) v := by
  have := ((hasDerivAt_id v).const_mul ((1 - s) * b0 P)).add
    ((Ytilde_hasDerivAt P v).const_mul s)
  rw [show (1 - s) * b0 P + s * deriv (Inner.Ytilde P) v =
    (1 - s) * b0 P * 1 + s * deriv (Inner.Ytilde P) v by ring]
  exact this

lemma Xs_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Xs P p.1 p.2) := by
  unfold Xs
  exact (((contDiff_const.sub contDiff_fst).mul contDiff_const).mul contDiff_snd).add
    (contDiff_fst.mul ((Inner.Xtilde_smooth P).comp contDiff_snd))

lemma Ys_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Ys P p.1 p.2) := by
  unfold Ys
  exact (((contDiff_const.sub contDiff_fst).mul contDiff_const).mul contDiff_snd).add
    (contDiff_fst.mul ((Inner.Ytilde_smooth P).comp contDiff_snd))

theorem Fs_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Fs P p.1 p.2) := by
  unfold Fs
  have hX : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Xs P p.1 p.2.re) :=
    (Xs_contDiff P).comp (contDiff_fst.prodMk (reCLM.contDiff.comp contDiff_snd))
  have hY : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Ys P p.1 p.2.im) :=
    (Ys_contDiff P).comp (contDiff_fst.prodMk (imCLM.contDiff.comp contDiff_snd))
  exact (ofRealCLM.contDiff.comp hX).add ((ofRealCLM.contDiff.comp hY).mul contDiff_const)

theorem Js_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Js P p.1 p.2) := by
  unfold Js
  have hX := Inner.contDiff_deriv_Xtilde P
  have hY := Inner.contDiff_deriv_Ytilde P
  exact (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul (hX.comp (reCLM.contDiff.comp contDiff_snd)))).mul
    (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul (hY.comp (imCLM.contDiff.comp contDiff_snd))))

lemma Js_slice_contDiff (s : ℝ) : ContDiff ℝ ∞ (Js P s) :=
  (Js_contDiff P).comp (contDiff_const.prodMk contDiff_id)

/-- The derivative of a "product" map `w ↦ X(Re w) + i Y(Im w)`. -/
theorem hasFDerivAt_prod_map {X Y : ℝ → ℝ} {dx dy : ℝ} {w : ℂ} (hX : HasDerivAt X dx w.re)
    (hY : HasDerivAt Y dy w.im) :
    HasFDerivAt (fun w : ℂ => (X w.re : ℂ) + (Y w.im : ℂ) * I)
      (ofRealCLM.comp (dx • reCLM) + (ofRealCLM.comp (dy • imCLM)).smulRight I) w := by
  have h1 : HasFDerivAt (fun w : ℂ => (X w.re : ℂ)) (ofRealCLM.comp (dx • reCLM)) w := by
    have := (hX.hasFDerivAt.comp w reCLM.hasFDerivAt)
    refine (ofRealCLM.hasFDerivAt.comp w this).congr_fderiv ?_
    ext1 z; simp; ring
  have h2 : HasFDerivAt (fun w : ℂ => (Y w.im : ℂ)) (ofRealCLM.comp (dy • imCLM)) w := by
    have := (hY.hasFDerivAt.comp w imCLM.hasFDerivAt)
    refine (ofRealCLM.hasFDerivAt.comp w this).congr_fderiv ?_
    ext1 z; simp; ring
  refine (h1.add (h2.mul_const I)).congr_fderiv ?_
  ext1 z; simp; ring

/-- `det D(X(Re w) + i Y(Im w)) = X' Y'`. -/
theorem det_prod_map {X Y : ℝ → ℝ} {dx dy : ℝ} {w : ℂ} (hX : HasDerivAt X dx w.re)
    (hY : HasDerivAt Y dy w.im) :
    LinearMap.det (fderiv ℝ (fun w : ℂ => (X w.re : ℂ) + (Y w.im : ℂ) * I) w : ℂ →ₗ[ℝ] ℂ) =
      dx * dy := by
  rw [(hasFDerivAt_prod_map hX hY).fderiv, Inner.det_eq_re_im]
  simp

theorem Fs_det (s : ℝ) (w : ℂ) :
    LinearMap.det (fderiv ℝ (Fs P s) w : ℂ →ₗ[ℝ] ℂ) = Js P s w :=
  det_prod_map (Xs_hasDerivAt P s w.re) (Ys_hasDerivAt P s w.im)

/-! ### Positivity and area growth (`lem:pll-density-area`) -/

/-- **`lem:pll-density-area` (a), expansion.** -/
theorem Js_expand (s : ℝ) (w : ℂ) :
    Js P s w = (1 - s) ^ 2 * j0 P +
      s * (1 - s) * (a0 P * deriv (Inner.Ytilde P) w.im + b0 P * deriv (Inner.Xtilde P) w.re) +
      s ^ 2 * Inner.Jmor P w := by
  simp only [Js, Inner.Jmor, j0, Inner.j0]; ring

/-- `J_s ≥ (1 - s)² j₀ + s² J₁` for `s ∈ [0, 1]`. -/
theorem Js_ge {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (w : ℂ) :
    (1 - s) ^ 2 * j0 P + s ^ 2 * Inner.Jmor P w ≤ Js P s w := by
  rw [Js_expand]
  have h1 : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (by linarith [hs.2])
  have h2 : 0 ≤ a0 P * deriv (Inner.Ytilde P) w.im + b0 P * deriv (Inner.Xtilde P) w.re :=
    add_nonneg (mul_pos (a0_pos P) (Inner.Ytilde_deriv_pos P _)).le
      (mul_pos (b0_pos P) (Inner.Xtilde_deriv_pos P _)).le
  nlinarith

/-- **`lem:pll-density-area` (a).** `J_s > 0` for `s ∈ [0, 1]`. -/
theorem Js_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (w : ℂ) : 0 < Js P s w := by
  have hX := Inner.Xtilde_deriv_pos P w.re
  have hY := Inner.Ytilde_deriv_pos P w.im
  have ha := a0_pos P; have hb := b0_pos P
  have h1 : 0 < (1 - s) * a0 P + s * deriv (Inner.Xtilde P) w.re := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; simpa using ha
    · nlinarith [hs.2]
  have h2 : 0 < (1 - s) * b0 P + s * deriv (Inner.Ytilde P) w.im := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; simpa using hb
    · nlinarith [hs.2]
  exact mul_pos h1 h2

/-- **`lem:pll-density-area` (b).** `J_s(w) = j₀` for `|w| ≤ ρ_T`, every `s ∈ ℝ`. -/
theorem Js_zero (s : ℝ) {w : ℂ} (hw : ‖w‖ ≤ Inner.rhoT P) : Js P s w = j0 P := by
  have hu : |w.re| ≤ Inner.uEps P := (abs_re_le_norm w).trans (hw.trans (min_le_left _ _))
  have hv : |w.im| ≤ Inner.vEps P := (abs_im_le_norm w).trans (hw.trans (min_le_right _ _))
  rw [Js, Inner.Xtilde_deriv_closed P hu, Inner.Ytilde_deriv_closed P hv]
  simp only [j0, Inner.j0]; ring

/-- `J₀ ≡ j₀`. -/
theorem Js_at_zero (w : ℂ) : Js P 0 w = j0 P := by simp [Js, j0, Inner.j0]

/-- `J₁ = X̃' Ỹ'`. -/
theorem Js_at_one : Js P 1 = Inner.Jmor P := by
  funext w; simp [Js, Inner.Jmor]

theorem Fs_at_one : Fs P 1 = Inner.Fmor P := by
  funext w; simp [Fs, Xs, Ys, Inner.Fmor]

theorem Fs_at_zero (w : ℂ) : Fs P 0 w = (a0 P * w.re : ℝ) + (b0 P * w.im : ℝ) * I := by
  simp [Fs, Xs, Ys]

/-! ### Circle averages: generic tools -/

theorem Jbar_continuous_of {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) :
    Continuous (Inner.Jbar J s) := by
  unfold Inner.Jbar
  refine continuous_const.mul ?_
  have hR := Inner.contDiff_Rot.continuous
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hc.comp (hR.comp (continuous_snd.prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst))))

/-- A lower bound `c ≤ J_s` passes to `J̄_s`. -/
theorem Jbar_ge_of {J : ℝ → ℂ → ℝ} {s c : ℝ} (hc : Continuous (J s)) (hJ : ∀ w, c ≤ J s w)
    (t : ℝ) : c ≤ Inner.Jbar J s t := by
  unfold Inner.Jbar
  have : ∫ φ in (0 : ℝ)..2 * π, c ≤ ∫ φ in (0 : ℝ)..2 * π, J s (Inner.Rot φ (√t : ℂ)) :=
    intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
      ((hc.comp (Inner.continuous_Rot_left _)).intervalIntegrable _ _) fun φ _ => hJ _
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  have hpi := Real.pi_pos
  calc c = (2 * π)⁻¹ * (2 * π * c) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-- A lower bound `c ≤ J_s` gives `π c E ≤ 𝓐_s(E)` for `E ≥ 0`. -/
theorem Acal_ge_of {J : ℝ → ℂ → ℝ} {s c : ℝ} (hc : Continuous (J s)) (hJ : ∀ w, c ≤ J s w)
    {E : ℝ} (hE : 0 ≤ E) : π * c * E ≤ Inner.Acal J s E := by
  unfold Inner.Acal
  have : ∫ t in (0 : ℝ)..E, c ≤ ∫ t in (0 : ℝ)..E, Inner.Jbar J s t :=
    intervalIntegral.integral_mono_on hE intervalIntegrable_const
      ((Jbar_continuous_of hc).intervalIntegrable _ _) fun t _ => Jbar_ge_of hc hJ t
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  nlinarith [Real.pi_pos]

/-- Linear lower bound for `J̄_s`: `J̄_s ≥ (1-s)² j₀ + s² J̄₁`. -/
theorem Jbar_Js_ge {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (1 - s) ^ 2 * j0 P + s ^ 2 * Inner.Jbar (Inner.JmorF P) 0 t ≤ Inner.Jbar (Js P) s t := by
  unfold Inner.Jbar
  have hJm := Inner.Jmor_smooth P |>.continuous
  have hJs := (Js_slice_contDiff P s).continuous
  set g : ℝ → ℂ := fun φ => Inner.Rot φ (√t : ℂ)
  have hg : Continuous g := Inner.continuous_Rot_left _
  have hint1 : IntervalIntegrable (fun φ => Inner.Jmor P (g φ)) MeasureTheory.volume 0 (2 * π) :=
    (hJm.comp hg).intervalIntegrable _ _
  have hmono : ∫ φ in (0 : ℝ)..2 * π, ((1 - s) ^ 2 * j0 P + s ^ 2 * Inner.Jmor P (g φ)) ≤
      ∫ φ in (0 : ℝ)..2 * π, Js P s (g φ) :=
    intervalIntegral.integral_mono_on (by positivity)
      (intervalIntegrable_const.add (hint1.const_mul _))
      ((hJs.comp hg).intervalIntegrable _ _) fun φ _ => Js_ge P hs _
  rw [intervalIntegral.integral_add intervalIntegrable_const (hint1.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
    sub_zero] at hmono
  have hpi := Real.pi_pos
  have : (2 * π)⁻¹ * (2 * π * ((1 - s) ^ 2 * j0 P) +
      s ^ 2 * ∫ φ in (0 : ℝ)..2 * π, Inner.Jmor P (g φ)) =
      (1 - s) ^ 2 * j0 P + s ^ 2 * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, Inner.Jmor P (g φ)) := by
    field_simp
  simp only [Inner.JmorF]
  rw [← this]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **`lem:pll-density-area` (c).** For `s ∈ [0, 1]` and `E ≥ 0`:
`𝓐_s(E) ≥ [K₀(1-s)² + s²] E - s² d₀ ≥ κ E - d₀`. -/
theorem As_ge {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {E : ℝ} (hE : 0 ≤ E) :
    (K0 P * (1 - s) ^ 2 + s ^ 2) * E - s ^ 2 * P.d0 ≤ As P s E ∧
      kappa P * E - P.d0 ≤ (K0 P * (1 - s) ^ 2 + s ^ 2) * E - s ^ 2 * P.d0 := by
  have hJs := (Js_slice_contDiff P s).continuous
  have h1 : ∫ t in (0 : ℝ)..E, ((1 - s) ^ 2 * j0 P + s ^ 2 * Inner.Jbar (Inner.JmorF P) 0 t) ≤
      ∫ t in (0 : ℝ)..E, Inner.Jbar (Js P) s t :=
    intervalIntegral.integral_mono_on hE
      (intervalIntegrable_const.add
        (((Inner.Jbar_JmorF_continuous P 0).intervalIntegrable _ _).const_mul _))
      ((Jbar_continuous_of hJs).intervalIntegrable _ _) fun t _ => Jbar_Js_ge P hs t
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (((Inner.Jbar_JmorF_continuous P 0).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
    sub_zero] at h1
  have hA1 := Inner.Acal_ge P 0 hE
  have hA1' : E - P.d0 ≤ π * ∫ t in (0 : ℝ)..E, Inner.Jbar (Inner.JmorF P) 0 t := hA1
  have hAs : As P s E = π * ∫ t in (0 : ℝ)..E, Inner.Jbar (Js P) s t := rfl
  have hpi := Real.pi_pos
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hs21 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  refine ⟨?_, ?_⟩
  · rw [hAs]
    have : π * (E * ((1 - s) ^ 2 * j0 P) +
        s ^ 2 * ∫ t in (0 : ℝ)..E, Inner.Jbar (Inner.JmorF P) 0 t) ≤
        π * ∫ t in (0 : ℝ)..E, Inner.Jbar (Js P) s t := mul_le_mul_of_nonneg_left h1 hpi.le
    have h3 : s ^ 2 * (E - P.d0) ≤
        s ^ 2 * (π * ∫ t in (0 : ℝ)..E, Inner.Jbar (Inner.JmorF P) 0 t) :=
      mul_le_mul_of_nonneg_left hA1' hs2
    unfold K0
    nlinarith
  · have hk := kappa_le P s
    have := P.d0_nonneg
    nlinarith

/-- The constant family `t ↦ J_s` satisfies the normalisation hypotheses for `s ∈ [0, 1]`. -/
theorem JsC_flat {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Inner.FlatDensity (JsC P s) (-1) 1 (j0 P) (Inner.rhoT P) where
  smooth := (Js_slice_contDiff P s).comp contDiff_snd
  pos := fun _ _ w => Js_pos P hs w
  flat := fun _ _ _ hw => Js_zero P s hw
  j_pos := j0_pos P
  ρ₀_pos := Inner.rhoT_pos P
  tendsto := fun _ _ => by
    have hlin : Tendsto (fun E : ℝ => kappa P * E - P.d0) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (kappa_pos P))
    refine tendsto_atTop_mono' _ ?_ hlin
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with E hE
    have := As_ge P hs hE
    exact this.2.trans this.1

lemma zero_mem_Ioo : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-! ### Each `f_s` (`lem:pln-energy`, fixed `s`) -/

lemma fs_eq_const (s : ℝ) (z : ℂ) :
    fs P s z = Fs P s (Inner.TrotInv (JsC P s) 0 (Inner.Darea (JsC P s) 0 z)) := rfl

/-- **`lem:pln-energy`.** For `s ∈ [0, 1]`, `f_s` is `C^∞` on the plane, `det Df_s = 1`, and
`f_s(z) = F_s(z/√j₀)` for `|z| ≤ √j₀ ρ_T`. -/
theorem fs_fixed {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fs P s) ∧ (∀ z, LinearMap.det (fderiv ℝ (fs P s) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ √(j0 P) * Inner.rhoT P → fs P s z = Fs P s (z / (√(j0 P) : ℂ))) :=
  Inner.normalize_smooth_of_const (JsC_flat P hs) zero_mem_Ioo
    ((Fs_contDiff P).comp (contDiff_const.prodMk contDiff_id)) (fun w => Fs_det P s w)

theorem fs_contDiff {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ContDiff ℝ ∞ (fs P s) :=
  (fs_fixed P hs).1

/-- **`lem:pln-energy`.** `f_s` is symplectic: `det Df_s = 1`. -/
theorem fs_symplectic {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : ℂ) :
    LinearMap.det (fderiv ℝ (fs P s) z : ℂ →ₗ[ℝ] ℂ) = 1 :=
  (fs_fixed P hs).2.1 z

/-- `T_s⁻¹ D_s z` has `|·|² = E_s(π|z|²)`. -/
theorem fs_level {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : ℂ) :
    ‖Inner.TrotInv (Js P) s (Inner.Darea (Js P) s z)‖ ^ 2 = Es P s (π * ‖z‖ ^ 2) :=
  Inner.normalize_circle (JsC_flat P hs) zero_mem_Ioo z

/-- `f_s(z) = (X_s(u), Y_s(v))` with `(u, v) = T_s⁻¹ D_s z`. -/
lemma fs_re (s : ℝ) (z : ℂ) :
    (fs P s z).re = Xs P s (Inner.TrotInv (Js P) s (Inner.Darea (Js P) s z)).re := by
  simp [fs, Fs]

lemma fs_im (s : ℝ) (z : ℂ) :
    (fs P s z).im = Ys P s (Inner.TrotInv (Js P) s (Inner.Darea (Js P) s z)).im := by
  simp [fs, Fs]

theorem Xs_strictMono {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : StrictMono (Xs P s) := by
  refine strictMono_of_hasDerivAt_pos (Xs_hasDerivAt P s) fun u => ?_
  have := Inner.Xtilde_deriv_pos P u; have := a0_pos P
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h]; simpa
  · nlinarith [hs.2]

theorem Ys_strictMono {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : StrictMono (Ys P s) := by
  refine strictMono_of_hasDerivAt_pos (Ys_hasDerivAt P s) fun v => ?_
  have := Inner.Ytilde_deriv_pos P v; have := b0_pos P
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h]; simpa
  · nlinarith [hs.2]

/-- **`lem:pln-energy`.** `f_s` is injective (`s ∈ [0, 1]`). -/
theorem fs_injective {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Function.Injective (fs P s) := by
  have hJ := JsC_flat P hs
  have hF : Function.Injective (Fs P s) := by
    intro w₁ w₂ h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Fs, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_zero, add_im, mul_im, zero_add, add_zero] at h1 h2
    exact Complex.ext ((Xs_strictMono P hs).injective (by simpa using h1))
      ((Ys_strictMono P hs).injective (by simpa using h2))
  have hT : Function.Injective (Inner.TrotInv (JsC P s) 0) := fun a b h => by
    rw [← Inner.Trot_TrotInv hJ zero_mem_Ioo a, h, Inner.Trot_TrotInv hJ zero_mem_Ioo b]
  exact hF.comp (hT.comp (Inner.Darea_bijective hJ zero_mem_Ioo).1)

/-- `𝐋` as a continuous linear map. -/
def Lclm : ℂ →L[ℝ] ℂ :=
  ofRealCLM.comp (Inner.cx P • reCLM) + (ofRealCLM.comp (Inner.cy P • imCLM)).smulRight I

lemma Lclm_apply (z : ℂ) : Lclm P z = Lmap P z := by
  simp [Lclm, Lmap]

/-- **`lem:pln-energy`.** `f₀ = 𝐋`. -/
theorem fs_eq_L_at_zero : fs P 0 = Lmap P := by
  funext z
  -- `J₀ ≡ j₀` is flat on every disk; use the constant family with a large flat radius.
  set ρ := ‖z‖ / √(j0 P) + 1
  have hsj : 0 < √(j0 P) := Real.sqrt_pos.2 (j0_pos P)
  have hρ : 0 < ρ := by positivity
  have hJ : Inner.FlatDensity (JsC P 0) (-1) 1 (j0 P) ρ :=
    { smooth := (Js_slice_contDiff P 0).comp contDiff_snd
      pos := fun _ _ w => Js_pos P ⟨le_rfl, zero_le_one⟩ w
      flat := fun _ _ w _ => Js_at_zero P w
      j_pos := j0_pos P
      ρ₀_pos := hρ
      tendsto := (JsC_flat P ⟨le_rfl, zero_le_one⟩).tendsto }
  have hz : ‖z‖ ≤ √(j0 P) * ρ := by
    have : √(j0 P) * ρ = ‖z‖ + √(j0 P) := by simp only [ρ]; field_simp
    rw [this]; linarith
  rw [fs_eq_const, Inner.normalize_eq_of_const hJ zero_mem_Ioo (Fs P 0) hz, Fs_at_zero]
  have hre : (z / (√(j0 P) : ℂ)).re = z.re / √(j0 P) := by simp [Complex.div_ofReal_re]
  have him : (z / (√(j0 P) : ℂ)).im = z.im / √(j0 P) := by simp [Complex.div_ofReal_im]
  rw [hre, him, Lmap, Inner.cx, Inner.cy]
  congr 2 <;> ring_nf

/-- **`lem:pln-energy`.** `f₁ = f`. -/
theorem fs_eq_finner : fs P 1 = Inner.finner P := by
  funext z
  have h : JsC P 1 = Inner.JmorF P := by
    funext t w; simp [JsC, Inner.JmorF, Js_at_one]
  rw [fs_eq_const, h, Fs_at_one]; rfl

end SymplecticPacking.Qhat
