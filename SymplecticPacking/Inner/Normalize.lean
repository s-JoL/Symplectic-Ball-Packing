import Mathlib
import SymplecticPacking.Explicit
import SymplecticPacking.Inner.Inverse
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy

/-!
# Rotation and area normalisations

`sec:pln-normalisation-maps`: the rotation and area normalisations (paper `def:pln-normalisations`,
`lem:pln-rotation` (i)–(iii), `lem:pln-area` (non-analytic parts), in parametric form).

We work parametrically from the start: a density family `J : ℝ → ℂ → ℝ`, `s ↦ J s`; the
one-density case is the constant family. The plane is `ℂ`, `Rot φ w = exp(φ i) w`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology Set Metric Complex
open scoped ContDiff Real

/-! ### Definitions (`def:pln-normalisations`) -/

/-- The rotation `Rot_φ w = exp(φ i) w`. -/
def Rot (φ : ℝ) (w : ℂ) : ℂ := Complex.exp (φ * I) * w

/-- The circle average `J̄_s(t) = (2π)⁻¹ ∫₀^{2π} J_s(Rot_φ √t) dφ`. For `t < 0` this is `J_s(0)`
(since `√t = 0`), which is the constant extension of the paper under the flatness hypothesis
(`Jbar_eq_of_le`). -/
def Jbar (J : ℝ → ℂ → ℝ) (s t : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, J s (Rot φ (Real.sqrt t : ℂ))

/-- The circle average through `w`, `(2π)⁻¹ ∫₀^{2π} J_s(Rot_φ w) dφ`; equals `J̄_s(|w|²)`
(`Jbar_normSq`). Auxiliary, smooth in Cartesian coordinates. -/
def Jcirc (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, J s (Rot φ w)

/-- The weighted mean `𝓜_s(w) = (2π)⁻¹ ∫₀^{2π} (φ - π) J_s(Rot_φ w) dφ`. -/
def Bfun (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, (φ - π) * J s (Rot φ w)

/-- The rotation normalisation `T(w) = Rot_{𝓜(w)/J̄(|w|²)} w`. -/
def Trot (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : ℂ := Rot (Bfun J s w / Jbar J s (‖w‖ ^ 2)) w

/-- `𝓐_s(E) = π ∫₀^E J̄_s(t) dt` (the paper defines `𝓐` as the area integral
`∫_{|w|² ≤ E} J`, equal to this formula by the first statement of `lem:pln-area`; only the
formula is used here).
For `E < 0` this is `π J_s(0) E`. -/
def Acal (J : ℝ → ℂ → ℝ) (s E : ℝ) : ℝ := π * ∫ t in (0 : ℝ)..E, Jbar J s t

/-- `E_J = 𝓐_J⁻¹`. -/
def Einv (J : ℝ → ℂ → ℝ) (s : ℝ) : ℝ → ℝ := invR (Acal J s)

/-- The area normalisation `D(z) = √(π E/I) z`, `I = π|z|²`, `E = E_J(I)`; `D(0) = 0`
(automatic, as `x / 0 = 0`). -/
def Darea (J : ℝ → ℂ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (π * Einv J s (π * ‖z‖ ^ 2) / (π * ‖z‖ ^ 2)) : ℂ) * z

/-- Hypotheses on the density family: jointly `C^∞`, positive on `Ioo s₁ s₂ × ℂ`, equal to the
constant `j` on `|w| ≤ ρ₀`, and with `𝓐_s → ∞`. -/
structure FlatDensity (J : ℝ → ℂ → ℝ) (s₁ s₂ j ρ₀ : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2)
  pos : ∀ s ∈ Ioo s₁ s₂, ∀ w, 0 < J s w
  flat : ∀ s ∈ Ioo s₁ s₂, ∀ w : ℂ, ‖w‖ ≤ ρ₀ → J s w = j
  j_pos : 0 < j
  ρ₀_pos : 0 < ρ₀
  tendsto : ∀ s ∈ Ioo s₁ s₂, Tendsto (Acal J s) atTop atTop

/-! ### Generic tools -/

/-- The determinant of an `ℝ`-linear endomorphism of `ℂ`. -/
theorem det_eq_re_im (L : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det L = (L 1).re * (L I).im - (L 1).im * (L I).re := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]
  ring

theorem norm_Rot (φ : ℝ) (w : ℂ) : ‖Rot φ w‖ = ‖w‖ := by
  simp [Rot, Complex.norm_exp_ofReal_mul_I]

theorem Rot_add (φ ψ : ℝ) (w : ℂ) : Rot φ (Rot ψ w) = Rot (φ + ψ) w := by
  simp only [Rot, ofReal_add, add_mul, Complex.exp_add]; ring

theorem Rot_two_pi_add (φ : ℝ) (w : ℂ) : Rot (φ + 2 * π) w = Rot φ w := by
  simp only [Rot, ofReal_add, add_mul, Complex.exp_add, ofReal_mul, ofReal_ofNat]
  rw [Complex.exp_two_pi_mul_I, mul_one]

theorem Rot_zero (w : ℂ) : Rot 0 w = w := by simp [Rot]

theorem contDiff_Rot : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Rot p.1 p.2) := by
  unfold Rot
  exact ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const).cexp.mul contDiff_snd

theorem continuous_Rot_left (w : ℂ) : Continuous (fun φ : ℝ => Rot φ w) :=
  contDiff_Rot.continuous.comp (continuous_id.prodMk continuous_const)

/-- Rotation invariance of circle integrals. -/
theorem integral_Rot_shift (g : ℂ → ℝ) (a : ℝ) (w : ℂ) :
    ∫ φ in (0 : ℝ)..2 * π, g (Rot φ (Rot a w)) = ∫ φ in (0 : ℝ)..2 * π, g (Rot φ w) := by
  have hper : Function.Periodic (fun φ => g (Rot φ w)) (2 * π) := fun φ => by
    simp only [Rot_two_pi_add]
  simp_rw [Rot_add]
  rw [intervalIntegral.integral_comp_add_right (fun φ => g (Rot φ w)), zero_add,
    add_comm (2 * π) a, hper.intervalIntegral_add_eq a 0, zero_add]

theorem Rot_arg (w : ℂ) : Rot (Complex.arg w) (‖w‖ : ℂ) = w := by
  rw [Rot, mul_comm]; exact Complex.norm_mul_exp_arg_mul_I w

/-- `J̄_s(|w|²) = (2π)⁻¹ ∫ J_s(Rot_φ w)`. -/
theorem Jbar_normSq (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : Jbar J s (‖w‖ ^ 2) = Jcirc J s w := by
  unfold Jbar Jcirc
  rw [Real.sqrt_sq (norm_nonneg w)]
  conv_rhs => rw [← Rot_arg w]
  rw [integral_Rot_shift (J s)]

theorem Jcirc_Rot (J : ℝ → ℂ → ℝ) (s a : ℝ) (w : ℂ) : Jcirc J s (Rot a w) = Jcirc J s w := by
  unfold Jcirc; rw [integral_Rot_shift (J s)]

/-- Rescaling `[0, 2π]` to `[0, 1]`. -/
theorem circle_integral_eq_unit (f : ℝ → ℝ) :
    (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, f φ = ∫ t in (0 : ℝ)..1, f (2 * π * t) := by
  rw [intervalIntegral.integral_comp_mul_left f (by positivity : (2 * π) ≠ 0), mul_zero, mul_one,
    smul_eq_mul]

theorem Jcirc_eq_unit (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) :
    Jcirc J s w = ∫ t in (0 : ℝ)..1, J s (Rot (2 * π * t) w) :=
  circle_integral_eq_unit (fun φ => J s (Rot φ w))

theorem Bfun_eq_unit (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) :
    Bfun J s w = ∫ t in (0 : ℝ)..1, (2 * π * t - π) * J s (Rot (2 * π * t) w) :=
  circle_integral_eq_unit (fun φ => (φ - π) * J s (Rot φ w))

section smooth
variable {J : ℝ → ℂ → ℝ} (hJ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2))
include hJ

theorem contDiff_slice (s : ℝ) : ContDiff ℝ ∞ (J s) :=
  hJ.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_circ_integrand :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℂ) => J q.2.1 (Rot (2 * π * q.1) q.2.2)) :=
  hJ.comp (contDiff_snd.fst.prodMk
    (contDiff_Rot.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd.snd)))

/-- `(s, w) ↦ J̄_s(|w|²)` is jointly `C^∞`. -/
theorem contDiff_Jcirc : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Jcirc J p.1 p.2) := by
  simp_rw [Jcirc_eq_unit]
  exact OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral
    (contDiff_circ_integrand hJ)

/-- `(s, w) ↦ 𝓜_s(w)` is jointly `C^∞`. -/
theorem contDiff_Bfun : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Bfun J p.1 p.2) := by
  simp_rw [Bfun_eq_unit]
  exact OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral
    (((contDiff_const.mul contDiff_fst).sub contDiff_const).mul (contDiff_circ_integrand hJ))

end smooth

theorem Jcirc_pos {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
    (w : ℂ) : 0 < Jcirc J s w := by
  unfold Jcirc
  have : 0 < ∫ φ in (0 : ℝ)..2 * π, J s (Rot φ w) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hc.comp (continuous_Rot_left w)).intervalIntegrable _ _) (fun φ _ => hp _)
      (by positivity)
  positivity

theorem Jbar_pos {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
    (t : ℝ) : 0 < Jbar J s t := by
  unfold Jbar
  have : 0 < ∫ φ in (0 : ℝ)..2 * π, J s (Rot φ (Real.sqrt t : ℂ)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hc.comp (continuous_Rot_left _)).intervalIntegrable _ _) (fun φ _ => hp _)
      (by positivity)
  positivity

theorem Trot_eq (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) :
    Trot J s w = Rot (Bfun J s w / Jcirc J s w) w := by
  rw [Trot, Jbar_normSq]

theorem norm_Trot (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : ‖Trot J s w‖ = ‖w‖ := norm_Rot _ _

/-! ### Flat densities near the origin (`sec:pln-normalisation-maps` (i), (ii)) -/

section flat
variable {J : ℝ → ℂ → ℝ} {s j ρ₀ : ℝ} (hflat : ∀ w : ℂ, ‖w‖ ≤ ρ₀ → J s w = j)
include hflat

theorem Jcirc_eq_of_le {w : ℂ} (hw : ‖w‖ ≤ ρ₀) : Jcirc J s w = j := by
  unfold Jcirc
  rw [intervalIntegral.integral_congr (g := fun _ => j)
    (fun φ _ => hflat _ (by rw [norm_Rot]; exact hw))]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; field_simp

theorem Bfun_eq_zero_of_le {w : ℂ} (hw : ‖w‖ ≤ ρ₀) : Bfun J s w = 0 := by
  unfold Bfun
  rw [intervalIntegral.integral_congr (g := fun φ => (φ - π) * j)
    (fun φ _ => by rw [hflat _ (by rw [norm_Rot]; exact hw)])]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]; ring

/-- `J̄_s(t) = j` for `t ≤ ρ₀²` (for `t < 0` this is the constant extension). -/
theorem Jbar_eq_of_le {t : ℝ} (ht : t ≤ ρ₀ ^ 2) (hρ : 0 ≤ ρ₀) : Jbar J s t = j := by
  have hn : ‖(Real.sqrt t : ℂ)‖ ≤ ρ₀ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt t ≤ Real.sqrt (ρ₀ ^ 2) := Real.sqrt_le_sqrt ht
      _ = ρ₀ := Real.sqrt_sq hρ
  have := Jcirc_eq_of_le hflat hn
  unfold Jcirc at this
  exact this

theorem Trot_eq_id_of_const {w : ℂ} (hw : ‖w‖ ≤ ρ₀) : Trot J s w = w := by
  rw [Trot, Bfun_eq_zero_of_le hflat hw, zero_div, Rot_zero]

end flat

/-! ### `lem:pln-rotation` (i): `∂_ψ 𝓜 = J - J̄` -/

theorem Bfun_deriv_arg {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) (w : ℂ) (ψ : ℝ) :
    HasDerivAt (fun ψ => Bfun J s (Rot ψ w)) (J s (Rot ψ w) - Jbar J s (‖w‖ ^ 2)) ψ := by
  set g : ℝ → ℝ := fun φ => J s (Rot φ w)
  have hg : Continuous g := hc.comp (continuous_Rot_left w)
  have hper : Function.Periodic g (2 * π) := fun φ => by simp only [g, Rot_two_pi_add]
  set C := ∫ φ in (0 : ℝ)..2 * π, g φ
  have hf : Continuous (fun φ => (φ - π) * g φ) := (continuous_id.sub continuous_const).mul hg
  set H : ℝ → ℝ := fun u => ∫ φ in (0 : ℝ)..u, (φ - π) * g φ
  have hK : (fun ψ => Bfun J s (Rot ψ w)) =
      fun ψ => (2 * π)⁻¹ * ((H (ψ + 2 * π) - H ψ) - ψ * C) := by
    funext ψ
    unfold Bfun
    congr 1
    simp_rw [Rot_add]
    have e1 := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * π)
      (fun φ => (φ - ψ - π) * g φ) ψ
    simp only [add_sub_cancel_right, zero_add, g] at e1
    rw [e1, add_comm (2 * π) ψ]
    have hi1 : IntervalIntegrable (fun φ => (φ - π) * g φ) MeasureTheory.volume ψ (ψ + 2 * π) :=
      hf.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun φ => ψ * g φ) MeasureTheory.volume ψ (ψ + 2 * π) :=
      (continuous_const.mul hg).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun φ => (φ - π) * g φ - ψ * g φ)
      (fun φ _ => by simp only [g]; ring), intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, hper.intervalIntegral_add_eq ψ 0, zero_add]
    simp only [H, C]
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]
  have hH : ∀ u, HasDerivAt H ((u - π) * g u) u := fun u =>
    (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
  rw [hK]
  have hd := ((((hH (ψ + 2 * π)).comp_add_const ψ (2 * π)).sub (hH ψ)).sub
    ((hasDerivAt_id ψ).mul_const C)).const_mul (2 * π)⁻¹
  convert hd using 1
  · funext y; simp only [Pi.sub_apply, id]
  rw [Jbar_normSq, Jcirc, hper ψ]
  simp only [g, C]
  field_simp
  ring

/-! ### `lem:pln-rotation` (ii): circles, the developed angle, bijectivity -/

/-- The developed angle `Ψ(ψ) = ψ + 𝓜(Rot_ψ w)/J̄(|w|²)` on the circle through `w`. -/
def TrotAngle (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) (ψ : ℝ) : ℝ :=
  ψ + Bfun J s (Rot ψ w) / Jbar J s (‖w‖ ^ 2)

theorem Trot_Rot (J : ℝ → ℂ → ℝ) (s ψ : ℝ) (w : ℂ) :
    Trot J s (Rot ψ w) = Rot (TrotAngle J s w ψ) w := by
  rw [Trot, norm_Rot, Rot_add, TrotAngle, add_comm]

theorem Rot_periodic (w : ℂ) : Function.Periodic (fun φ => Rot φ w) (2 * π) :=
  fun φ => Rot_two_pi_add φ w

theorem Rot_eq_Rot {α β : ℝ} {r : ℂ} (hr : r ≠ 0) (h : Rot α r = Rot β r) :
    ∃ n : ℤ, α = β + n * (2 * π) := by
  have h' := mul_right_cancel₀ hr h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h'
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa using this

/-- Total increase `2π`. -/
theorem TrotAngle_add_two_pi (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) (ψ : ℝ) :
    TrotAngle J s w (ψ + 2 * π) = TrotAngle J s w ψ + 2 * π := by
  simp only [TrotAngle, Rot_two_pi_add]; ring

section circle
variable {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
include hc hp

/-- `Ψ' = J/J̄ > 0`. -/
theorem TrotAngle_hasDerivAt (w : ℂ) (ψ : ℝ) :
    HasDerivAt (TrotAngle J s w) (J s (Rot ψ w) / Jbar J s (‖w‖ ^ 2)) ψ := by
  have hJb := (Jbar_pos hc hp (‖w‖ ^ 2)).ne'
  have := (hasDerivAt_id ψ).add ((Bfun_deriv_arg hc w ψ).div_const (Jbar J s (‖w‖ ^ 2)))
  convert this using 1
  · funext x; simp [TrotAngle]
  · field_simp; ring

theorem TrotAngle_strictMono (w : ℂ) : StrictMono (TrotAngle J s w) :=
  strictMono_of_hasDerivAt_pos (TrotAngle_hasDerivAt hc hp w)
    (fun _ => div_pos (hp _) (Jbar_pos hc hp _))

theorem TrotAngle_continuous (w : ℂ) : Continuous (TrotAngle J s w) :=
  continuous_iff_continuousAt.mpr fun ψ => (TrotAngle_hasDerivAt hc hp w ψ).continuousAt

theorem TrotAngle_inj_aux (r : ℂ) (hr : r ≠ 0) {a₁ a₂ : ℝ} (h12 : a₁ ≤ a₂)
    (h21 : a₂ < a₁ + 2 * π) (h : Rot (TrotAngle J s r a₁) r = Rot (TrotAngle J s r a₂) r) :
    a₁ = a₂ := by
  obtain ⟨n, hn⟩ := Rot_eq_Rot hr h.symm
  have hm := TrotAngle_strictMono hc hp r
  have h1 : TrotAngle J s r a₁ ≤ TrotAngle J s r a₂ := hm.monotone h12
  have h2 : TrotAngle J s r a₂ < TrotAngle J s r a₁ + 2 * π := by
    rw [← TrotAngle_add_two_pi]; exact hm h21
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ n := by
    by_contra hneg; push Not at hneg; nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hge; push Not at hge; nlinarith
  have : n = 0 := by
    have a : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    have b : n < 1 := by exact_mod_cast hn1
    omega
  subst this
  simp at hn
  exact hm.injective hn.symm

/-- **`lem:pln-rotation` (ii).** `T` is a bijection of `ℂ`. -/
theorem Trot_bijective : Function.Bijective (Trot J s) := by
  constructor
  · intro w₁ w₂ h
    have hn : ‖w₁‖ = ‖w₂‖ := by rw [← norm_Trot J s w₁, h, norm_Trot]
    by_cases h0 : ‖w₁‖ = 0
    · have h1 : w₁ = 0 := norm_eq_zero.mp h0
      have h2 : w₂ = 0 := norm_eq_zero.mp (by rw [← hn]; exact h0)
      rw [h1, h2]
    set r : ℂ := (‖w₁‖ : ℂ)
    have hr : r ≠ 0 := by simpa [r] using h0
    have e1 : w₁ = Rot (arg w₁) r := (Rot_arg w₁).symm
    have e2 : w₂ = Rot (arg w₂) r := by
      have := (Rot_arg w₂).symm; rwa [← hn] at this
    rw [e1, e2, Trot_Rot, Trot_Rot] at h
    have hπ1 := neg_pi_lt_arg w₁
    have hπ2 := neg_pi_lt_arg w₂
    have hπ3 := arg_le_pi w₁
    have hπ4 := arg_le_pi w₂
    have : arg w₁ = arg w₂ := by
      rcases le_total (arg w₁) (arg w₂) with h12 | h21
      · exact TrotAngle_inj_aux hc hp r hr h12 (by linarith) h
      · exact (TrotAngle_inj_aux hc hp r hr h21 (by linarith) h.symm).symm
    rw [e1, e2, this]
  · intro y
    by_cases h0 : y = 0
    · exact ⟨0, by simp [h0, Trot, Rot]⟩
    set r : ℂ := (‖y‖ : ℂ)
    have hα := toIcoMod_mem_Ico Real.two_pi_pos (TrotAngle J s r 0) (arg y)
    have hΨ2 : TrotAngle J s r (2 * π) = TrotAngle J s r 0 + 2 * π := by
      simpa using TrotAngle_add_two_pi J s r 0
    obtain ⟨ψ, -, hψ⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 2 * π)
      (TrotAngle_continuous hc hp r).continuousOn
      ⟨hα.1, by have := hα.2; rw [← hΨ2] at this; exact this.le⟩
    refine ⟨Rot ψ r, ?_⟩
    rw [Trot_Rot, hψ, toIcoMod, (Rot_periodic r).sub_zsmul_eq]
    exact Rot_arg y

end circle

/-! ### `lem:pln-rotation` (iii): the pullback identity -/

/-- The angle `ϑ_T` written with the Cartesian circle average. -/
def thetaC (J : ℝ → ℂ → ℝ) (s : ℝ) (w : ℂ) : ℝ := Bfun J s w / Jcirc J s w

theorem Trot_eq_thetaC (J : ℝ → ℂ → ℝ) (s : ℝ) : Trot J s = fun w => Rot (thetaC J s w) w := by
  funext w; rw [Trot_eq, thetaC]

/-- Directional derivative of `w ↦ Rot (θ w) w`. -/
theorem hasDerivAt_Rot_line {θ : ℂ → ℝ} {ℓ : ℂ →L[ℝ] ℝ} {w : ℂ} (hθ : HasFDerivAt θ ℓ w)
    (v : ℂ) :
    HasDerivAt (fun t : ℝ => Rot (θ (w + t • v)) (w + t • v))
      (Complex.exp (θ w * I) * ((ℓ v : ℂ) * I) * w + Complex.exp (θ w * I) * v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hθ0 : HasFDerivAt θ ℓ (w + (0 : ℝ) • v) := by simpa using hθ
  have hg : HasDerivAt (fun t : ℝ => θ (w + t • v)) (ℓ v) 0 := hθ0.comp_hasDerivAt (0 : ℝ) hl
  have he := (hg.ofReal_comp.mul_const I).cexp
  have := he.mul hl
  convert this using 1
  · funext t; simp [Rot]
  · simp

theorem hasDerivAt_Rot_left (w : ℂ) : HasDerivAt (fun ψ : ℝ => Rot ψ w) (I * w) 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).cexp.mul_const w
  simpa [Rot] using this

/-- The determinant of `D(w ↦ Rot (θ w) w)` is `1 + Dθ(w)(i w)`. -/
theorem det_fderiv_Rot_theta {θ : ℂ → ℝ} {w : ℂ} (hθ : DifferentiableAt ℝ θ w) :
    LinearMap.det (fderiv ℝ (fun w => Rot (θ w) w) w : ℂ →ₗ[ℝ] ℂ) =
      1 + fderiv ℝ θ w (I * w) := by
  set ℓ := fderiv ℝ θ w
  have hθ' : HasFDerivAt θ ℓ w := hθ.hasFDerivAt
  have hT : DifferentiableAt ℝ (fun w => Rot (θ w) w) w := by
    have : DifferentiableAt ℝ (fun x => ((θ x : ℝ), x)) w := hθ.prodMk differentiableAt_id
    exact (contDiff_Rot.differentiable (by simp) _).comp w this
  have hval : ∀ v, fderiv ℝ (fun w => Rot (θ w) w) w v =
      Complex.exp (θ w * I) * ((ℓ v : ℂ) * I) * w + Complex.exp (θ w * I) * v := by
    intro v
    have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
    have hT0 : HasFDerivAt (fun w => Rot (θ w) w) (fderiv ℝ (fun w => Rot (θ w) w) w)
        (w + (0 : ℝ) • v) := by simpa using hT.hasFDerivAt
    exact (hT0.comp_hasDerivAt (l := fun w => Rot (θ w) w) (0 : ℝ) hl).unique (hasDerivAt_Rot_line hθ' v)
  rw [det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hval, hval]
  have hIw : I * w = (-w.im : ℝ) • (1 : ℂ) + (w.re : ℝ) • I := by
    apply Complex.ext <;> simp
  rw [hIw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  clear_value ℓ
  set e := Complex.exp (θ w * I)
  have he : e.re ^ 2 + e.im ^ 2 = 1 := by
    have h := Complex.norm_exp_ofReal_mul_I (θ w)
    rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply] at h
    rw [← h]; ring
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im, add_re, add_im]
  linear_combination (1 + (-w.im * ℓ 1 + w.re * ℓ I)) * he

theorem contDiff_slice_of {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ → ℂ → G} (hF : ContDiff ℝ ∞ (fun p : ℝ × ℂ => F p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ∞ (F s) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

section pullback
variable {J : ℝ → ℂ → ℝ} {s : ℝ} (hJ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2))
  (hp : ∀ w, 0 < J s w)
include hJ hp

theorem contDiff_thetaC : ContDiff ℝ ∞ (thetaC J s) :=
  (contDiff_slice_of (contDiff_Bfun hJ) s).div (contDiff_slice_of (contDiff_Jcirc hJ) s)
    (fun w => (Jcirc_pos (contDiff_slice hJ s).continuous hp w).ne')

/-- `det DT = J / J̄`. -/
theorem Trot_det (w : ℂ) :
    LinearMap.det (fderiv ℝ (Trot J s) w : ℂ →ₗ[ℝ] ℂ) = J s w / Jbar J s (‖w‖ ^ 2) := by
  have hc := (contDiff_slice hJ s).continuous
  have hθd : DifferentiableAt ℝ (thetaC J s) w :=
    (contDiff_thetaC hJ hp).differentiable (by simp) w
  rw [Trot_eq_thetaC, det_fderiv_Rot_theta hθd]
  have hθ0 : HasFDerivAt (thetaC J s) (fderiv ℝ (thetaC J s) w) (Rot 0 w) := by
    rw [Rot_zero]; exact hθd.hasFDerivAt
  have h1 := hθ0.comp_hasDerivAt (0 : ℝ) (hasDerivAt_Rot_left w)
  have h2 : HasDerivAt (fun ψ => thetaC J s (Rot ψ w))
      ((J s (Rot 0 w) - Jbar J s (‖w‖ ^ 2)) / Jcirc J s w) 0 := by
    have := (Bfun_deriv_arg hc w 0).div_const (Jcirc J s w)
    convert this using 1
    funext ψ; simp only [thetaC, Jcirc_Rot]
  rw [h1.unique h2, Rot_zero, Jbar_normSq]
  have := (Jcirc_pos hc hp w).ne'
  field_simp; ring

end pullback

/-! ### Generic tools: localized parametric integrals, parametric inverses -/

theorem contDiffAt_fixed_integral_local {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {U : Set ℝ} (hU : IsOpen U) {f : ℝ × (ℝ × X) → ℝ}
    (hf : ContDiffOn ℝ ∞ f {q | q.2.1 ∈ U}) {p₀ : ℝ × X} (hp₀ : p₀.1 ∈ U) :
    ContDiffAt ℝ ∞ (fun p : ℝ × X => ∫ t in (0 : ℝ)..1, f (t, p)) p₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hp₀
  let c : ContDiffBump p₀.1 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hO : IsOpen {q : ℝ × (ℝ × X) | q.2.1 ∈ U} := hU.preimage continuous_snd.fst
  have hcs : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × X) => c q.2.1) :=
    (c.contDiff (n := ⊤)).comp contDiff_snd.fst
  have hg : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × X) => c q.2.1 * f q) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2.1 ∈ U
    · exact hcs.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds hq))
    · have hnot : q.2.1 ∉ tsupport c := by
        rw [c.tsupport_eq]
        intro hm
        have hr : c.rOut = ε / 2 := rfl
        rw [hr] at hm
        exact hq (hball (lt_of_le_of_lt (mem_closedBall.mp hm) (by linarith)))
      have h1 := notMem_tsupport_iff_eventuallyEq.mp hnot
      have h2 := (continuous_snd.fst.tendsto q).eventually h1
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [h2] with q' hq'
      simp only [Pi.zero_apply] at hq'
      simp [hq']
  have hI := OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral hg
  apply hI.contDiffAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ p in 𝓝 p₀, p.1 ∈ closedBall p₀.1 (ε / 4) :=
    continuous_fst.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (by positivity))
  filter_upwards [hnear] with p hp
  rw [intervalIntegral.integral_const_mul, c.one_of_mem_closedBall hp, one_mul]

theorem contDiff_slice_of_contDiffOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {G : ℝ → X → Y} {U : Set ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ (fun p : ℝ × X => G p.1 p.2) (U ×ˢ univ)) {s : ℝ} (hs : s ∈ U) :
    ContDiff ℝ ∞ (G s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds
    (show (s, x) ∈ U ×ˢ (univ : Set X) from ⟨hs, mem_univ x⟩))
  exact h.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- **Parametric inverse function theorem.** If `G s` is injective with injective derivative for
`s ∈ U` and `(s, x) ↦ G s x` is `C^∞`, then any right inverse `(s, y) ↦ inv s y` is `C^∞`. -/
theorem contDiffOn_param_inverse {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {G inv : ℝ → X → X} {U : Set ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ (fun p : ℝ × X => G p.1 p.2) (U ×ˢ univ))
    (hinj : ∀ s ∈ U, Function.Injective (G s))
    (hder : ∀ s ∈ U, ∀ x, Function.Injective (fderiv ℝ (G s) x))
    (hinv : ∀ s ∈ U, ∀ y, G s (inv s y) = y) :
    ContDiffOn ℝ ∞ (fun p : ℝ × X => inv p.1 p.2) (U ×ˢ univ) := by
  rintro ⟨s₀, y₀⟩ ⟨hs₀, -⟩
  apply ContDiffAt.contDiffWithinAt
  set x₀ := inv s₀ y₀
  have hO : U ×ˢ (univ : Set X) ∈ 𝓝 (s₀, x₀) := (hU.prod isOpen_univ).mem_nhds ⟨hs₀, mem_univ _⟩
  have hGa : ContDiffAt ℝ ∞ (fun p : ℝ × X => G p.1 p.2) (s₀, x₀) := hG.contDiffAt hO
  set Φ : ℝ × X → ℝ × X := fun p => (p.1, G p.1 p.2)
  have hΦ : ContDiffAt ℝ ∞ Φ (s₀, x₀) := contDiffAt_fst.prodMk hGa
  set D := fderiv ℝ (fun p : ℝ × X => G p.1 p.2) (s₀, x₀)
  have hGd : HasFDerivAt (fun p : ℝ × X => G p.1 p.2) D (s₀, x₀) :=
    (hGa.differentiableAt (by simp)).hasFDerivAt
  have hslice : fderiv ℝ (G s₀) x₀ = D.comp (ContinuousLinearMap.inr ℝ ℝ X) :=
    (hGd.comp x₀ (hasFDerivAt_prodMk_right s₀ x₀)).fderiv
  set Φ' : ℝ × X →L[ℝ] ℝ × X := (ContinuousLinearMap.fst ℝ ℝ X).prod D
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have ha : a = (a.1, 0) + (0, a.2) := by simp
    have hb : b = (b.1, 0) + (0, b.2) := by simp
    rw [ha, hb, map_add, map_add, h1] at h2
    have h3 := add_left_cancel h2
    have h4 : fderiv ℝ (G s₀) x₀ a.2 = fderiv ℝ (G s₀) x₀ b.2 := by
      rw [hslice]; simpa using h3
    exact Prod.ext h1 (hder s₀ hs₀ x₀ h4)
  set E : (ℝ × X) ≃L[ℝ] (ℝ × X) :=
    (LinearEquiv.ofInjectiveEndo (Φ' : (ℝ × X) →ₗ[ℝ] (ℝ × X)) hΦ'inj).toContinuousLinearEquiv
  have hE : (E : ℝ × X →L[ℝ] ℝ × X) = Φ' := by ext v <;> rfl
  have hΦ' : HasFDerivAt Φ (E : ℝ × X →L[ℝ] ℝ × X) (s₀, x₀) := by
    rw [hE]; exact hasFDerivAt_fst.prodMk hGd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Ψ := hΦ.localInverse hΦ' hn
  have hΨs : ContDiffAt ℝ ∞ Ψ (Φ (s₀, x₀)) := hΦ.to_localInverse hΦ' hn
  have hstrict := hΦ.hasStrictFDerivAt' hΦ' hn
  have hright : ∀ᶠ p in 𝓝 (Φ (s₀, x₀)), Φ (Ψ p) = p := hstrict.eventually_right_inverse
  have hpt : Φ (s₀, x₀) = (s₀, y₀) := by simp only [Φ, x₀, hinv s₀ hs₀]
  rw [hpt] at hΨs hright
  apply (contDiffAt_snd.comp (s₀, y₀) hΨs).congr_of_eventuallyEq
  have hU' : ∀ᶠ p : ℝ × X in 𝓝 (s₀, y₀), p.1 ∈ U :=
    continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hs₀)
  filter_upwards [hright, hU'] with p hp hpU
  have hΨ1 : (Ψ p).1 = p.1 := by have := congrArg Prod.fst hp; simpa [Φ] using this
  have hΨ2 : G p.1 (Ψ p).2 = p.2 := by have := congrArg Prod.snd hp; simpa [Φ, hΨ1] using this
  apply hinj p.1 hpU
  simp only [Function.comp_apply]
  rw [hinv p.1 hpU, hΨ2]

/-- A linear endomorphism of `ℂ` with nonzero determinant is injective. -/
theorem injective_of_det_ne_zero (L : ℂ →L[ℝ] ℂ) (h : LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) ≠ 0) :
    Function.Injective L := by
  have hu : IsUnit (L : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit h)
  exact ((Module.End.isUnit_iff _).mp hu).1

/-! ### The inverse rotation -/

open Classical in
/-- `T⁻¹`: the unique preimage under `T` (definite description), `y` itself if there is none. -/
def TrotInv (J : ℝ → ℂ → ℝ) (s : ℝ) (y : ℂ) : ℂ :=
  if h : ∃! w, Trot J s w = y then Explicit.the h else y

theorem TrotInv_eq_of {J : ℝ → ℂ → ℝ} {s : ℝ} (hinj : Function.Injective (Trot J s)) {w y : ℂ}
    (h : Trot J s w = y) : TrotInv J s y = w := by
  have hu : ∃! w, Trot J s w = y := ⟨w, h, fun z hz => hinj (hz.trans h.symm)⟩
  unfold TrotInv
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact Explicit.the_eq hu h

/-! ### Results under the flatness hypothesis -/

namespace FlatDensity
variable {J : ℝ → ℂ → ℝ} {s₁ s₂ j ρ₀ : ℝ} (hJ : FlatDensity J s₁ s₂ j ρ₀)
include hJ

theorem cont {s : ℝ} : Continuous (J s) := (contDiff_slice hJ.smooth s).continuous

theorem bij {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Function.Bijective (Trot J s) :=
  Trot_bijective hJ.cont (hJ.pos s hs)

end FlatDensity

section flatResults
variable {J : ℝ → ℂ → ℝ} {s₁ s₂ j ρ₀ : ℝ} (hJ : FlatDensity J s₁ s₂ j ρ₀)
include hJ

theorem Trot_TrotInv {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (y : ℂ) : Trot J s (TrotInv J s y) = y := by
  obtain ⟨w, hw⟩ := (hJ.bij hs).2 y
  rw [TrotInv_eq_of (hJ.bij hs).1 hw, hw]

theorem TrotInv_Trot {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (w : ℂ) : TrotInv J s (Trot J s w) = w :=
  TrotInv_eq_of (hJ.bij hs).1 rfl

theorem norm_TrotInv {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (y : ℂ) : ‖TrotInv J s y‖ = ‖y‖ := by
  conv_rhs => rw [← Trot_TrotInv hJ hs y]
  rw [norm_Trot]

/-- `T⁻¹(w) = w` for `|w| ≤ ρ₀`. -/
theorem TrotInv_eq_id_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {y : ℂ} (hy : ‖y‖ ≤ ρ₀) :
    TrotInv J s y = y :=
  TrotInv_eq_of (hJ.bij hs).1 (Trot_eq_id_of_const (hJ.flat s hs) hy)

/-- `(s, w) ↦ T_s(w)` is `C^∞` on `Ioo s₁ s₂ × ℂ`. -/
theorem Trot_param_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => Trot J p.1 p.2) (Ioo s₁ s₂ ×ˢ univ) := by
  have he : (fun p : ℝ × ℂ => Trot J p.1 p.2) =
      fun p => Rot (Bfun J p.1 p.2 / Jcirc J p.1 p.2) p.2 := funext fun p => Trot_eq J p.1 p.2
  rw [he]
  exact contDiff_Rot.comp_contDiffOn
    (((contDiff_Bfun hJ.smooth).contDiffOn.div (contDiff_Jcirc hJ.smooth).contDiffOn
      fun p hp => (Jcirc_pos hJ.cont (hJ.pos p.1 hp.1) p.2).ne').prodMk contDiffOn_snd)

/-- **`sec:pln-normalisation-maps` (i).** `T` is `C^∞`. -/
theorem Trot_smooth_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : ContDiff ℝ ∞ (Trot J s) :=
  contDiff_slice_of_contDiffOn isOpen_Ioo (Trot_param_smooth hJ) hs

theorem Trot_det_ne_zero {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (w : ℂ) :
    LinearMap.det (fderiv ℝ (Trot J s) w : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
  rw [Trot_det hJ.smooth (hJ.pos s hs)]
  exact (div_pos (hJ.pos s hs w) (Jbar_pos hJ.cont (hJ.pos s hs) _)).ne'

/-- **`sec:pln-normalisation-maps`, inverse rotation.** `(s, y) ↦ T_s⁻¹(y)` is `C^∞`. -/
theorem TrotInv_param_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => TrotInv J p.1 p.2) (Ioo s₁ s₂ ×ˢ univ) :=
  contDiffOn_param_inverse isOpen_Ioo (Trot_param_smooth hJ) (fun _ hs => (hJ.bij hs).1)
    (fun _ hs w => injective_of_det_ne_zero _ (Trot_det_ne_zero hJ hs w))
    (fun _ hs y => Trot_TrotInv hJ hs y)

/-- **`sec:pln-normalisation-maps` (i).** `T⁻¹` is `C^∞`. -/
theorem TrotInv_smooth_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : ContDiff ℝ ∞ (TrotInv J s) :=
  contDiff_slice_of_contDiffOn isOpen_Ioo (TrotInv_param_smooth hJ) hs

/-! ### `sec:pln-normalisation-maps` (ii), `lem:pln-area`: `J̄`, `𝓐`, `E` -/

/-- `(s, t) ↦ J̄_s(t)` (with the constant extension for `t < 0`) is `C^∞` near `Ioo s₁ s₂ × ℝ`. -/
theorem Jbar_param_contDiffAt {s t : ℝ} (hs : s ∈ Ioo s₁ s₂) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Jbar J p.1 p.2) (s, t) := by
  by_cases ht : 0 < t
  · have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((Real.sqrt p.2 : ℝ) : ℂ)) (s, t) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (s, t)
        ((Real.contDiffAt_sqrt ht.ne').comp (s, t) contDiffAt_snd)
    exact (contDiff_Jcirc hJ.smooth).contDiffAt.comp (s, t) (contDiffAt_fst.prodMk h1)
  · push Not at ht
    have hρ : 0 < ρ₀ ^ 2 := by have := hJ.ρ₀_pos; positivity
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (s, t), p.1 ∈ Ioo s₁ s₂ ∧ p.2 < ρ₀ ^ 2 :=
      (isOpen_Ioo.prod isOpen_Iio).mem_nhds ⟨hs, show t < ρ₀ ^ 2 by linarith⟩
    apply (contDiffAt_const (c := j)).congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    exact Jbar_eq_of_le (hJ.flat p.1 hp.1) hp.2.le hJ.ρ₀_pos.le

theorem Jbar_continuous {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Continuous (Jbar J s) :=
  continuous_iff_continuousAt.mpr fun t =>
    (Jbar_param_contDiffAt hJ (t := t) hs).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)

omit hJ in
theorem Acal_eq_unit (J : ℝ → ℂ → ℝ) (s E : ℝ) :
    Acal J s E = π * (E * ∫ u in (0 : ℝ)..1, Jbar J s (E * u)) := by
  have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (Jbar J s) E
  rw [mul_zero, mul_one, smul_eq_mul] at this
  rw [Acal, this]

/-- `(s, E) ↦ 𝓐_s(E)` is `C^∞` on `Ioo s₁ s₂ × ℝ`. -/
theorem Acal_param_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Acal J p.1 p.2) (Ioo s₁ s₂ ×ˢ univ) := by
  rintro ⟨s, E⟩ ⟨hs, -⟩
  apply ContDiffAt.contDiffWithinAt
  simp_rw [Acal_eq_unit]
  have hf : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => Jbar J q.2.1 (q.2.2 * q.1))
      {q | q.2.1 ∈ Ioo s₁ s₂} := fun q hq =>
    ((Jbar_param_contDiffAt hJ (t := q.2.2 * q.1) hq).comp q
      (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.mul contDiffAt_fst))).contDiffWithinAt
  exact contDiffAt_const.mul (contDiffAt_snd.mul
    (contDiffAt_fixed_integral_local (X := ℝ) isOpen_Ioo hf (p₀ := (s, E)) hs))

/-- `𝓐_s' = π J̄_s`. -/
theorem Acal_hasDerivAt {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (E : ℝ) :
    HasDerivAt (Acal J s) (π * Jbar J s E) E :=
  (((Jbar_continuous hJ hs).integral_hasStrictDerivAt 0 E).hasDerivAt).const_mul π

theorem Acal_deriv_pos {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (E : ℝ) : 0 < π * Jbar J s E :=
  mul_pos Real.pi_pos (Jbar_pos hJ.cont (hJ.pos s hs) E)

theorem Acal_continuous {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Continuous (Acal J s) :=
  continuous_iff_continuousAt.mpr fun E => (Acal_hasDerivAt hJ hs E).continuousAt

theorem Acal_strictMono {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : StrictMono (Acal J s) :=
  strictMono_of_hasDerivAt_pos (Acal_hasDerivAt hJ hs) (Acal_deriv_pos hJ hs)

/-- `𝓐_s(E) = π j E` for `E ≤ ρ₀²` (in particular for `0 ≤ E ≤ ρ₀²`). -/
theorem Acal_eq_of_le {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {E : ℝ} (hE : E ≤ ρ₀ ^ 2) :
    Acal J s E = π * j * E := by
  have hρ : 0 ≤ ρ₀ ^ 2 := by positivity
  unfold Acal
  rw [intervalIntegral.integral_congr (g := fun _ => j) (fun t ht => by
    refine Jbar_eq_of_le (hJ.flat s hs) ?_ hJ.ρ₀_pos.le
    rw [uIcc, mem_Icc] at ht
    exact ht.2.trans (max_le hρ hE))]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring

theorem Acal_zero {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Acal J s 0 = 0 := by
  rw [Acal_eq_of_le hJ hs (by positivity), mul_zero]

theorem Acal_tendsto_atBot {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Tendsto (Acal J s) atBot atBot := by
  have hlin : Tendsto (fun E : ℝ => π * j * E) atBot atBot :=
    tendsto_id.const_mul_atBot (mul_pos Real.pi_pos hJ.j_pos)
  refine hlin.congr' ?_
  filter_upwards [eventually_le_atBot (0 : ℝ)] with E hE
  exact (Acal_eq_of_le hJ hs (hE.trans (by positivity))).symm

theorem Acal_Einv {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (I : ℝ) : Acal J s (Einv J s I) = I :=
  apply_invR' (Acal_continuous hJ hs) (Acal_strictMono hJ hs) (hJ.tendsto s hs)
    (Acal_tendsto_atBot hJ hs) I

theorem Einv_Acal {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (E : ℝ) : Einv J s (Acal J s E) = E :=
  invR_apply' (Acal_strictMono hJ hs) E

/-- **`lem:pln-area`.** `𝓐_s` is an increasing bijection (of `ℝ`, restricting to one of
`[0, ∞)` since `𝓐_s(0) = 0`). -/
theorem Acal_bijective {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Function.Bijective (Acal J s) :=
  ⟨(Acal_strictMono hJ hs).injective, fun I => ⟨Einv J s I, Acal_Einv hJ hs I⟩⟩

theorem Einv_strictMono {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : StrictMono (Einv J s) :=
  invR_strictMono (Acal_continuous hJ hs) (Acal_strictMono hJ hs) (hJ.tendsto s hs)
    (Acal_tendsto_atBot hJ hs)

theorem Einv_zero {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Einv J s 0 = 0 := by
  conv_lhs => rw [← Acal_zero hJ hs]
  exact Einv_Acal hJ hs 0

theorem Einv_pos {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {I : ℝ} (hI : 0 < I) : 0 < Einv J s I := by
  have := Einv_strictMono hJ hs hI
  rwa [Einv_zero hJ hs] at this

/-- `E_s(I) = I/(π j)` for `0 ≤ I ≤ π j ρ₀²`. -/
theorem Einv_eq_of_le {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {I : ℝ} (h0 : 0 ≤ I)
    (hI : I ≤ π * j * ρ₀ ^ 2) : Einv J s I = I / (π * j) := by
  have hc : 0 < π * j := mul_pos Real.pi_pos hJ.j_pos
  apply invR_linear (Acal_strictMono hJ hs) hc (a := ρ₀ ^ 2)
  · intro x hx; exact Acal_eq_of_le hJ hs ((le_abs_self x).trans hx)
  · rw [abs_of_nonneg h0]; exact hI

theorem Einv_hasDerivAt {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (I : ℝ) :
    HasDerivAt (Einv J s) (π * Jbar J s (Einv J s I))⁻¹ I :=
  hasDerivAt_invR (Acal_continuous hJ hs) (Acal_strictMono hJ hs) (hJ.tendsto s hs)
    (Acal_tendsto_atBot hJ hs) (Acal_hasDerivAt hJ hs) (Acal_deriv_pos hJ hs) I

/-- `(s, I) ↦ E_s(I)` is `C^∞` on `Ioo s₁ s₂ × ℝ`. -/
theorem Einv_param_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Einv J p.1 p.2) (Ioo s₁ s₂ ×ˢ univ) := by
  refine contDiffOn_param_inverse (X := ℝ) isOpen_Ioo (Acal_param_smooth hJ)
    (fun _ hs => (Acal_strictMono hJ hs).injective) (fun s hs E => ?_)
    (fun _ hs I => Acal_Einv hJ hs I)
  rw [(Acal_hasDerivAt hJ hs E).hasFDerivAt.fderiv]
  intro a b hab
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hab
  exact mul_right_cancel₀ (Acal_deriv_pos hJ hs E).ne' hab

/-! ### The area normalisation `D` -/

/-- The radial factor `√(π E/I)` of `D`, as a function of `(s, z)`. -/
def Dfactor (J : ℝ → ℂ → ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (π * Einv J s (π * ‖z‖ ^ 2) / (π * ‖z‖ ^ 2))

omit hJ in
theorem Darea_eq_Dfactor (J : ℝ → ℂ → ℝ) (s : ℝ) :
    Darea J s = fun z => (Dfactor J s z : ℂ) * z := rfl

theorem Einv_nonneg {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {I : ℝ} (hI : 0 ≤ I) : 0 ≤ Einv J s I := by
  rw [← Einv_zero hJ hs]; exact (Einv_strictMono hJ hs).monotone hI

/-- `|D(z)|² = E(π|z|²)`. -/
theorem norm_Darea_sq {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (z : ℂ) :
    ‖Darea J s z‖ ^ 2 = Einv J s (π * ‖z‖ ^ 2) := by
  by_cases hz : z = 0
  · simp [hz, Darea, Einv_zero hJ hs]
  have hr : 0 < ‖z‖ ^ 2 := by positivity
  have hE := Einv_nonneg hJ hs (I := π * ‖z‖ ^ 2) (by positivity)
  rw [Darea, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]
  field_simp

/-- **`sec:pln-normalisation-maps` (ii).** `D(z) = z/√j` for `|z| ≤ √j ρ₀`. -/
theorem Darea_eq_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {z : ℂ} (hz : ‖z‖ ≤ Real.sqrt j * ρ₀) :
    Darea J s z = z / (Real.sqrt j : ℂ) := by
  by_cases h0 : z = 0
  · simp [h0, Darea]
  have hj := hJ.j_pos
  have hr : 0 < ‖z‖ ^ 2 := by positivity
  have hle : ‖z‖ ^ 2 ≤ j * ρ₀ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg z) hz 2
    rwa [mul_pow, Real.sq_sqrt hj.le] at this
  unfold Darea
  rw [Einv_eq_of_le hJ hs (by positivity) (by nlinarith [Real.pi_pos])]
  have : π * (π * ‖z‖ ^ 2 / (π * j)) / (π * ‖z‖ ^ 2) = j⁻¹ := by
    field_simp
  rw [this, Real.sqrt_inv]
  push_cast
  ring

theorem Dfactor_param_contDiffAt {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => Dfactor J p.1 p.2) (s, z) := by
  have hI : 0 < π * ‖z‖ ^ 2 := by have := norm_pos_iff.mpr hz; positivity
  have hn : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => π * ‖p.2‖ ^ 2) (s, z) :=
    contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (s, z) contDiffAt_snd)
  have hE0 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => Einv J q.1 q.2) (s, π * ‖z‖ ^ 2) :=
    (Einv_param_smooth hJ).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (s, π * ‖z‖ ^ 2) ∈ Ioo s₁ s₂ ×ˢ (univ : Set ℝ) from ⟨hs, mem_univ _⟩))
  have hE : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => Einv J p.1 (π * ‖p.2‖ ^ 2)) (s, z) :=
    ContDiffAt.comp (s, z) (g := fun q : ℝ × ℝ => Einv J q.1 q.2)
      (f := fun p : ℝ × ℂ => (p.1, π * ‖p.2‖ ^ 2)) hE0 (contDiffAt_fst.prodMk hn)
  have hq : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => π * Einv J p.1 (π * ‖p.2‖ ^ 2) / (π * ‖p.2‖ ^ 2))
      (s, z) := (contDiffAt_const.mul hE).div hn hI.ne'
  have hpos : 0 < π * Einv J s (π * ‖z‖ ^ 2) / (π * ‖z‖ ^ 2) :=
    div_pos (mul_pos Real.pi_pos (Einv_pos hJ hs hI)) hI
  exact (Real.contDiffAt_sqrt hpos.ne').comp (s, z) hq

/-- **`sec:pln-normalisation-maps`, area.** `(s, z) ↦ D_s(z)` is `C^∞` on `Ioo s₁ s₂ × ℂ`. -/
theorem Darea_param_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => Darea J p.1 p.2) (Ioo s₁ s₂ ×ˢ univ) := by
  rintro ⟨s, z⟩ ⟨hs, -⟩
  apply ContDiffAt.contDiffWithinAt
  by_cases hz : z = 0
  · have hρ : 0 < Real.sqrt j * ρ₀ := mul_pos (Real.sqrt_pos.mpr hJ.j_pos) hJ.ρ₀_pos
    have hnear : ∀ᶠ p : ℝ × ℂ in 𝓝 (s, z), p.1 ∈ Ioo s₁ s₂ ∧ p.2 ∈ ball (0 : ℂ) (Real.sqrt j * ρ₀) :=
      (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hs, by rw [hz]; exact mem_ball_self hρ⟩
    apply (contDiffAt_snd.div_const (Real.sqrt j : ℂ)).congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    exact Darea_eq_of_const hJ hp.1 (mem_ball_zero_iff.mp hp.2).le
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp (s, z)
      (Dfactor_param_contDiffAt hJ hs hz)).mul contDiffAt_snd

/-- **`sec:pln-normalisation-maps` (ii).** `D` is `C^∞`. -/
theorem Darea_smooth_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : ContDiff ℝ ∞ (Darea J s) :=
  contDiff_slice_of_contDiffOn isOpen_Ioo (Darea_param_smooth hJ) hs

end flatResults

/-- The determinant of `D(z ↦ f(z) z)` (`f` real) is `f (f + Df(z) z)`. -/
theorem det_fderiv_real_mul {f : ℂ → ℝ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    LinearMap.det (fderiv ℝ (fun z => (f z : ℂ) * z) z : ℂ →ₗ[ℝ] ℂ) =
      f z * (f z + fderiv ℝ f z z) := by
  set ℓ := fderiv ℝ f z
  have hT : DifferentiableAt ℝ (fun z => (f z : ℂ) * z) z :=
    (Complex.ofRealCLM.differentiableAt.comp z hf).mul differentiableAt_id
  have hval : ∀ v, fderiv ℝ (fun z => (f z : ℂ) * z) z v = (ℓ v : ℂ) * z + (f z : ℂ) * v := by
    intro v
    have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
    have hf0 : HasFDerivAt f ℓ (z + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
    have hg : HasDerivAt (fun t : ℝ => f (z + t • v)) (ℓ v) 0 := hf0.comp_hasDerivAt (0 : ℝ) hl
    have h2 := hg.ofReal_comp.mul hl
    have hT0 : HasFDerivAt (fun z => (f z : ℂ) * z) (fderiv ℝ (fun z => (f z : ℂ) * z) z)
        (z + (0 : ℝ) • v) := by simpa using hT.hasFDerivAt
    have h1 := hT0.comp_hasDerivAt (l := fun z => (f z : ℂ) * z) (0 : ℝ) hl
    have := h1.unique h2
    simpa using this
  rw [det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hval, hval]
  have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • I := by
    apply Complex.ext <;> simp
  have hℓ : ℓ z = z.re * ℓ 1 + z.im * ℓ I := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hℓ]
  clear_value ℓ
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im, add_re, add_im]
  ring

section flatResults2
variable {J : ℝ → ℂ → ℝ} {s₁ s₂ j ρ₀ : ℝ} (hJ : FlatDensity J s₁ s₂ j ρ₀)
include hJ

/-- **`lem:pln-area`, `sec:pln-normalisation-maps` (ii).** `D^*(J̄ du∧dv) = ω_source`,
everywhere. -/
theorem Darea_pullback {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (z : ℂ) :
    Jbar J s (‖Darea J s z‖ ^ 2) * LinearMap.det (fderiv ℝ (Darea J s) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hj := hJ.j_pos
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj
  have hρ : 0 < Real.sqrt j * ρ₀ := mul_pos hsj hJ.ρ₀_pos
  by_cases hz : ‖z‖ < Real.sqrt j * ρ₀
  · set c : ℝ := (Real.sqrt j)⁻¹
    have hev : Darea J s =ᶠ[𝓝 z] fun w => ((fun _ : ℂ => c) w : ℂ) * w := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      rw [Darea_eq_of_const hJ hs (mem_ball_zero_iff.mp hw).le]
      simp only [c]; push_cast; ring
    have hD : ‖Darea J s z‖ ≤ ρ₀ := by
      rw [Darea_eq_of_const hJ hs hz.le, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hsj.le, div_le_iff₀ hsj]
      linarith [mul_comm ρ₀ (Real.sqrt j)]
    rw [hev.fderiv_eq, det_fderiv_real_mul (differentiableAt_const c)]
    rw [show fderiv ℝ (fun _ : ℂ => c) z = 0 from (hasFDerivAt_const c z).fderiv,
      show (0 : ℂ →L[ℝ] ℝ) z = 0 from rfl, add_zero]
    rw [Jbar_normSq, Jcirc_eq_of_le (hJ.flat s hs) hD]
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt hj.le, mul_inv_cancel₀ hj.ne']
  · have hz0 : z ≠ 0 := by intro h; apply hz; rw [h, norm_zero]; exact hρ
    set f := Dfactor J s
    have hfd : DifferentiableAt ℝ f z :=
      ((Dfactor_param_contDiffAt hJ hs hz0).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    rw [norm_Darea_sq hJ hs, Darea_eq_Dfactor, det_fderiv_real_mul hfd]
    set r := ‖z‖ ^ 2
    have hr : 0 < r := by have := norm_pos_iff.mpr hz0; positivity
    have key : ∀ t : ℝ, t ^ 2 * f (t • z) ^ 2 * r = Einv J s (π * (t ^ 2 * r)) := by
      intro t
      have hn : ‖t • z‖ ^ 2 = t ^ 2 * r := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      by_cases ht : t = 0
      · subst ht; simp [Einv_zero hJ hs]
      have htr : 0 < t ^ 2 * r := by positivity
      have hE := Einv_nonneg hJ hs (I := π * (t ^ 2 * r)) (by positivity)
      simp only [f, Dfactor]
      rw [hn, Real.sq_sqrt (by positivity)]
      field_simp
    have hl : HasDerivAt (fun t : ℝ => t • z) z 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const z
    have hf1 : HasFDerivAt f (fderiv ℝ f z) ((1 : ℝ) • z) := by simpa using hfd.hasFDerivAt
    have hg : HasDerivAt (fun t : ℝ => f (t • z)) (fderiv ℝ f z z) 1 := hf1.comp_hasDerivAt (l := f) 1 hl
    have h1 := ((hasDerivAt_pow 2 (1 : ℝ)).mul (hg.pow 2)).mul_const r
    have h2 := (Einv_hasDerivAt hJ hs (π * ((1 : ℝ) ^ 2 * r))).comp (1 : ℝ)
      (((hasDerivAt_pow 2 (1 : ℝ)).mul_const r).const_mul π)
    have h1' := h1.congr_of_eventuallyEq (f₁ := fun t : ℝ => Einv J s (π * (t ^ 2 * r)))
      (Eventually.of_forall fun t => (key t).symm)
    have heq := h1'.unique h2
    simp only [Pi.pow_apply, one_smul, one_pow, mul_one, one_mul] at heq
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at heq
    set A := Jbar J s (Einv J s (π * r))
    set ℓ := fderiv ℝ f z z
    have hA : 0 < A := Jbar_pos hJ.cont (hJ.pos s hs) _
    have e1 : (π * A)⁻¹ * (π * (2 * r)) = 2 * r / A := by field_simp
    rw [e1] at heq
    have e2 : A * ((2 * f z ^ 2 + 2 * f z * ℓ) * r) = 2 * r := by rw [heq]; field_simp
    have h2r : (2 * r) ≠ 0 := by positivity
    exact mul_left_cancel₀ h2r (by linear_combination e2)

theorem Acal_pos {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {E : ℝ} (hE : 0 < E) : 0 < Acal J s E := by
  have := Acal_strictMono hJ hs hE
  rwa [Acal_zero hJ hs] at this

/-- **`lem:pln-area`.** `D` is a bijection of `ℂ`. -/
theorem Darea_bijective {s : ℝ} (hs : s ∈ Ioo s₁ s₂) : Function.Bijective (Darea J s) := by
  constructor
  · intro z₁ z₂ h
    have hn : ‖z₁‖ = ‖z₂‖ := by
      have h1 := norm_Darea_sq hJ hs z₁
      rw [h, norm_Darea_sq hJ hs z₂] at h1
      have h2 := (Einv_strictMono hJ hs).injective h1
      have h3 : ‖z₂‖ ^ 2 = ‖z₁‖ ^ 2 := by
        have := Real.pi_pos
        field_simp at h2; linarith
      have := (sq_eq_sq₀ (norm_nonneg z₂) (norm_nonneg z₁)).mp h3
      exact this.symm
    by_cases h0 : z₁ = 0
    · rw [h0, norm_zero] at hn
      rw [h0, norm_eq_zero.mp hn.symm]
    have hI : 0 < π * ‖z₁‖ ^ 2 := by have := norm_pos_iff.mpr h0; positivity
    have hf : 0 < Dfactor J s z₁ :=
      Real.sqrt_pos.mpr (div_pos (mul_pos Real.pi_pos (Einv_pos hJ hs hI)) hI)
    have hf' : Dfactor J s z₂ = Dfactor J s z₁ := by simp only [Dfactor, hn]
    rw [Darea_eq_Dfactor] at h
    simp only [hf'] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hf.ne') h
  · intro y
    by_cases h0 : y = 0
    · exact ⟨0, by simp [h0, Darea]⟩
    have hr : 0 < ‖y‖ ^ 2 := by have := norm_pos_iff.mpr h0; positivity
    have hA := Acal_pos hJ hs hr
    set c := Real.sqrt (Acal J s (‖y‖ ^ 2) / (π * ‖y‖ ^ 2))
    have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hA (by positivity))
    refine ⟨(c : ℂ) * y, ?_⟩
    have hz : π * ‖(c : ℂ) * y‖ ^ 2 = Acal J s (‖y‖ ^ 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_pow,
        Real.sq_sqrt (div_pos hA (by positivity)).le]
      field_simp
    rw [Darea, hz, Einv_Acal hJ hs, ← mul_assoc, ← Complex.ofReal_mul]
    have : Real.sqrt (π * ‖y‖ ^ 2 / Acal J s (‖y‖ ^ 2)) * c = 1 := by
      rw [← Real.sqrt_mul (div_pos (by positivity) hA).le]
      rw [show π * ‖y‖ ^ 2 / Acal J s (‖y‖ ^ 2) * (Acal J s (‖y‖ ^ 2) / (π * ‖y‖ ^ 2)) = 1 by
        field_simp]
      exact Real.sqrt_one
    rw [this, Complex.ofReal_one, one_mul]

/-! ### The composite (`sec:pln-normalisation-maps`) -/

/-- The composite `F_s ∘ T_s⁻¹ ∘ D_s` maps `{π|z|² = I}` into `F_s({|w|² = E_s(I)})`. -/
theorem normalize_circle {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (z : ℂ) :
    ‖TrotInv J s (Darea J s z)‖ ^ 2 = Einv J s (π * ‖z‖ ^ 2) := by
  rw [norm_TrotInv hJ hs, norm_Darea_sq hJ hs]

/-- On `|z| ≤ √j ρ₀` the composite is `z ↦ G(z/√j)`. -/
theorem normalize_eq_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (G : ℂ → ℂ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.sqrt j * ρ₀) :
    G (TrotInv J s (Darea J s z)) = G (z / (Real.sqrt j : ℂ)) := by
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hJ.j_pos
  rw [Darea_eq_of_const hJ hs hz, TrotInv_eq_id_of_const hJ hs]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsj.le, div_le_iff₀ hsj]
  linarith [mul_comm ρ₀ (Real.sqrt j)]

/-- `det D(T⁻¹)(y) · det DT(T⁻¹ y) = 1`. -/
theorem det_TrotInv_mul {s : ℝ} (hs : s ∈ Ioo s₁ s₂) (y : ℂ) :
    LinearMap.det (fderiv ℝ (Trot J s) (TrotInv J s y) : ℂ →ₗ[ℝ] ℂ) *
      LinearMap.det (fderiv ℝ (TrotInv J s) y : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hT := (Trot_smooth_of_const hJ hs).differentiable (by simp)
  have hTi := (TrotInv_smooth_of_const hJ hs).differentiable (by simp)
  have hid : Trot J s ∘ TrotInv J s = id := funext fun y => Trot_TrotInv hJ hs y
  have h := fderiv_comp y (hT (TrotInv J s y)) (hTi y)
  rw [hid, fderiv_id] at h
  rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, ← h,
    ContinuousLinearMap.coe_id, LinearMap.det_id]

/-- **Area identity of the composite.** If `det DG = J_s`, then `det D(G ∘ T_s⁻¹ ∘ D_s) = 1`. -/
theorem normalize_det {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {G : ℂ → ℂ} (hG : Differentiable ℝ G)
    (hGdet : ∀ w, LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ) = J s w) (z : ℂ) :
    LinearMap.det (fderiv ℝ (fun z => G (TrotInv J s (Darea J s z))) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hTi := (TrotInv_smooth_of_const hJ hs).differentiable (by simp)
  have hD := (Darea_smooth_of_const hJ hs).differentiable (by simp)
  have hc : (fun z => G (TrotInv J s (Darea J s z))) = G ∘ (TrotInv J s ∘ Darea J s) := rfl
  rw [hc, fderiv_comp z (hG _) ((hTi _).comp z (hD z)), fderiv_comp z (hTi _) (hD z),
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    LinearMap.det_comp]
  simp only [Function.comp_apply]
  set y := Darea J s z
  set w := TrotInv J s y
  have h1 := det_TrotInv_mul hJ hs y
  have h2 := Darea_pullback hJ hs z
  rw [Trot_det hJ.smooth (hJ.pos s hs)] at h1
  have hnw : ‖w‖ = ‖y‖ := norm_TrotInv hJ hs y
  rw [hnw] at h1
  rw [hGdet]
  have hJw := (hJ.pos s hs w).ne'
  have hJb := (Jbar_pos hJ.cont (hJ.pos s hs) (‖y‖ ^ 2)).ne'
  set a := LinearMap.det (fderiv ℝ (TrotInv J s) y : ℂ →ₗ[ℝ] ℂ)
  set b := LinearMap.det (fderiv ℝ (Darea J s) z : ℂ →ₗ[ℝ] ℂ)
  have : J s w * (a * b) =
      (J s w / Jbar J s (‖y‖ ^ 2) * a) * (Jbar J s (‖y‖ ^ 2) * b) := by
    field_simp
  rw [this, h1, h2, one_mul]

/-- **`sec:pln-normalisation-maps`.** For a jointly `C^∞` family `F_s` with
`det DF_s = J_s`, the map `(s, z) ↦ F_s(T_s⁻¹(D_s z))` is `C^∞` on `Ioo s₁ s₂ × ℂ`, has
determinant `1`, and equals `F_s(z/√j)` for `|z| ≤ √j ρ₀`. -/
theorem normalize_param_smooth {F : ℝ → ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => F p.1 p.2) (Ioo s₁ s₂ ×ˢ univ))
    (hFdet : ∀ s ∈ Ioo s₁ s₂, ∀ w, LinearMap.det (fderiv ℝ (F s) w : ℂ →ₗ[ℝ] ℂ) = J s w) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => F p.1 (TrotInv J p.1 (Darea J p.1 p.2)))
        (Ioo s₁ s₂ ×ˢ univ) ∧
      (∀ s ∈ Ioo s₁ s₂, ∀ z, LinearMap.det
        (fderiv ℝ (fun z => F s (TrotInv J s (Darea J s z))) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
      (∀ s ∈ Ioo s₁ s₂, ∀ z : ℂ, ‖z‖ ≤ Real.sqrt j * ρ₀ →
        F s (TrotInv J s (Darea J s z)) = F s (z / (Real.sqrt j : ℂ))) := by
  refine ⟨?_, fun s hs z => ?_, fun s hs z hz => normalize_eq_of_const hJ hs (F s) hz⟩
  · have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1, Darea J p.1 p.2)) (Ioo s₁ s₂ ×ˢ univ) :=
      contDiffOn_fst.prodMk (Darea_param_smooth hJ)
    have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1, TrotInv J p.1 (Darea J p.1 p.2)))
        (Ioo s₁ s₂ ×ˢ univ) :=
      contDiffOn_fst.prodMk ((TrotInv_param_smooth hJ).comp h1 fun p hp => ⟨hp.1, mem_univ _⟩)
    exact hF.comp h2 fun p hp => ⟨hp.1, mem_univ _⟩
  · exact normalize_det hJ hs
      ((contDiff_slice_of_contDiffOn isOpen_Ioo hF hs).differentiable (by simp)) (hFdet s hs) z

/-- **`sec:pln-normalisation-maps` (iii).** For a single density (`s` fixed) and a `C^∞` map
`G` with `det DG = J_s`, `G ∘ T⁻¹ ∘ D` is `C^∞`, has determinant `1`, and equals `G(z/√j)` for
`|z| ≤ √j ρ₀`. -/
theorem normalize_smooth_of_const {s : ℝ} (hs : s ∈ Ioo s₁ s₂) {G : ℂ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hGdet : ∀ w, LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ) = J s w) :
    ContDiff ℝ ∞ (fun z => G (TrotInv J s (Darea J s z))) ∧
      (∀ z, LinearMap.det
        (fderiv ℝ (fun z => G (TrotInv J s (Darea J s z))) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ Real.sqrt j * ρ₀ →
        G (TrotInv J s (Darea J s z)) = G (z / (Real.sqrt j : ℂ))) :=
  ⟨hG.comp ((TrotInv_smooth_of_const hJ hs).comp (Darea_smooth_of_const hJ hs)),
    normalize_det hJ hs (hG.differentiable (by simp)) hGdet,
    fun _ hz => normalize_eq_of_const hJ hs G hz⟩

end flatResults2

end SymplecticPacking.Inner
