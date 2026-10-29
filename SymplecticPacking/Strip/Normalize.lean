import SymplecticPacking.Inner.Normalize
import SymplecticPacking.Qhat.Normal

/-!
# Rotation and area normalisation for a general density

The rotation and area normalisations of `sec:pln-normalisation-maps` (`Inner/Normalize.lean`) for a *general* positive
`C^∞` density `J : ℂ → ℝ` with `𝓐_J → ∞` — no flatness near the origin is assumed. This is
what `sec:str` (`prop:str-strip`) needs for the strip density `J_st`, which is not constant near `0`.

The paper proves smoothness of `F ∘ T⁻¹ ∘ D` via real analyticity of the density. Here we prove
`C^∞` directly:
* `T(w) = Rot_{𝓜(w)/J̄(w)} w` is `C^∞` in the Cartesian variable (parametric integrals), and
  `det DT = J/J̄ > 0`, so `T⁻¹` is `C^∞` by the inverse function theorem;
* for `D` we use its inverse `D⁻¹(w) = √(G(w)) w` with
  `G(w) = ∫₀¹ 2r J̄(r w) dr` (`= 𝓐(|w|²)/(π|w|²)` for `w ≠ 0`, `= J(0)` at `0`), which is `C^∞`
  (a parametric integral with jointly smooth integrand) and positive; `det D(D⁻¹) = J̄ > 0`
  everywhere, so `D` is `C^∞` by the inverse function theorem.

We work with the constant family `cf J = fun _ => J` at the parameter `s = 0`, so that all
definitions (`Trot`, `TrotInv`, `Acal`, `Einv`, `Darea`) are literally those of `sec:pln-normalisation-maps`.
-/

noncomputable section

namespace SymplecticPacking.Strip

open Filter Topology Set Metric
open scoped ContDiff Real

set_option linter.unusedSectionVars false

/-- The constant density family `s ↦ J`. -/
abbrev cf (J : ℂ → ℝ) : ℝ → ℂ → ℝ := fun _ => J

/-- `G(w) = ∫₀¹ 2r J̄(r w) dr` (auxiliary; `π|w|² G(w) = 𝓐(|w|²)`). -/
def Gdisk (J : ℂ → ℝ) (w : ℂ) : ℝ :=
  ∫ r in (0 : ℝ)..1, 2 * r * Inner.Jcirc (cf J) 0 ((r : ℂ) * w)

/-- The inverse area normalisation `D⁻¹(w) = √(G(w)) w` (auxiliary). -/
def DareaInv (J : ℂ → ℝ) (w : ℂ) : ℂ := (Real.sqrt (Gdisk J w) : ℂ) * w

/-! ### Continuous positive densities: `J̄`, `𝓐`, `E` -/

section cont
variable {J : ℂ → ℝ} (hc : Continuous J) (hp : ∀ w, 0 < J w)
include hc hp

theorem gJbar_continuous : Continuous (Inner.Jbar (cf J) 0) := Qhat.Jbar_const_continuous hc

theorem gJbar_pos (t : ℝ) : 0 < Inner.Jbar (cf J) 0 t := Inner.Jbar_pos hc hp t

theorem gJcirc_pos (w : ℂ) : 0 < Inner.Jcirc (cf J) 0 w := Inner.Jcirc_pos hc hp w

theorem gJbar_of_nonpos {t : ℝ} (ht : t ≤ 0) : Inner.Jbar (cf J) 0 t = J 0 := by
  unfold Inner.Jbar
  rw [Real.sqrt_eq_zero'.mpr ht]
  simp only [Complex.ofReal_zero, Inner.Rot, mul_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp

theorem gAcal_hasDerivAt (E : ℝ) :
    HasDerivAt (Inner.Acal (cf J) 0) (π * Inner.Jbar (cf J) 0 E) E :=
  (((gJbar_continuous hc hp).integral_hasStrictDerivAt 0 E).hasDerivAt).const_mul π

theorem gAcal_continuous : Continuous (Inner.Acal (cf J) 0) :=
  continuous_iff_continuousAt.mpr fun E => (gAcal_hasDerivAt hc hp E).continuousAt

theorem gAcal_strictMono : StrictMono (Inner.Acal (cf J) 0) :=
  strictMono_of_hasDerivAt_pos (gAcal_hasDerivAt hc hp)
    (fun E => mul_pos Real.pi_pos (gJbar_pos hc hp E))

theorem gAcal_zero : Inner.Acal (cf J) 0 0 = 0 := by simp [Inner.Acal]

theorem gAcal_of_nonpos {E : ℝ} (hE : E ≤ 0) : Inner.Acal (cf J) 0 E = π * J 0 * E := by
  unfold Inner.Acal
  rw [intervalIntegral.integral_congr (g := fun _ => J 0) (fun t ht => by
    refine gJbar_of_nonpos hc hp ?_
    rw [uIcc_of_ge hE] at ht; exact ht.2)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring

theorem gAcal_tendsto_atBot : Tendsto (Inner.Acal (cf J) 0) atBot atBot := by
  have hlin : Tendsto (fun E : ℝ => π * J 0 * E) atBot atBot :=
    tendsto_id.const_mul_atBot (mul_pos Real.pi_pos (hp 0))
  refine hlin.congr' ?_
  filter_upwards [eventually_le_atBot (0 : ℝ)] with E hE
  exact (gAcal_of_nonpos hc hp hE).symm

theorem gEinv_Acal (E : ℝ) : Inner.Einv (cf J) 0 (Inner.Acal (cf J) 0 E) = E :=
  Inner.invR_apply' (gAcal_strictMono hc hp) E

theorem gEinv_zero : Inner.Einv (cf J) 0 0 = 0 := by
  conv_lhs => rw [← gAcal_zero hc hp]
  exact gEinv_Acal hc hp 0

variable (htop : Tendsto (Inner.Acal (cf J) 0) atTop atTop)
include htop

theorem gAcal_Einv (I : ℝ) : Inner.Acal (cf J) 0 (Inner.Einv (cf J) 0 I) = I :=
  Inner.apply_invR' (gAcal_continuous hc hp) (gAcal_strictMono hc hp) htop
    (gAcal_tendsto_atBot hc hp) I

theorem gEinv_strictMono : StrictMono (Inner.Einv (cf J) 0) :=
  Inner.invR_strictMono (gAcal_continuous hc hp) (gAcal_strictMono hc hp) htop
    (gAcal_tendsto_atBot hc hp)

theorem gEinv_nonneg {I : ℝ} (hI : 0 ≤ I) : 0 ≤ Inner.Einv (cf J) 0 I := by
  rw [← gEinv_zero hc hp]; exact (gEinv_strictMono hc hp htop).monotone hI

theorem gEinv_pos {I : ℝ} (hI : 0 < I) : 0 < Inner.Einv (cf J) 0 I := by
  rw [← gEinv_zero hc hp]; exact gEinv_strictMono hc hp htop hI

/-- `|D(z)|² = E(π|z|²)`. -/
theorem gnorm_Darea_sq (z : ℂ) :
    ‖Inner.Darea (cf J) 0 z‖ ^ 2 = Inner.Einv (cf J) 0 (π * ‖z‖ ^ 2) := by
  by_cases hz : z = 0
  · simp [hz, Inner.Darea, gEinv_zero hc hp]
  have hr : 0 < ‖z‖ ^ 2 := by have := norm_pos_iff.mpr hz; positivity
  have hE := gEinv_nonneg hc hp htop (I := π * ‖z‖ ^ 2) (by positivity)
  rw [Inner.Darea, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

end cont

/-! ### The function `G` and `D⁻¹` -/

section disk
variable {J : ℂ → ℝ} (hJ : ContDiff ℝ ∞ J) (hp : ∀ w, 0 < J w)
include hJ hp

theorem hcf : ContDiff ℝ ∞ (fun p : ℝ × ℂ => cf J p.1 p.2) := hJ.comp contDiff_snd

theorem Jcirc_contDiff : ContDiff ℝ ∞ (Inner.Jcirc (cf J) 0) :=
  Inner.contDiff_slice_of (Inner.contDiff_Jcirc (hcf hJ hp)) 0

/-- `π|w|² G(w) = 𝓐(|w|²)`. -/
theorem Gdisk_eq (w : ℂ) :
    π * ‖w‖ ^ 2 * Gdisk J w = Inner.Acal (cf J) 0 (‖w‖ ^ 2) := by
  have hc := hJ.continuous
  set E := ‖w‖ ^ 2
  have h1 : ∀ r : ℝ, Inner.Jcirc (cf J) 0 ((r : ℂ) * w) = Inner.Jbar (cf J) 0 (E * r ^ 2) := by
    intro r
    rw [← Inner.Jbar_normSq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [E]; ring_nf
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 1)
    (f := fun r => E * r ^ 2) (f' := fun r => E * (2 * r)) (g := Inner.Jbar (cf J) 0)
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).const_mul E) (by fun_prop)
    (gJbar_continuous hc hp)
  simp only [Function.comp_def] at hsub
  rw [show E * (0 : ℝ) ^ 2 = 0 by ring, show E * (1 : ℝ) ^ 2 = E by ring] at hsub
  unfold Inner.Acal Gdisk
  rw [← hsub, mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  simp only [h1]
  ring

theorem Gdisk_contDiff : ContDiff ℝ ∞ (Gdisk J) := by
  have hJc := Inner.contDiff_Jcirc (hcf hJ hp)
  have hi : ContDiff ℝ ∞ (fun q : ℝ × ℂ => 2 * q.1 * Inner.Jcirc (cf J) 0 ((q.1 : ℂ) * q.2)) := by
    refine (contDiff_const.mul contDiff_fst).mul ?_
    exact hJc.comp (contDiff_const.prodMk
      ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_snd))
  exact OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral hi

theorem Gdisk_pos (w : ℂ) : 0 < Gdisk J w := by
  have hc := Jcirc_contDiff hJ hp
  unfold Gdisk
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((continuous_const.mul continuous_id).mul (hc.continuous.comp
      (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
  · intro r hr
    exact mul_pos (by linarith [hr.1]) (gJcirc_pos hJ.continuous hp _)
  · norm_num

theorem Gdisk_zero : Gdisk J 0 = Inner.Jcirc (cf J) 0 0 := by
  unfold Gdisk
  simp only [mul_zero]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
  norm_num

theorem sqrtG_contDiff : ContDiff ℝ ∞ (fun w => Real.sqrt (Gdisk J w)) :=
  (Gdisk_contDiff hJ hp).sqrt fun w => (Gdisk_pos hJ hp w).ne'

theorem DareaInv_contDiff : ContDiff ℝ ∞ (DareaInv J) :=
  (Complex.ofRealCLM.contDiff.comp (sqrtG_contDiff hJ hp)).mul contDiff_id

/-- `det D(D⁻¹)(w) = J̄(|w|²)`. -/
theorem DareaInv_det (w : ℂ) :
    LinearMap.det (fderiv ℝ (DareaInv J) w : ℂ →ₗ[ℝ] ℂ) = Inner.Jcirc (cf J) 0 w := by
  set f := fun w => Real.sqrt (Gdisk J w)
  have hfd : ∀ z, DifferentiableAt ℝ f z := fun z =>
    (sqrtG_contDiff hJ hp).differentiable (by simp) z
  have hD : DareaInv J = fun z => (f z : ℂ) * z := rfl
  rw [hD, Inner.det_fderiv_real_mul (hfd w)]
  have hf2 : ∀ z, f z ^ 2 = Gdisk J z := fun z => Real.sq_sqrt (Gdisk_pos hJ hp z).le
  by_cases hw : w = 0
  · subst hw
    rw [map_zero, add_zero, ← sq, hf2, Gdisk_zero hJ hp]
  set r := ‖w‖ ^ 2
  have hr : 0 < r := by have := norm_pos_iff.mpr hw; positivity
  have key : ∀ t : ℝ, π * (t ^ 2 * r) * f (t • w) ^ 2 =
      Inner.Acal (cf J) 0 (t ^ 2 * r) := by
    intro t
    have hn : ‖t • w‖ ^ 2 = t ^ 2 * r := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hf2, ← hn]; exact Gdisk_eq hJ hp _
  have hl : HasDerivAt (fun t : ℝ => t • w) w 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
  have hf1 : HasFDerivAt f (fderiv ℝ f w) ((1 : ℝ) • w) := by simpa using (hfd w).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => f (t • w)) (fderiv ℝ f w w) 1 :=
    hf1.comp_hasDerivAt (l := f) 1 hl
  have h1 := ((((hasDerivAt_pow 2 (1 : ℝ)).mul_const r).const_mul π).mul (hg.pow 2))
  have h2 := (gAcal_hasDerivAt hJ.continuous hp ((1 : ℝ) ^ 2 * r)).comp (1 : ℝ)
    ((hasDerivAt_pow 2 (1 : ℝ)).mul_const r)
  have h1' := h1.congr_of_eventuallyEq (f₁ := fun t : ℝ => Inner.Acal (cf J) 0 (t ^ 2 * r))
    (Eventually.of_forall fun t => (key t).symm)
  have heq := h1'.unique h2
  simp only [Pi.pow_apply, one_smul, one_pow, one_mul, Nat.cast_ofNat] at heq
  rw [← Inner.Jbar_normSq]
  have hpi := Real.pi_pos
  have e : π * (2 * r) * (f w * (f w + fderiv ℝ f w w)) = π * (2 * r) * Inner.Jbar (cf J) 0 r := by
    linear_combination heq
  exact mul_left_cancel₀ (by positivity) e

theorem DareaInv_det_ne_zero (w : ℂ) :
    LinearMap.det (fderiv ℝ (DareaInv J) w : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
  rw [DareaInv_det hJ hp]; exact (gJcirc_pos hJ.continuous hp w).ne'

/-- `D ∘ D⁻¹ = id`. -/
theorem Darea_DareaInv (w : ℂ) : Inner.Darea (cf J) 0 (DareaInv J w) = w := by
  by_cases hw : w = 0
  · simp [hw, DareaInv, Inner.Darea]
  have hG := Gdisk_pos hJ hp w
  have hr : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.mpr hw; positivity
  have hn : π * ‖DareaInv J w‖ ^ 2 = Inner.Acal (cf J) 0 (‖w‖ ^ 2) := by
    rw [DareaInv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hG.le, ← Gdisk_eq hJ hp]
    ring
  rw [Inner.Darea, hn, gEinv_Acal hJ.continuous hp, ← Gdisk_eq hJ hp, DareaInv, ← mul_assoc,
    ← Complex.ofReal_mul]
  have : Real.sqrt (π * ‖w‖ ^ 2 / (π * ‖w‖ ^ 2 * Gdisk J w)) * Real.sqrt (Gdisk J w) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show π * ‖w‖ ^ 2 / (π * ‖w‖ ^ 2 * Gdisk J w) * Gdisk J w = 1 by field_simp]
    exact Real.sqrt_one
  rw [this, Complex.ofReal_one, one_mul]

theorem DareaInv_injective : Function.Injective (DareaInv J) := fun a b h => by
  rw [← Darea_DareaInv hJ hp a, h, Darea_DareaInv hJ hp b]

variable (htop : Tendsto (Inner.Acal (cf J) 0) atTop atTop)
include htop

/-- `D⁻¹ ∘ D = id`. -/
theorem DareaInv_Darea (y : ℂ) : DareaInv J (Inner.Darea (cf J) 0 y) = y := by
  by_cases hy : y = 0
  · simp [hy, DareaInv, Inner.Darea]
  have hc := hJ.continuous
  have hI : 0 < π * ‖y‖ ^ 2 := by have := norm_pos_iff.mpr hy; positivity
  set z := Inner.Darea (cf J) 0 y
  have hz2 : ‖z‖ ^ 2 = Inner.Einv (cf J) 0 (π * ‖y‖ ^ 2) := gnorm_Darea_sq hc hp htop y
  have hEpos := gEinv_pos hc hp htop hI
  have hkey := Gdisk_eq hJ hp z
  rw [hz2, gAcal_Einv hc hp htop] at hkey
  -- `G(z) E = |y|²`
  have hG := Gdisk_pos hJ hp z
  set c := Real.sqrt (π * Inner.Einv (cf J) 0 (π * ‖y‖ ^ 2) / (π * ‖y‖ ^ 2))
  have hzc : z = (c : ℂ) * y := rfl
  have hcG : Real.sqrt (Gdisk J z) * c = 1 := by
    rw [← Real.sqrt_mul hG.le]
    have : Gdisk J z * (π * Inner.Einv (cf J) 0 (π * ‖y‖ ^ 2) / (π * ‖y‖ ^ 2)) = 1 := by
      have h' : Gdisk J z * Inner.Einv (cf J) 0 (π * ‖y‖ ^ 2) = ‖y‖ ^ 2 :=
        mul_left_cancel₀ Real.pi_ne_zero (by linear_combination hkey)
      field_simp
      linear_combination h'
    rw [this, Real.sqrt_one]
  rw [DareaInv, hzc, ← mul_assoc, ← Complex.ofReal_mul, ← hzc, hcG, Complex.ofReal_one, one_mul]

/-- **`D` is `C^∞`** (inverse function theorem applied to `D⁻¹`). -/
theorem Darea_contDiff : ContDiff ℝ ∞ (Inner.Darea (cf J) 0) := by
  have h := Inner.contDiffOn_param_inverse (X := ℂ) (G := fun _ => DareaInv J)
    (inv := fun _ => Inner.Darea (cf J) 0) (U := univ) isOpen_univ
    ((DareaInv_contDiff hJ hp).comp contDiff_snd).contDiffOn
    (fun _ _ => DareaInv_injective hJ hp)
    (fun _ _ w => Inner.injective_of_det_ne_zero _ (DareaInv_det_ne_zero hJ hp w))
    (fun _ _ y => DareaInv_Darea hJ hp htop y)
  exact Inner.contDiff_slice_of_contDiffOn (G := fun _ => Inner.Darea (cf J) 0) isOpen_univ h
    (mem_univ 0)

/-- **`D^*(J̄ du∧dv) = ω`**: `J̄(|D z|²) · det DD(z) = 1`. -/
theorem Darea_pullback (z : ℂ) :
    Inner.Jbar (cf J) 0 (‖Inner.Darea (cf J) 0 z‖ ^ 2) *
      LinearMap.det (fderiv ℝ (Inner.Darea (cf J) 0) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hD := (Darea_contDiff hJ hp htop).differentiable (by simp)
  have hDi := (DareaInv_contDiff hJ hp).differentiable (by simp)
  have hid : DareaInv J ∘ Inner.Darea (cf J) 0 = id := funext fun y => DareaInv_Darea hJ hp htop y
  have h := fderiv_comp z (hDi (Inner.Darea (cf J) 0 z)) (hD z)
  rw [hid, fderiv_id] at h
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)) h
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at this
  rw [DareaInv_det hJ hp, ← Inner.Jbar_normSq] at this
  exact this.symm

end disk

/-! ### The rotation normalisation -/

section rot
variable {J : ℂ → ℝ} (hJ : ContDiff ℝ ∞ J) (hp : ∀ w, 0 < J w)
include hJ hp

theorem Trot_contDiff : ContDiff ℝ ∞ (Inner.Trot (cf J) 0) := by
  rw [Inner.Trot_eq_thetaC]
  exact Inner.contDiff_Rot.comp ((Inner.contDiff_thetaC (hcf hJ hp) hp).prodMk contDiff_id)

theorem Trot_bij : Function.Bijective (Inner.Trot (cf J) 0) :=
  Inner.Trot_bijective (J := cf J) hJ.continuous hp

theorem Trot_TrotInv (y : ℂ) : Inner.Trot (cf J) 0 (Inner.TrotInv (cf J) 0 y) = y := by
  obtain ⟨w, hw⟩ := (Trot_bij hJ hp).2 y
  rw [Inner.TrotInv_eq_of (Trot_bij hJ hp).1 hw, hw]

theorem TrotInv_Trot (w : ℂ) : Inner.TrotInv (cf J) 0 (Inner.Trot (cf J) 0 w) = w :=
  Inner.TrotInv_eq_of (Trot_bij hJ hp).1 rfl

theorem norm_TrotInv (y : ℂ) : ‖Inner.TrotInv (cf J) 0 y‖ = ‖y‖ := by
  conv_rhs => rw [← Trot_TrotInv hJ hp y]
  rw [Inner.norm_Trot]

theorem Trot_det (w : ℂ) :
    LinearMap.det (fderiv ℝ (Inner.Trot (cf J) 0) w : ℂ →ₗ[ℝ] ℂ) =
      J w / Inner.Jbar (cf J) 0 (‖w‖ ^ 2) :=
  Inner.Trot_det (J := cf J) (hcf hJ hp) hp w

/-- **`T⁻¹` is `C^∞`** (inverse function theorem). -/
theorem TrotInv_contDiff : ContDiff ℝ ∞ (Inner.TrotInv (cf J) 0) := by
  have h := Inner.contDiffOn_param_inverse (X := ℂ) (G := fun _ => Inner.Trot (cf J) 0)
    (inv := fun _ => Inner.TrotInv (cf J) 0) (U := univ) isOpen_univ
    ((Trot_contDiff hJ hp).comp contDiff_snd).contDiffOn
    (fun _ _ => (Trot_bij hJ hp).1)
    (fun _ _ w => Inner.injective_of_det_ne_zero _ (by
      rw [Trot_det hJ hp]
      exact (div_pos (hp w) (gJbar_pos hJ.continuous hp _)).ne'))
    (fun _ _ y => Trot_TrotInv hJ hp y)
  exact Inner.contDiff_slice_of_contDiffOn (G := fun _ => Inner.TrotInv (cf J) 0) isOpen_univ h
    (mem_univ 0)

theorem det_TrotInv_mul (y : ℂ) :
    LinearMap.det (fderiv ℝ (Inner.Trot (cf J) 0) (Inner.TrotInv (cf J) 0 y) : ℂ →ₗ[ℝ] ℂ) *
      LinearMap.det (fderiv ℝ (Inner.TrotInv (cf J) 0) y : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hT := (Trot_contDiff hJ hp).differentiable (by simp)
  have hTi := (TrotInv_contDiff hJ hp).differentiable (by simp)
  have hid : Inner.Trot (cf J) 0 ∘ Inner.TrotInv (cf J) 0 = id :=
    funext fun y => Trot_TrotInv hJ hp y
  have h := fderiv_comp y (hT (Inner.TrotInv (cf J) 0 y)) (hTi y)
  rw [hid, fderiv_id] at h
  rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, ← h,
    ContinuousLinearMap.coe_id, LinearMap.det_id]

end rot

/-! ### The composite `G ∘ T⁻¹ ∘ D` -/

section composite
variable {J : ℂ → ℝ} (hJ : ContDiff ℝ ∞ J) (hp : ∀ w, 0 < J w)
  (htop : Tendsto (Inner.Acal (cf J) 0) atTop atTop)
include hJ hp htop

/-- **General normalisation lemma** (`lem:str-normalisation` without flatness or
analyticity). For a `C^∞` map `G` with `det DG = J`, the composite `G ∘ T⁻¹ ∘ D` is `C^∞`, has
Jacobian determinant `1`, and maps the circle `π|z|² = I` into `G({|w|² = E(I)})`. -/
theorem normalize_general {G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGdet : ∀ w, LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ) = J w) :
    ContDiff ℝ ∞ (fun z => G (Inner.TrotInv (cf J) 0 (Inner.Darea (cf J) 0 z))) ∧
      (∀ z, LinearMap.det (fderiv ℝ (fun z => G (Inner.TrotInv (cf J) 0
        (Inner.Darea (cf J) 0 z))) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
      (∀ z, ‖Inner.TrotInv (cf J) 0 (Inner.Darea (cf J) 0 z)‖ ^ 2 =
        Inner.Einv (cf J) 0 (π * ‖z‖ ^ 2)) := by
  have hTi := TrotInv_contDiff hJ hp
  have hD := Darea_contDiff hJ hp htop
  refine ⟨hG.comp (hTi.comp hD), fun z => ?_, fun z => ?_⟩
  · have hTid := hTi.differentiable (by simp)
    have hDd := hD.differentiable (by simp)
    have hc : (fun z => G (Inner.TrotInv (cf J) 0 (Inner.Darea (cf J) 0 z))) =
        G ∘ (Inner.TrotInv (cf J) 0 ∘ Inner.Darea (cf J) 0) := rfl
    rw [hc, fderiv_comp z ((hG.differentiable (by simp)) _) ((hTid _).comp z (hDd z)),
      fderiv_comp z (hTid _) (hDd z), ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, LinearMap.det_comp]
    simp only [Function.comp_apply]
    set y := Inner.Darea (cf J) 0 z
    set w := Inner.TrotInv (cf J) 0 y
    have h1 := det_TrotInv_mul hJ hp y
    have h2 := Darea_pullback hJ hp htop z
    rw [Trot_det hJ hp] at h1
    have hnw : ‖w‖ = ‖y‖ := norm_TrotInv hJ hp y
    rw [hnw] at h1
    rw [hGdet]
    have hJw := (hp w).ne'
    have hJb := (gJbar_pos hJ.continuous hp (‖y‖ ^ 2)).ne'
    set a := LinearMap.det (fderiv ℝ (Inner.TrotInv (cf J) 0) y : ℂ →ₗ[ℝ] ℂ)
    set b := LinearMap.det (fderiv ℝ (Inner.Darea (cf J) 0) z : ℂ →ₗ[ℝ] ℂ)
    have : J w * (a * b) =
        (J w / Inner.Jbar (cf J) 0 (‖y‖ ^ 2) * a) * (Inner.Jbar (cf J) 0 (‖y‖ ^ 2) * b) := by
      field_simp
    rw [this, h1, h2, one_mul]
  · rw [norm_TrotInv hJ hp, gnorm_Darea_sq hJ.continuous hp htop]

end composite

end SymplecticPacking.Strip
