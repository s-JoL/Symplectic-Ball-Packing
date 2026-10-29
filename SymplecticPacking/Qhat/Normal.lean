import SymplecticPacking.Qhat.Flow
import SymplecticPacking.Inner.Normalize
import SymplecticPacking.Params

/-!
# Area normalisation of the ambient flow and the isotopy `q̂_t`

`sec:pln-normal`: the direct area normalisation of the ambient flow and the
whole-disk isotopy `q̂_t` (`sec:pln-normal`, `lem:pln-normalisation`, `thm:pln-isotopy`).

Implementation: we reuse the parametric rotation/area normalisation
`T_J⁻¹ ∘ D_J` of `sec:pln-normalisation-maps` (`Inner/Normalize.lean`). It requires a density that is *the same constant*
near the origin for all parameters, while `det Dφ_t = γ_t` there depends on `t`. We therefore
normalise the rescaled flow `G_t(w) = φ_t(w/√γ_t)`, whose density
`Ĵ_t(w) = det DG_t(w) = J^φ_t(w/√γ_t)/γ_t` equals `1` near `0`, and put
`N_t = (·/√γ_t) ∘ T_{Ĵ_t}⁻¹ ∘ D_{Ĵ_t}`, `q̂_t = φ_t ∘ N_t = G_t ∘ T_{Ĵ_t}⁻¹ ∘ D_{Ĵ_t}`.
The radial part is the paper's `(A^φ_t)⁻¹`; the angular part is the angular distribution
function of `J^φ_t` on each circle, normalised by the weighted mean of `sec:pln-normalisation-maps` instead of by
`ϑ_t(P, 0) = 0`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Metric MeasureTheory
open scoped ContDiff Real NNReal

/-! ### The area identity in polar coordinates -/

theorem Jbar_const_continuous {J : ℂ → ℝ} (hJ : Continuous J) :
    Continuous (Inner.Jbar (fun _ => J) 0) := by
  unfold Inner.Jbar
  refine continuous_const.mul ?_
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t φ => J (Inner.Rot φ (Real.sqrt t : ℂ)))
  exact hJ.comp (Inner.contDiff_Rot.continuous.comp (continuous_snd.prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst))))

theorem polarCoord_symm_eq_Rot (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = Inner.Rot p.2 (p.1 : ℂ) := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Inner.Rot, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `∫_{|w| ≤ ρ} J = π ∫₀^{ρ²} J̄ = 𝓐_J(ρ²)` (the first statement of `lem:pln-area`). -/
theorem integral_closedBall_eq_Acal {J : ℂ → ℝ} (hJ : Continuous J) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ w in closedBall (0 : ℂ) ρ, J w = Inner.Acal (fun _ => J) 0 (ρ ^ 2) := by
  set g : ℝ × ℝ → ℝ := fun p => p.1 * J (Inner.Rot p.2 (p.1 : ℂ)) with hgdef
  have hgc : Continuous g := continuous_fst.mul (hJ.comp (Inner.contDiff_Rot.continuous.comp
    (continuous_snd.prodMk (Complex.continuous_ofReal.comp continuous_fst))))
  have h1 : ∫ w in closedBall (0 : ℂ) ρ, J w =
      ∫ p in polarCoord.target, p.1 • (closedBall (0 : ℂ) ρ).indicator J
        (Complex.polarCoord.symm p) := by
    rw [Complex.integral_comp_polarCoord_symm, integral_indicator measurableSet_closedBall]
  have h2 : ∫ p in polarCoord.target, p.1 • (closedBall (0 : ℂ) ρ).indicator J
        (Complex.polarCoord.symm p) =
      ∫ p in polarCoord.target, (Iic ρ ×ˢ (univ : Set ℝ)).indicator g p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hiff : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) ρ ↔
        p ∈ Iic ρ ×ˢ (univ : Set ℝ) := by
      rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp1]
      simp
    dsimp only
    by_cases hpr : p ∈ Iic ρ ×ˢ (univ : Set ℝ)
    · rw [indicator_of_mem (hiff.mpr hpr), indicator_of_mem hpr, polarCoord_symm_eq_Rot]
      rfl
    · rw [indicator_of_notMem (fun h => hpr (hiff.mp h)), indicator_of_notMem hpr, smul_zero]
  have h3 : ∫ p in polarCoord.target, (Iic ρ ×ˢ (univ : Set ℝ)).indicator g p =
      ∫ p in Ioc 0 ρ ×ˢ Ioo (-π) π, g p := by
    rw [setIntegral_indicator (measurableSet_Iic.prod MeasurableSet.univ)]
    congr 2
    ext p
    simp only [polarCoord, mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_Iic, mem_univ,
      and_true, mem_Ioc]
    tauto
  have hint : IntegrableOn g (Ioc 0 ρ ×ˢ Ioo (-π) π) := by
    apply (hgc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
  rw [h1, h2, h3, Measure.volume_eq_prod, setIntegral_prod g (by rwa [← Measure.volume_eq_prod])]
  -- the inner integral
  have hinner : ∀ r ∈ Ioc (0 : ℝ) ρ, ∫ θ in Ioo (-π) π, g (r, θ) =
      r * (2 * π * Inner.Jbar (fun _ => J) 0 (r ^ 2)) := by
    intro r hr
    simp only [hgdef]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    congr 1
    have hper : Function.Periodic (fun θ => J (Inner.Rot θ (r : ℂ))) (2 * π) :=
      fun θ => by simp only [Inner.Rot_two_pi_add]
    have hsh := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at hsh
    rw [hsh]
    unfold Inner.Jbar
    rw [Real.sqrt_sq hr.1.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, ← intervalIntegral.integral_of_le hρ]
  unfold Inner.Acal
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := ρ)
    (f := fun r => r ^ 2) (f' := fun r => 2 * r) (g := Inner.Jbar (fun _ => J) 0)
    (fun x _ => by simpa using (hasDerivAt_pow 2 x)) (by fun_prop) (Jbar_const_continuous hJ)
  simp only [Function.comp_def] at hsub
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  congr 1
  ext r
  ring

/-- Change of variables: for an injective differentiable `G` with `det DG ≥ 0`,
`∫_S det DG = area G(S)`. -/
theorem integral_det_eq_volume {G : ℂ → ℂ} (hG : Differentiable ℝ G)
    (hinj : Function.Injective G)
    (hpos : ∀ w, 0 ≤ LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ)) {S : Set ℂ}
    (hS : MeasurableSet S) :
    ∫ w in S, LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ) = (volume (G '' S)).toReal := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun x _ => (hG x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn (fun _ => (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at h
  rw [Measure.real] at h
  rw [h]
  refine setIntegral_congr_fun hS fun w _ => ?_
  exact (abs_of_nonneg (hpos w)).symm

/-- **Area identity.** If `G` is an injective `C¹` map with `det DG ≥ 0` mapping `B̄(ρ)` onto
`B̄(R)`, then `𝓐_{det DG}(ρ²) = π R²`. -/
theorem Acal_eq_of_image {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (hinj : Function.Injective G)
    (hpos : ∀ w, 0 ≤ LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ)) {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 ≤ R) (him : G '' closedBall 0 ρ = closedBall 0 R) :
    Inner.Acal (fun _ w => LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ)) 0 (ρ ^ 2) = π * R ^ 2 := by
  have hc : Continuous fun w => LinearMap.det (fderiv ℝ G w : ℂ →ₗ[ℝ] ℂ) :=
    ContinuousLinearMap.continuous_det.comp (hG.continuous_fderiv (by norm_num))
  rw [← integral_closedBall_eq_Acal hc hρ,
    integral_det_eq_volume (hG.differentiable (by norm_num)) hinj hpos measurableSet_closedBall, him,
    Complex.volume_closedBall]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-! ### Definitions (`sec:pln-normal`) -/

/-- The determinant of an `ℝ`-linear endomorphism of `ℂ`, by the explicit `2 × 2` formula
(used in definitions instead of `LinearMap.det`, whose Mathlib definition picks a basis). -/
def det2 (L : ℂ →L[ℝ] ℂ) : ℝ := (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re

theorem det2_contDiff : ContDiff ℝ ∞ det2 := by
  have h1 : ContDiff ℝ ∞ (fun L : ℂ →L[ℝ] ℂ => L 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff
  have hI : ContDiff ℝ ∞ (fun L : ℂ →L[ℝ] ℂ => L Complex.I) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff
  have he : det2 = fun L : ℂ →L[ℝ] ℂ => Complex.reCLM (L 1) * Complex.imCLM (L Complex.I) -
      Complex.imCLM (L 1) * Complex.reCLM (L Complex.I) := rfl
  rw [he]
  exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp hI)).sub
    ((Complex.imCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp hI))

theorem det2_eq (L : ℂ →L[ℝ] ℂ) : det2 L = LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) := by
  rw [Inner.det_eq_re_im]; rfl

/-- `J^φ_t = det Dφ_t` (Cartesian; in polar area coordinates `φ_t^*ω₂ = J^φ_t dP∧dΘ`). -/
def Jphi (D : PathData) (t : ℝ) (w : ℂ) : ℝ := det2 (fderiv ℝ (ambientFlow D t) w)

/-- The rescaled flow `G_t(w) = φ_t(w/√γ_t)`. -/
def Gphi (D : PathData) (t : ℝ) (w : ℂ) : ℂ := ambientFlow D t ((Real.sqrt (D.gam t))⁻¹ • w)

/-- Its density `Ĵ_t = det DG_t` (`= J^φ_t(·/√γ_t)/γ_t`, `Jhat_eq`). -/
def Jhat (D : PathData) (t : ℝ) (w : ℂ) : ℝ := det2 (fderiv ℝ (Gphi D t) w)

theorem Jphi_def (D : PathData) (t : ℝ) (w : ℂ) :
    Jphi D t w = LinearMap.det (fderiv ℝ (ambientFlow D t) w : ℂ →ₗ[ℝ] ℂ) := det2_eq _

theorem Jhat_def (D : PathData) (t : ℝ) (w : ℂ) :
    Jhat D t w = LinearMap.det (fderiv ℝ (Gphi D t) w : ℂ →ₗ[ℝ] ℂ) := det2_eq _

/-- `𝒩_t = (·/√γ_t) ∘ T_{Ĵ_t}⁻¹ ∘ D_{Ĵ_t}`. -/
def normalize (D : PathData) (t : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (D.gam t))⁻¹ • Inner.TrotInv (Jhat D) t (Inner.Darea (Jhat D) t z)

/-- **`sec:pln-normal`.** `q̂_t = φ_t ∘ 𝒩_t`. -/
def qhat (D : PathData) (t : ℝ) (z : ℂ) : ℂ := ambientFlow D t (normalize D t z)

theorem qhat_eq_Gphi (D : PathData) (t : ℝ) (z : ℂ) :
    qhat D t z = Gphi D t (Inner.TrotInv (Jhat D) t (Inner.Darea (Jhat D) t z)) := rfl

/-! ### Generic lemmas -/

theorem Trot_congr {J J' : ℝ → ℂ → ℝ} {s s' : ℝ} (h : J s = J' s') :
    Inner.Trot J s = Inner.Trot J' s' := by
  unfold Inner.Trot Inner.Bfun Inner.Jbar
  simp only [h]

theorem TrotInv_congr {J J' : ℝ → ℂ → ℝ} {s s' : ℝ} (h : J s = J' s') :
    Inner.TrotInv J s = Inner.TrotInv J' s' := by
  unfold Inner.TrotInv
  rw [Trot_congr h]

theorem Darea_congr {J J' : ℝ → ℂ → ℝ} {s s' : ℝ} (h : J s = J' s') :
    Inner.Darea J s = Inner.Darea J' s' := by
  unfold Inner.Darea Inner.Einv Inner.Acal Inner.Jbar
  simp only [h]

theorem Acal_congr {J J' : ℝ → ℂ → ℝ} {s s' : ℝ} (h : J s = J' s') :
    Inner.Acal J s = Inner.Acal J' s' := by
  unfold Inner.Acal Inner.Jbar
  simp only [h]

theorem det_fderiv_of_eventuallyEq_id {f : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[𝓝 w] id) :
    LinearMap.det (fderiv ℝ f w : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [h.fderiv_eq, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id]

theorem image_smul_closedBall {a r : ℝ} (ha : 0 < a) :
    (fun w : ℂ => a • w) '' closedBall 0 r = closedBall 0 (a * r) := by
  rw [Set.image_smul, smul_closedBall' ha.ne', smul_zero, Real.norm_of_nonneg ha.le]

/-- The integral `∫₀^{2π} (φ - π) dφ = 0`. -/
theorem integral_sub_pi : ∫ φ in (0 : ℝ)..2 * π, (φ - π) = 0 := by
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

section normal
variable {D : PathData} (hD : OrdinaryPath D)
include hD

/-! ### Properties of `γ_t` -/

theorem gam_pos (t : ℝ) : 0 < D.gam t := lt_of_lt_of_le (pow_pos hD.c_pos 2) (hD.gam_ge t)

theorem pdag_pos : 0 < D.pdag := by
  have := hD.e_pos; have := hD.four_e_lt_h; have := hD.pplus_lt_pdag; linarith

theorem zero_mem_disk : (0 : ℂ) ∈ areaDisk D.pdag := by
  simp only [areaDisk, mem_ofPred_eq, norm_zero]; norm_num; exact pdag_pos hD

theorem Psupp_nonneg : 0 ≤ D.Psupp :=
  le_trans (by positivity) (hD.image 0 0 (zero_mem_disk hD))

theorem gam_of_nonpos {t : ℝ} (ht : t ≤ 0) : D.gam t = 1 := by
  rw [← hD.det t 0 (zero_mem_disk hD)]
  apply det_fderiv_of_eventuallyEq_id
  filter_upwards [(isOpen_areaDisk _).mem_nhds (zero_mem_disk hD)] with w hw
  exact hD.eq_id t ht w hw

theorem gam_of_one_le {t : ℝ} (ht : 1 ≤ t) : D.gam t = 1 := by
  rw [← hD.gam_one, ← hD.det t 0 (zero_mem_disk hD), ← hD.det 1 0 (zero_mem_disk hD)]
  have hev : D.path t =ᶠ[𝓝 (0 : ℂ)] D.path 1 := by
    filter_upwards [(isOpen_areaDisk _).mem_nhds (zero_mem_disk hD)] with w hw
    exact hD.eq_one t ht w hw
  rw [hev.fderiv_eq]

theorem sqrt_gam_pos (t : ℝ) : 0 < Real.sqrt (D.gam t) := Real.sqrt_pos.mpr (gam_pos hD t)

theorem norm_sq_smul_inv_sqrt (t : ℝ) (w : ℂ) :
    ‖(Real.sqrt (D.gam t))⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / D.gam t := by
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr (sqrt_gam_pos hD t).le), inv_pow,
    Real.sq_sqrt (gam_pos hD t).le]
  ring

theorem invSqrtGam_contDiff : ContDiff ℝ ∞ (fun t => (Real.sqrt (D.gam t))⁻¹) :=
  (hD.gam_smooth.sqrt fun t => (gam_pos hD t).ne').inv fun t => (sqrt_gam_pos hD t).ne'

/-! ### The rescaled flow and its density -/

theorem Gphi_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Gphi D p.1 p.2) :=
  (ambientFlow_smooth hD).comp (contDiff_fst.prodMk
    (((invSqrtGam_contDiff hD).comp contDiff_fst).smul contDiff_snd))

theorem Gphi_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (Gphi D t) :=
  (Gphi_smooth hD).comp (contDiff_const.prodMk contDiff_id)

theorem Gphi_bijective (t : ℝ) : Function.Bijective (Gphi D t) := by
  have hs := (sqrt_gam_pos hD t).ne'
  have hsm : Function.Bijective (fun w : ℂ => (Real.sqrt (D.gam t))⁻¹ • w) :=
    ⟨fun a b h => smul_right_injective ℂ (inv_ne_zero hs) h,
      fun y => ⟨Real.sqrt (D.gam t) • y, by
        show (Real.sqrt (D.gam t))⁻¹ • (Real.sqrt (D.gam t) • y) = y
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul]⟩⟩
  exact (ambientFlow_bijective hD t).comp hsm

theorem fderiv_Gphi (t : ℝ) (w : ℂ) : fderiv ℝ (Gphi D t) w =
    (fderiv ℝ (ambientFlow D t) ((Real.sqrt (D.gam t))⁻¹ • w)).comp
      ((Real.sqrt (D.gam t))⁻¹ • ContinuousLinearMap.id ℝ ℂ) := by
  have h1 : HasFDerivAt (fun w : ℂ => (Real.sqrt (D.gam t))⁻¹ • w)
      ((Real.sqrt (D.gam t))⁻¹ • ContinuousLinearMap.id ℝ ℂ) w :=
    ((Real.sqrt (D.gam t))⁻¹ • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
  have h2 := ((ambientFlow_slice_smooth hD t).differentiable (by simp) _).hasFDerivAt.comp w h1
  exact h2.fderiv

/-- `Ĵ_t(w) = J^φ_t(w/√γ_t)/γ_t`. -/
theorem Jhat_eq (t : ℝ) (w : ℂ) :
    Jhat D t w = Jphi D t ((Real.sqrt (D.gam t))⁻¹ • w) / D.gam t := by
  rw [Jhat_def, Jphi_def, fderiv_Gphi hD, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_id, LinearMap.det_smul,
    LinearMap.det_id, Complex.finrank_real_complex, inv_pow, Real.sq_sqrt (gam_pos hD t).le]
  ring

theorem Jhat_pos (t : ℝ) (w : ℂ) : 0 < Jhat D t w := by
  rw [Jhat_eq hD, Jphi_def]; exact div_pos (ambientFlow_det_pos hD t _) (gam_pos hD t)

theorem Jhat_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Jhat D p.1 p.2) := by
  have hF := ContDiff.fderiv (f := fun (q : ℝ × ℂ) (y : ℂ) => Gphi D q.1 y) (g := fun q => q.2)
    ((Gphi_smooth hD).comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (m := ∞) (n := ∞) (by simp)
  have he : (fun p : ℝ × ℂ => Jhat D p.1 p.2) = fun p =>
      (fderiv ℝ (Gphi D p.1) p.2 1).re * (fderiv ℝ (Gphi D p.1) p.2 Complex.I).im -
        (fderiv ℝ (Gphi D p.1) p.2 1).im * (fderiv ℝ (Gphi D p.1) p.2 Complex.I).re := by
    funext p; rfl
  rw [he]
  have h1 := hF.clm_apply (contDiff_const (c := (1 : ℂ)))
  have hI := hF.clm_apply (contDiff_const (c := Complex.I))
  exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp hI)).sub
    ((Complex.imCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp hI))

theorem Jhat_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (Jhat D t) := by
  have he : Jhat D t = det2 ∘ fderiv ℝ (Gphi D t) := rfl
  rw [he]
  exact det2_contDiff.comp ((Gphi_slice_smooth hD t).fderiv_right (m := ∞) (by simp))

/-- On the rescaled core `π|w|² ≤ γ_t p_on`, `Ĵ_t = 1`. -/
theorem Jhat_core {t : ℝ} {w : ℂ} (hw : π * ‖w‖ ^ 2 ≤ D.gam t * pon D) : Jhat D t w = 1 := by
  rw [Jhat_eq hD]
  have hz : π * ‖(Real.sqrt (D.gam t))⁻¹ • w‖ ^ 2 ≤ pon D := by
    rw [norm_sq_smul_inv_sqrt hD, mul_div_assoc', div_le_iff₀ (gam_pos hD t), mul_comm (pon D)]
    exact hw
  rw [Jphi_def, ambientFlow_det hD hz t, div_self (gam_pos hD t).ne']

/-- On the rescaled collar `π|w|²/γ_t > P_supp`, `Ĵ_t = 1/γ_t`. -/
theorem Jhat_collar {t : ℝ} {w : ℂ} (hw : D.Psupp < π * ‖w‖ ^ 2 / D.gam t) :
    Jhat D t w = 1 / D.gam t := by
  rw [Jhat_eq hD]
  congr 1
  rw [Jphi_def]
  apply det_fderiv_of_eventuallyEq_id
  have hz : D.Psupp < π * ‖(Real.sqrt (D.gam t))⁻¹ • w‖ ^ 2 := by
    rw [norm_sq_smul_inv_sqrt hD, mul_div_assoc']; exact hw
  have hO : IsOpen {y : ℂ | D.Psupp < π * ‖y‖ ^ 2} := isOpen_lt continuous_const continuous_area
  filter_upwards [hO.mem_nhds hz] with y hy
  exact ambientFlow_eq_id hD hy t

theorem Gphi_image {t R : ℝ} (hR : 0 ≤ R) (hRs : D.Psupp ≤ π * R ^ 2) :
    Gphi D t '' closedBall 0 (Real.sqrt (D.gam t) * R) = closedBall 0 R := by
  have hs := sqrt_gam_pos hD t
  have h1 : Gphi D t = ambientFlow D t ∘ fun w => (Real.sqrt (D.gam t))⁻¹ • w := rfl
  rw [h1, Set.image_comp, image_smul_closedBall (inv_pos.mpr hs), ← mul_assoc,
    inv_mul_cancel₀ hs.ne', one_mul]
  have hcl : closedBall (0 : ℂ) R = closedAreaDisk (π * R ^ 2) := by
    rw [closedAreaDisk_eq _ (by positivity), mul_div_cancel_left₀ _ Real.pi_ne_zero,
      Real.sqrt_sq hR]
  rw [hcl]
  exact ambientFlow_disk hD hRs t

/-- **Collar.** `𝓐_{Ĵ_t}(E) = πE/γ_t` for `E ≥ γ_t P_supp/π`. -/
theorem Acal_collar {t E : ℝ} (hE : D.gam t * D.Psupp / π ≤ E) :
    Inner.Acal (Jhat D) t E = π * E / D.gam t := by
  have hg := gam_pos hD t
  have hE0 : 0 ≤ E := le_trans (by have := Psupp_nonneg hD; positivity) hE
  set R := Real.sqrt (E / D.gam t)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = E / D.gam t := Real.sq_sqrt (div_nonneg hE0 hg.le)
  have hRs : D.Psupp ≤ π * R ^ 2 := by
    rw [hR2, mul_div_assoc', le_div_iff₀ hg]
    rw [div_le_iff₀ Real.pi_pos] at hE; linarith
  have hρ : (Real.sqrt (D.gam t) * R) ^ 2 = E := by
    rw [mul_pow, Real.sq_sqrt hg.le, hR2]; field_simp
  have h := Acal_eq_of_image ((Gphi_slice_smooth hD t).of_le (by simp))
    (Gphi_bijective hD t).1 (fun w => by rw [← Jhat_def]; exact (Jhat_pos hD t w).le) (by positivity) hR
    (Gphi_image hD hR hRs)
  rw [hρ] at h
  rw [Acal_congr (J' := fun _ w => LinearMap.det (fderiv ℝ (Gphi D t) w : ℂ →ₗ[ℝ] ℂ))
    (s' := 0) (funext fun w => Jhat_def D t w), h, hR2]
  ring

theorem Acal_tendsto (t : ℝ) : Tendsto (Inner.Acal (Jhat D) t) atTop atTop := by
  have hlin : Tendsto (fun E : ℝ => π * E / D.gam t) atTop atTop := by
    have := (tendsto_id.const_mul_atTop Real.pi_pos).atTop_div_const (gam_pos hD t)
    simpa using this
  refine hlin.congr' ?_
  filter_upwards [eventually_ge_atTop (D.gam t * D.Psupp / π)] with E hE
  exact (Acal_collar hD hE).symm

/-- The flat radius `ρ_c = c √(p_on/π)`: `Ĵ_t = 1` on `|w| ≤ ρ_c` for every `t`. -/
def rhoC (D : PathData) : ℝ := D.c * Real.sqrt (pon D / π)

theorem rhoC_pos : 0 < rhoC D :=
  mul_pos hD.c_pos (Real.sqrt_pos.mpr (div_pos (pon_pos hD) Real.pi_pos))

theorem Jhat_flat {t : ℝ} {w : ℂ} (hw : ‖w‖ ≤ rhoC D) : Jhat D t w = 1 := by
  apply Jhat_core hD
  have h1 : ‖w‖ ^ 2 ≤ D.c ^ 2 * (pon D / π) := by
    calc ‖w‖ ^ 2 ≤ rhoC D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = D.c ^ 2 * (pon D / π) := by
        unfold rhoC; rw [mul_pow, Real.sq_sqrt (div_pos (pon_pos hD) Real.pi_pos).le]
  have h2 : π * ‖w‖ ^ 2 ≤ D.c ^ 2 * pon D := by
    have := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    rwa [show π * (D.c ^ 2 * (pon D / π)) = D.c ^ 2 * pon D by field_simp] at this
  exact h2.trans (mul_le_mul_of_nonneg_right (hD.gam_ge t) (pon_pos hD).le)

/-- `Ĵ` is a flat density family in the sense of `sec:pln-normalisation-maps` (constant `1` on `|w| ≤ ρ_c`). -/
theorem Jhat_flatDensity (a b : ℝ) : Inner.FlatDensity (Jhat D) a b 1 (rhoC D) where
  smooth := Jhat_smooth hD
  pos := fun t _ w => Jhat_pos hD t w
  flat := fun t _ w hw => Jhat_flat hD hw
  j_pos := one_pos
  ρ₀_pos := rhoC_pos hD
  tendsto := fun t _ => Acal_tendsto hD t

/-- The constant family `s ↦ Ĵ_t` is flat on any radius `ρ` on which `Ĵ_t = 1`. -/
theorem Jhat_flatDensity_const (t : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hflat : ∀ w : ℂ, ‖w‖ ≤ ρ → Jhat D t w = 1) :
    Inner.FlatDensity (fun _ => Jhat D t) (t - 1) (t + 1) 1 ρ where
  smooth := (Jhat_slice_smooth hD t).comp contDiff_snd
  pos := fun _ _ w => Jhat_pos hD t w
  flat := fun _ _ w hw => hflat w hw
  j_pos := one_pos
  ρ₀_pos := hρ
  tendsto := fun _ _ => Acal_tendsto hD t

omit hD in
theorem mem_Ioo_self (t : ℝ) : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩

/-- Where `Ĵ_t = 1` on `|w| ≤ ρ`, `q̂_t = G_t` on `|z| ≤ ρ`. -/
theorem qhat_eq_Gphi_of_flat {t ρ : ℝ} (hρ : 0 < ρ) (hflat : ∀ w : ℂ, ‖w‖ ≤ ρ → Jhat D t w = 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) : qhat D t z = Gphi D t z := by
  have hJ := Jhat_flatDensity_const hD t hρ hflat
  have h := Inner.normalize_eq_of_const hJ (mem_Ioo_self t) (Gphi D t)
    (z := z) (by rw [Real.sqrt_one, one_mul]; exact hz)
  rw [Real.sqrt_one, Complex.ofReal_one, div_one] at h
  exact h

/-! ### `lem:pln-normalisation` -/

/-! ### `thm:pln-isotopy` -/

/-- **`thm:pln-isotopy` (b).** Core: `q̂_t(z) = φ_t(z/√γ_t) = 𝔢_t(z/√γ_t)` for `π|z|² ≤ γ_t p_on`
(in particular on the common core `π|z|² ≤ c² p_on`). -/
theorem qhat_core {t : ℝ} {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.gam t * pon D) :
    qhat D t z = ambientFlow D t ((Real.sqrt (D.gam t))⁻¹ • z) ∧
      qhat D t z = D.path t ((Real.sqrt (D.gam t))⁻¹ • z) := by
  have hg := gam_pos hD t
  set ρ := Real.sqrt (D.gam t * pon D / π)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (div_pos (mul_pos hg (pon_pos hD)) Real.pi_pos)
  have hρ2 : ρ ^ 2 = D.gam t * pon D / π := Real.sq_sqrt (by have := pon_pos hD; positivity)
  have hflat : ∀ w : ℂ, ‖w‖ ≤ ρ → Jhat D t w = 1 := by
    intro w hw
    apply Jhat_core hD
    have := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [hρ2, le_div_iff₀ Real.pi_pos] at this
    linarith
  have hzρ : ‖z‖ ≤ ρ := by
    rw [← Real.sqrt_sq (norm_nonneg z)]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ Real.pi_pos]; linarith
  have h1 := qhat_eq_Gphi_of_flat hD hρ hflat hzρ
  refine ⟨h1, ?_⟩
  rw [h1]
  apply ambientFlow_eq_ordPath hD
  rw [norm_sq_smul_inv_sqrt hD, mul_div_assoc', div_le_iff₀ hg]
  linarith

/-- **`thm:pln-isotopy` (c).** Collar: `q̂_t = id` on `{π|z|² > P_supp}`. -/
theorem qhat_collar {t : ℝ} {z : ℂ} (hz : D.Psupp < π * ‖z‖ ^ 2) : qhat D t z = z := by
  have hg := gam_pos hD t
  have hs := sqrt_gam_pos hD t
  have hJ := Jhat_flatDensity hD (t - 1) (t + 1)
  have ht := mem_Ioo_self t
  have hz0 : 0 < ‖z‖ := by
    rcases (norm_nonneg z).eq_or_lt with h | h
    · rw [← h] at hz; have := Psupp_nonneg hD; simp at hz; linarith
    · exact h
  -- the area normalisation is the scaling by `√γ_t`
  have hE : Inner.Einv (Jhat D) t (π * ‖z‖ ^ 2) = D.gam t * ‖z‖ ^ 2 := by
    have hA : Inner.Acal (Jhat D) t (D.gam t * ‖z‖ ^ 2) = π * ‖z‖ ^ 2 := by
      rw [Acal_collar hD]
      · field_simp
      · rw [div_le_iff₀ Real.pi_pos]
        have := mul_le_mul_of_nonneg_left hz.le hg.le
        linarith
    rw [← hA, Inner.Einv_Acal hJ ht]
  have hDz : Inner.Darea (Jhat D) t z = ((Real.sqrt (D.gam t) : ℝ) : ℂ) * z := by
    unfold Inner.Darea
    rw [hE]
    congr 3
    field_simp
  -- the rotation normalisation is the identity on the collar circle
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((Real.sqrt (D.gam t) : ℝ) : ℂ) * z := ⟨_, rfl⟩
  rw [← hw] at hDz
  have hnw : ‖w‖ = Real.sqrt (D.gam t) * ‖z‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hcirc : ∀ φ : ℝ, Jhat D t (Inner.Rot φ w) = 1 / D.gam t := by
    intro φ
    apply Jhat_collar hD
    rw [Inner.norm_Rot, hnw, mul_pow, Real.sq_sqrt hg.le]
    field_simp
    linarith
  have hB : Inner.Bfun (Jhat D) t w = 0 := by
    unfold Inner.Bfun
    simp only [hcirc]
    rw [intervalIntegral.integral_mul_const, integral_sub_pi, zero_mul, mul_zero]
  have hT : Inner.Trot (Jhat D) t w = w := by
    unfold Inner.Trot; rw [hB, zero_div, Inner.Rot_zero]
  have hTi : Inner.TrotInv (Jhat D) t w = w := Inner.TrotInv_eq_of (hJ.bij ht).1 hT
  unfold qhat normalize
  rw [hDz, hTi]
  have : (Real.sqrt (D.gam t))⁻¹ • w = z := by
    rw [hw, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne',
      Complex.ofReal_one, one_mul]
  rw [this]
  exact ambientFlow_eq_id hD hz t

/-- **`thm:pln-isotopy` (d).** `(t, z) ↦ q̂_t(z)` is jointly `C^∞`. -/
theorem qhat_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhat D p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, z⟩
  have hJ := Jhat_flatDensity hD (t - 1) (t + 1)
  have h := (Inner.normalize_param_smooth hJ (F := Gphi D) (Gphi_smooth hD).contDiffOn
    (fun s _ w => (Jhat_def D s w).symm)).1
  exact h.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨mem_Ioo_self t, mem_univ _⟩)

theorem qhat_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (qhat D t) :=
  (qhat_smooth hD).comp (contDiff_const.prodMk contDiff_id)

/-- **`thm:pln-isotopy` (a).** `q̂_t` is symplectic: `det Dq̂_t = 1`. -/
theorem qhat_symplectic (t : ℝ) (z : ℂ) :
    LinearMap.det (fderiv ℝ (qhat D t) z : ℂ →ₗ[ℝ] ℂ) = 1 :=
  (Inner.normalize_param_smooth (Jhat_flatDensity hD (t - 1) (t + 1)) (F := Gphi D)
    (Gphi_smooth hD).contDiffOn (fun s _ w => (Jhat_def D s w).symm)).2.1 t (mem_Ioo_self t) z

/-- **`thm:pln-isotopy` (a).** `q̂_t` is a bijection of `ℂ`. -/
theorem qhat_bijective (t : ℝ) : Function.Bijective (qhat D t) := by
  have hJ := Jhat_flatDensity hD (t - 1) (t + 1)
  have ht := mem_Ioo_self t
  have hTi : Function.Bijective (Inner.TrotInv (Jhat D) t) :=
    ⟨Function.LeftInverse.injective (g := Inner.Trot (Jhat D) t)
      (fun y => Inner.Trot_TrotInv hJ ht y),
      fun y => ⟨Inner.Trot (Jhat D) t y, Inner.TrotInv_Trot hJ ht y⟩⟩
  have h : qhat D t = Gphi D t ∘ Inner.TrotInv (Jhat D) t ∘ Inner.Darea (Jhat D) t := rfl
  rw [h]
  exact (Gphi_bijective hD t).comp (hTi.comp (Inner.Darea_bijective hJ ht))

/-- **`thm:pln-isotopy` (a).** `q̂_t` maps `D̄(P)` onto itself for `P ≥ P_supp`. -/
theorem qhat_disk {P : ℝ} (hP : D.Psupp ≤ P) (t : ℝ) :
    qhat D t '' closedAreaDisk P = closedAreaDisk P :=
  image_eq_of_fixed (qhat_bijective hD t) (A := closedAreaDisk D.Psupp)
    (fun y hy => qhat_collar hD (not_le.mp hy)) (fun z hz => le_trans hz hP)

/-- **`thm:pln-isotopy` (a).** `q̂_t` maps `D(P)` onto itself for `P > P_supp`; in particular
`q̂_t(D(h)) = D(h)`. -/
theorem qhat_openDisk {P : ℝ} (hP : D.Psupp < P) (t : ℝ) :
    qhat D t '' areaDisk P = areaDisk P :=
  image_eq_of_fixed (qhat_bijective hD t) (A := closedAreaDisk D.Psupp)
    (fun y hy => qhat_collar hD (not_le.mp hy)) (fun z hz => lt_of_le_of_lt hz hP)

/-- If `φ_t = id` and `γ_t = 1`, then `q̂_t = id`. -/
theorem qhat_eq_id_of {t : ℝ} (hφ : ambientFlow D t = id) (hγ : D.gam t = 1) :
    qhat D t = id := by
  have hG : Gphi D t = id := by
    funext w; simp [Gphi, hφ, hγ]
  have hJ1 : ∀ w, Jhat D t w = 1 := fun w => by
    rw [Jhat_def, hG, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
  funext z
  have h := qhat_eq_Gphi_of_flat hD (ρ := ‖z‖ + 1) (by positivity) (fun w _ => hJ1 w)
    (le_of_lt (lt_add_one _))
  rw [h, hG]

/-- **`thm:pln-isotopy` (e).** `q̂_0 = id`. -/
theorem qhat_zero : qhat D 0 = id :=
  qhat_eq_id_of hD (ambientFlow_zero hD) (gam_of_nonpos hD le_rfl)

theorem qhat_of_nonpos {t : ℝ} (ht : t ≤ 0) : qhat D t = id :=
  qhat_eq_id_of hD (funext fun y => ambientFlow_of_nonpos hD ht y) (gam_of_nonpos hD ht)

theorem qhat_of_one_le {t : ℝ} (ht : 1 ≤ t) : qhat D t = qhat D 1 := by
  have hG : Gphi D t = Gphi D 1 := by
    funext w
    simp only [Gphi]
    rw [gam_of_one_le hD ht, ambientFlow_of_one_le hD ht, hD.gam_one]
  have hJ : Jhat D t = Jhat D 1 := by
    funext w; unfold Jhat; rw [hG]
  funext z
  rw [qhat_eq_Gphi, qhat_eq_Gphi, hG, TrotInv_congr (J' := Jhat D) (s' := 1) hJ,
    Darea_congr (J' := Jhat D) (s' := 1) hJ]

/-! ### `thm:pln-isotopy` -/

/-- **`thm:pln-isotopy`.** `q̂_1 = 𝔢_1` on `{π|z|² ≤ p_on}` (`⊇ {π|z|² ≤ h - 4e}`). -/
theorem qhat_one_eq {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pon D) : qhat D 1 z = D.path 1 z := by
  have h := (qhat_core hD (t := 1) (z := z) (by rw [hD.gam_one, one_mul]; exact hz)).2
  rwa [hD.gam_one, Real.sqrt_one, inv_one, one_smul] at h

/-- **`thm:pln-isotopy`, generic form.** If the endpoint `𝔢_1` satisfies the comparison
`R(π|𝔢_1 z|²) < π|z|² + 13e/24` on `{π|z|² ≤ h - 4e}` (estimate (5) of
`prop:pll-comparison` for `𝔢_1 = C ∘ f`), and `R ≤ h` on `[0,h]`, then
`R(π|q̂_1 z|²) ≤ π|z|² + 4e` on `D̄(h)`. -/
theorem R_q_le {R : ℝ → ℝ} (hR : ∀ x ∈ Icc 0 D.h, R x ≤ D.h)
    (hcmp : ∀ z : ℂ, π * ‖z‖ ^ 2 ≤ D.h - 4 * D.e →
      R (π * ‖D.path 1 z‖ ^ 2) < π * ‖z‖ ^ 2 + 13 * D.e / 24)
    {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h) : R (π * ‖qhat D 1 z‖ ^ 2) ≤ π * ‖z‖ ^ 2 + 4 * D.e := by
  have he := hD.e_pos
  rcases le_or_gt (π * ‖z‖ ^ 2) (D.h - 4 * D.e) with h1 | h1
  · rw [qhat_one_eq hD (h1.trans (pon_bounds hD).1.le)]
    linarith [hcmp z h1]
  · have hq : qhat D 1 z ∈ closedAreaDisk D.h := by
      rw [← qhat_disk hD hD.Psupp_lt_h.le 1]; exact ⟨z, hz, rfl⟩
    have := hR _ ⟨by positivity, hq⟩
    linarith

end normal

/-! ### The comparison with the parameters of `sec:pll-setting` -/

theorem Rcal_le_h (P : Params) {x : ℝ} (hx : x ∈ Icc 0 P.h) : P.Rcal x ≤ P.h := by
  have ha := P.a_pos
  have hah := P.a_lt_h
  unfold Params.Rcal
  split_ifs with h
  · have hA : P.A * P.a = P.h := by unfold Params.A; field_simp
    nlinarith [P.A_pos, hx.1]
  · have hB : P.B * (P.h - P.a) = P.h := by
      unfold Params.B; field_simp [(sub_pos.mpr hah).ne']
    nlinarith [P.B_pos, hx.2]

section params
variable {D : PathData} (hD : OrdinaryPath D) (P : Params) (hh : D.h = P.h) (he : D.e = P.eq_)
include hD hh he

/-- **`thm:pln-isotopy`, (1).** `Rcal(p(q z)) ≤ I + 4e_q` on `D̄(h)`, `q = q̂_1`, `p = π|·|²`,
given estimate (5) for the endpoint `𝔢_1 = C ∘ f`. -/
theorem Rcal_q_le
    (hcmp : ∀ z : ℂ, π * ‖z‖ ^ 2 ≤ P.h - 4 * P.eq_ →
      P.Rcal (π * ‖D.path 1 z‖ ^ 2) < π * ‖z‖ ^ 2 + 13 * P.eq_ / 24)
    {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ P.h) :
    P.Rcal (π * ‖qhat D 1 z‖ ^ 2) ≤ π * ‖z‖ ^ 2 + 4 * P.eq_ := by
  have := R_q_le hD (R := P.Rcal) (fun x hx => hh ▸ Rcal_le_h P (hh ▸ hx))
    (fun z hz => he ▸ hcmp z (hh ▸ he ▸ hz)) (hh ▸ hz)
  rwa [he] at this

/-- **`thm:pln-isotopy`, (1).** `K(I) - F(p(q z)) ≥ 31g/32` on `D̄(h)`. -/
theorem K_sub_F_q_ge
    (hcmp : ∀ z : ℂ, π * ‖z‖ ^ 2 ≤ P.h - 4 * P.eq_ →
      P.Rcal (π * ‖D.path 1 z‖ ^ 2) < π * ‖z‖ ^ 2 + 13 * P.eq_ / 24)
    {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ P.h) :
    31 * P.g / 32 ≤ P.K (π * ‖z‖ ^ 2) - P.F (π * ‖qhat D 1 z‖ ^ 2) :=
  P.K_sub_F_ge (Rcal_q_le hD P hh he hcmp hz)

end params

end SymplecticPacking.Qhat
