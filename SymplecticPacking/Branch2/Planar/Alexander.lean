import SymplecticPacking.Branch2.Planar.FiveGeneric

/-!
# The Alexander family of an area-preserving embedding

For a globally smooth `Φ : ℂ → ℂ` which is area preserving and injective on `D(p†)`, the family

  `q_σ(z) = Φ(0) + ∫₀¹ DΦ(tσz) z dt`   (`= Φ(0) + (Φ(σz) − Φ(0))/σ` for `σ ≠ 0`)

is jointly smooth, `q_0 = Φ(0) + DΦ(0)`, `q_1 = Φ`, and every `q_σ` (`σ ∈ [0,1]`) is an
area-preserving embedding of `D(p†)` with `|q_σ − Φ(0)| ≤ M R†`, `M = sup_{D̄(p†)} ‖DΦ‖`.
It is the inner family of the generic five-segment path (`FiveGeneric.lean`).
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Filter Topology Set Complex
open scoped ContDiff Real

/-- Input of the Alexander family. -/
structure AlexInput where
  Φ : ℂ → ℂ
  A11 : ℝ
  A22 : ℝ
  h : ℝ
  pdag : ℝ
  Rq : ℝ

namespace AlexInput

variable (D : AlexInput)

/-- The source disk. -/
def srcDisk : Set ℂ := {z | π * ‖z‖ ^ 2 < D.pdag}

/-- `𝐀₀ = diag(A₁₁, A₂₂)`. -/
def A0 : ℂ →L[ℝ] ℂ :=
  ofRealCLM.comp (D.A11 • reCLM) + (ofRealCLM.comp (D.A22 • imCLM)).smulRight I

/-- Hypotheses. -/
structure Hyp : Prop where
  smooth : ContDiff ℝ ∞ D.Φ
  det : ∀ z ∈ D.srcDisk, LinearMap.det (fderiv ℝ D.Φ z : ℂ →ₗ[ℝ] ℂ) = 1
  injOn : InjOn D.Φ D.srcDisk
  deriv_zero : fderiv ℝ D.Φ 0 = D.A0
  A11_neg : D.A11 < 0
  A22_neg : D.A22 < 0
  A11_mul_A22 : D.A11 * D.A22 = 1
  pdag_pos : 0 < D.pdag
  pdag_lt_h : D.pdag < D.h
  b_lt : ‖D.Φ 0‖ < √(D.h / π)
  bound_one : ∀ z ∈ D.srcDisk, ‖D.Φ z‖ ≤ D.Rq
  Rq_lt : D.Rq < √(D.h / π)

/-- The Hadamard quotient `G(σ, z) = ∫₀¹ DΦ(tσz) z dt`. -/
def Gq (σ : ℝ) (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) z

/-- The Alexander family `q_σ = Φ(0) + G(σ, ·)`. -/
def q (σ : ℝ) (z : ℂ) : ℂ := D.Φ 0 + D.Gq σ z

/-- `M = sup_{D̄(p†)} ‖DΦ‖`. -/
def Mder : ℝ := sSup ((fun w => ‖fderiv ℝ D.Φ w‖) '' {z : ℂ | π * ‖z‖ ^ 2 ≤ D.pdag})

/-- The data of the five-segment path. -/
def toFam : FamData where
  q := D.q
  b := D.Φ 0
  A11 := D.A11
  A22 := D.A22
  h := D.h
  pdag := D.pdag
  Bstar := D.Mder * √(D.pdag / π)
  Rq := D.Rq

variable {D}

section hyp
variable (hD : D.Hyp)
include hD

lemma fderiv_contDiff : ContDiff ℝ ∞ (fun w => fderiv ℝ D.Φ w) :=
  hD.smooth.fderiv_right (m := ∞) le_rfl

lemma integrand_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℂ) =>
      fderiv ℝ D.Φ (((p.1 * p.2.1 : ℝ) : ℂ) * p.2.2) p.2.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℂ) => ((p.1 * p.2.1 : ℝ) : ℂ) * p.2.2) :=
    (ofRealCLM.contDiff.comp (contDiff_fst.mul contDiff_snd.fst)).mul contDiff_snd.snd
  exact ((fderiv_contDiff hD).comp h1).clm_apply contDiff_snd.snd

theorem Gq_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Gq p.1 p.2) :=
  OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral (integrand_contDiff hD)

theorem q_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.q p.1 p.2) :=
  contDiff_const.add (Gq_contDiff hD)

/-- `Φ(σz) = Φ(0) + σ G(σ, z)`. -/
theorem Phi_eq (σ : ℝ) (z : ℂ) : D.Φ ((σ : ℂ) * z) = D.Φ 0 + (σ : ℂ) * D.Gq σ z := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => D.Φ (((t * σ : ℝ) : ℂ) * z))
      (fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) ((σ : ℂ) * z)) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => ((t * σ : ℝ) : ℂ) * z) ((σ : ℂ) * z) t := by
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have := (h0.mul_const (σ : ℂ)).mul_const z
      simpa [one_mul] using this
    exact ((hD.smooth.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t hl
  have hcont : Continuous (fun t : ℝ =>
      fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) ((σ : ℂ) * z)) := by
    have := integrand_contDiff hD
    have hc : Continuous (fun t : ℝ => fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z)) :=
      (fderiv_contDiff hD).continuous.comp (by fun_prop)
    exact hc.clm_apply continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (hcont.intervalIntegrable _ _)
  have hlin : ∀ t : ℝ, fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) ((σ : ℂ) * z) =
      (σ : ℂ) * fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) z := by
    intro t
    rw [show (σ : ℂ) * z = (σ : ℝ) • z by rw [Complex.real_smul], map_smul, Complex.real_smul]
  simp_rw [hlin] at hint
  rw [intervalIntegral.integral_const_mul] at hint
  simp only [one_mul, zero_mul, Complex.ofReal_zero] at hint
  unfold Gq
  linear_combination -hint

theorem q_one (z : ℂ) : D.q 1 z = D.Φ z := by
  have := Phi_eq hD 1 z
  simp only [Complex.ofReal_one, one_mul] at this
  rw [q, this]

theorem q_zero (z : ℂ) : D.q 0 z = D.Φ 0 + D.A0 z := by
  rw [q, Gq]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, hD.deriv_zero]
  simp

/-- For `σ ≠ 0`, `q_σ(z) = Φ(0) + (Φ(σz) − Φ(0))/σ`. -/
theorem q_eq_of_ne {σ : ℝ} (hσ : σ ≠ 0) (z : ℂ) :
    D.q σ z = D.Φ 0 + (σ : ℂ)⁻¹ * (D.Φ ((σ : ℂ) * z) - D.Φ 0) := by
  rw [Phi_eq hD σ z, q]
  have : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  field_simp
  ring

lemma smul_mem_srcDisk {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ D.srcDisk) :
    (σ : ℂ) * z ∈ D.srcDisk := by
  have hz' : π * ‖z‖ ^ 2 < D.pdag := hz
  show π * ‖(σ : ℂ) * z‖ ^ 2 < D.pdag
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.1, mul_pow]
  have h1 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have h2 : 0 ≤ π * ‖z‖ ^ 2 := by positivity
  nlinarith

theorem q_fderiv {σ : ℝ} (z : ℂ) :
    HasFDerivAt (D.q σ) (fderiv ℝ D.Φ ((σ : ℂ) * z)) z := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · have he : D.q 0 = fun z => D.Φ 0 + D.A0 z := funext (q_zero hD)
    rw [he, Complex.ofReal_zero, zero_mul, hD.deriv_zero]
    exact (D.A0.hasFDerivAt).const_add _
  · have he : D.q σ = fun z => D.Φ 0 + (σ : ℂ)⁻¹ * (D.Φ ((σ : ℂ) * z) - D.Φ 0) :=
      funext (q_eq_of_ne hD hσ)
    rw [he]
    have hl : HasFDerivAt (fun z : ℂ => (σ : ℂ) * z) ((σ : ℝ) • ContinuousLinearMap.id ℝ ℂ) z := by
      have := (ContinuousLinearMap.id ℝ ℂ).hasFDerivAt (x := z) |>.const_smul (σ : ℝ)
      refine this.congr_of_eventuallyEq ?_
      exact Eventually.of_forall fun w => by simp [Complex.real_smul]
    have hΦ := ((hD.smooth.differentiable (by simp) _).hasFDerivAt).comp z hl
    have h2 := ((hΦ.sub_const (D.Φ 0)).const_smul ((σ : ℝ)⁻¹)).const_add (D.Φ 0)
    refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_fderiv ?_
    · simp [Complex.real_smul]
    · ext1 v
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_smul]
      rw [inv_mul_cancel₀ hσ, one_smul]

theorem q_det {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ D.srcDisk) :
    LinearMap.det (fderiv ℝ (D.q σ) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [(q_fderiv hD z).fderiv]
  exact hD.det _ (smul_mem_srcDisk hD hσ hz)

theorem A0_injective : Function.Injective D.A0 := by
  apply Inner.injective_of_det_ne_zero
  rw [Inner.det_eq_re_im]
  simp [A0, hD.A11_mul_A22]

theorem q_injOn {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : InjOn (D.q σ) D.srcDisk := by
  intro z₁ hz₁ z₂ hz₂ h
  rcases eq_or_ne σ 0 with rfl | hσ0
  · rw [q_zero hD, q_zero hD, add_right_inj] at h
    exact A0_injective hD h
  · rw [q_eq_of_ne hD hσ0, q_eq_of_ne hD hσ0, add_right_inj] at h
    have hs : (σ : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hσ0)
    have h' := sub_left_inj.mp (mul_left_cancel₀ hs h)
    have := hD.injOn (smul_mem_srcDisk hD hσ hz₁) (smul_mem_srcDisk hD hσ hz₂) h'
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hσ0) this

lemma closedDisk_compact : IsCompact {z : ℂ | π * ‖z‖ ^ 2 ≤ D.pdag} := by
  have hpi := Real.pi_pos
  have hsub : {z : ℂ | π * ‖z‖ ^ 2 ≤ D.pdag} ⊆ Metric.closedBall 0 √(D.pdag / π) := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [← Real.sqrt_sq (norm_nonneg z)]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hpi]; have : π * ‖z‖ ^ 2 ≤ D.pdag := hz; linarith)
  exact (isCompact_closedBall 0 _).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const) hsub

lemma norm_fderiv_le {w : ℂ} (hw : π * ‖w‖ ^ 2 ≤ D.pdag) : ‖fderiv ℝ D.Φ w‖ ≤ D.Mder := by
  apply le_csSup
  · exact (closedDisk_compact hD).bddAbove_image
      ((fderiv_contDiff hD).continuous.norm.continuousOn)
  · exact ⟨w, hw, rfl⟩

lemma Mder_nonneg : 0 ≤ D.Mder :=
  (norm_nonneg _).trans (norm_fderiv_le hD (w := 0) (by simp [hD.pdag_pos.le]))

theorem Gq_norm_le {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ D.srcDisk) :
    ‖D.Gq σ z‖ ≤ D.Mder * √(D.pdag / π) := by
  have hzR : ‖z‖ ≤ √(D.pdag / π) := by
    have hpi := Real.pi_pos
    rw [← Real.sqrt_sq (norm_nonneg z)]
    exact Real.sqrt_le_sqrt (by
      rw [le_div_iff₀ hpi]; have : π * ‖z‖ ^ 2 < D.pdag := hz; linarith)
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) z‖ ≤
      D.Mder * √(D.pdag / π) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htσ : t * σ ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg ht.1.le hσ.1, by nlinarith [ht.2, hσ.1, hσ.2, ht.1]⟩
    have hm := smul_mem_srcDisk hD htσ hz
    calc ‖fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z) z‖
        ≤ ‖fderiv ℝ D.Φ (((t * σ : ℝ) : ℂ) * z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ D.Mder * √(D.pdag / π) :=
          mul_le_mul (norm_fderiv_le hD (le_of_lt hm)) hzR (norm_nonneg _) (Mder_nonneg hD)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_one, mul_one] at this
  exact this

theorem toFam_hyp : D.toFam.Hyp where
  pdag_pos := hD.pdag_pos
  pdag_lt_h := hD.pdag_lt_h
  A11_neg := hD.A11_neg
  A22_neg := hD.A22_neg
  A11_mul_A22 := hD.A11_mul_A22
  smooth := (q_contDiff hD).contDiffOn
  q_zero := fun z => q_zero hD z
  injOn := fun σ hσ => q_injOn hD hσ
  diff := fun σ _ z _ => (q_fderiv hD (σ := σ) z).differentiableAt
  det := fun σ hσ z hz => q_det hD hσ hz
  bound := fun σ hσ z hz => by
    show ‖D.q σ z - D.Φ 0‖ ≤ D.Mder * √(D.pdag / π)
    rw [q, add_sub_cancel_left]
    exact Gq_norm_le hD hσ hz
  bound_one := fun z hz => by
    show ‖D.q 1 z‖ ≤ D.Rq
    rw [q_one hD]; exact hD.bound_one z hz
  b_lt := hD.b_lt
  Rq_lt := hD.Rq_lt

theorem toFam_q_one (z : ℂ) : D.toFam.q 1 z = D.Φ z := q_one hD z

end hyp

end AlexInput

end SymplecticPacking.Branch2.Planar
