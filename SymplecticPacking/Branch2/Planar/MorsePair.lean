import SymplecticPacking.Inner.Map

/-!
# Morse pairs and their normalised inner maps (generic form of `Inner/Morse`, `Inner/Map`,
`Inner/AreaBound`)

A *Morse pair* is a pair `X, Y : ℝ → ℝ` of smooth increasing bijections with positive derivative,
linear (`X u = a u`, `Y v = b v`) on `[-ε, ε]`. With `F_mor(u + iv) = X(u) + i Y(v)`,
`J = X'(u) Y'(v)` and the rotation/area normalisations of `Inner/Normalize.lean`,

  `f = F_mor ∘ T⁻¹ ∘ D`

is a smooth area-preserving bijection of `ℂ` with `R(Re f) + W(Im f) = E(π|z|²)`, where
`R = (X⁻¹)²`, `W = (Y⁻¹)²` and `E = 𝓐⁻¹`, and `𝓐(E)` is the area of `{R(x) + W(y) ≤ E}`.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Filter Topology Set MeasureTheory Complex
open scoped ContDiff Real

open Inner (invR Acal Einv Darea TrotInv Trot FlatDensity)

/-- A Morse pair. -/
structure MorsePair where
  X : ℝ → ℝ
  Y : ℝ → ℝ
  a : ℝ
  b : ℝ
  ε : ℝ

namespace MorsePair

variable (M : MorsePair)

/-- Hypotheses on a Morse pair. -/
structure Hyp : Prop where
  X_smooth : ContDiff ℝ ∞ M.X
  Y_smooth : ContDiff ℝ ∞ M.Y
  X_deriv_pos : ∀ u, 0 < deriv M.X u
  Y_deriv_pos : ∀ v, 0 < deriv M.Y v
  a_pos : 0 < M.a
  b_pos : 0 < M.b
  ε_pos : 0 < M.ε
  X_lin : ∀ u, |u| ≤ M.ε → M.X u = M.a * u
  Y_lin : ∀ v, |v| ≤ M.ε → M.Y v = M.b * v
  X_top : Tendsto M.X atTop atTop
  X_bot : Tendsto M.X atBot atBot
  Y_top : Tendsto M.Y atTop atTop
  Y_bot : Tendsto M.Y atBot atBot

/-- `F_mor(u + iv) = X(u) + i Y(v)`. -/
def Fmor (w : ℂ) : ℂ := (M.X w.re : ℂ) + (M.Y w.im : ℂ) * I

/-- `J(u + iv) = X'(u) Y'(v)`. -/
def J (w : ℂ) : ℝ := deriv M.X w.re * deriv M.Y w.im

/-- `J` as a constant family. -/
def JF : ℝ → ℂ → ℝ := fun _ => M.J

/-- The normalised inner map `f = F_mor ∘ T⁻¹ ∘ D`. -/
def finner (z : ℂ) : ℂ := M.Fmor (TrotInv M.JF 0 (Darea M.JF 0 z))

/-- `R = (X⁻¹)²`. -/
def Rf (x : ℝ) : ℝ := invR M.X x ^ 2

/-- `W = (Y⁻¹)²`. -/
def Wf (y : ℝ) : ℝ := invR M.Y y ^ 2

/-- The length `X(√s) - X(-√s)` of `{R ≤ s}`. -/
def Lx (s : ℝ) : ℝ := M.X √s - M.X (-√s)

/-- The density in Cartesian coordinates. -/
def K (p : ℝ × ℝ) : ℝ := deriv M.X p.1 * deriv M.Y p.2

@[simp] lemma Fmor_re (w : ℂ) : (M.Fmor w).re = M.X w.re := by simp [Fmor]

@[simp] lemma Fmor_im (w : ℂ) : (M.Fmor w).im = M.Y w.im := by simp [Fmor]

variable {M}

lemma zero_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

section hyp
variable (hM : M.Hyp)
include hM

lemma X_strictMono : StrictMono M.X := strictMono_of_deriv_pos hM.X_deriv_pos
lemma Y_strictMono : StrictMono M.Y := strictMono_of_deriv_pos hM.Y_deriv_pos

lemma X_apply_inv (x : ℝ) : M.X (invR M.X x) = x :=
  Inner.apply_invR' hM.X_smooth.continuous (X_strictMono hM) hM.X_top hM.X_bot x

lemma Y_apply_inv (y : ℝ) : M.Y (invR M.Y y) = y :=
  Inner.apply_invR' hM.Y_smooth.continuous (Y_strictMono hM) hM.Y_top hM.Y_bot y

lemma inv_X_apply (u : ℝ) : invR M.X (M.X u) = u := Inner.invR_apply' (X_strictMono hM) u
lemma inv_Y_apply (v : ℝ) : invR M.Y (M.Y v) = v := Inner.invR_apply' (Y_strictMono hM) v

lemma inv_X_continuous : Continuous (invR M.X) :=
  Inner.invR_continuous hM.X_smooth.continuous (X_strictMono hM) hM.X_top hM.X_bot

lemma inv_Y_continuous : Continuous (invR M.Y) :=
  Inner.invR_continuous hM.Y_smooth.continuous (Y_strictMono hM) hM.Y_top hM.Y_bot

lemma Rf_X (u : ℝ) : M.Rf (M.X u) = u ^ 2 := by rw [Rf, inv_X_apply hM]
lemma Wf_Y (v : ℝ) : M.Wf (M.Y v) = v ^ 2 := by rw [Wf, inv_Y_apply hM]

lemma X_zero : M.X 0 = 0 := by rw [hM.X_lin 0 (by simp [hM.ε_pos.le]), mul_zero]

lemma Rf_continuous : Continuous M.Rf := (inv_X_continuous hM).pow 2
lemma Wf_continuous : Continuous M.Wf := (inv_Y_continuous hM).pow 2

lemma Rf_nonneg (x : ℝ) : 0 ≤ M.Rf x := sq_nonneg _
lemma Wf_nonneg (y : ℝ) : 0 ≤ M.Wf y := sq_nonneg _

/-- `{R ≤ s} = [X(-√s), X(√s)]`. -/
theorem Rf_le_iff {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    M.Rf x ≤ s ↔ M.X (-√s) ≤ x ∧ x ≤ M.X √s := by
  rw [Rf, Real.sq_le hs,
    ← (X_strictMono hM).le_iff_le (a := -√s) (b := invR M.X x),
    ← (X_strictMono hM).le_iff_le (a := invR M.X x) (b := √s), X_apply_inv hM]

/-- `{W ≤ s} = [Y(-√s), Y(√s)]`. -/
theorem Wf_le_iff {s : ℝ} (hs : 0 ≤ s) (y : ℝ) :
    M.Wf y ≤ s ↔ M.Y (-√s) ≤ y ∧ y ≤ M.Y √s := by
  rw [Wf, Real.sq_le hs,
    ← (Y_strictMono hM).le_iff_le (a := -√s) (b := invR M.Y y),
    ← (Y_strictMono hM).le_iff_le (a := invR M.Y y) (b := √s), Y_apply_inv hM]

lemma contDiff_deriv_X : ContDiff ℝ ∞ (deriv M.X) :=
  (contDiff_infty_iff_deriv.mp hM.X_smooth).2

lemma contDiff_deriv_Y : ContDiff ℝ ∞ (deriv M.Y) :=
  (contDiff_infty_iff_deriv.mp hM.Y_smooth).2

lemma X_deriv_lin {u : ℝ} (hu : |u| ≤ M.ε) : deriv M.X u = M.a := by
  refine Inner.deriv_eq_of_closed hM.X_smooth hM.ε_pos (fun x hx => ?_) hu
  have hev : M.X =ᶠ[𝓝 x] fun u => M.a * u := by
    have : Ioo (-M.ε) M.ε ∈ 𝓝 x := isOpen_Ioo.mem_nhds (abs_lt.mp hx)
    filter_upwards [this] with y hy
    exact hM.X_lin y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  rw [hev.deriv_eq]; simp

lemma Y_deriv_lin {v : ℝ} (hv : |v| ≤ M.ε) : deriv M.Y v = M.b := by
  refine Inner.deriv_eq_of_closed hM.Y_smooth hM.ε_pos (fun x hx => ?_) hv
  have hev : M.Y =ᶠ[𝓝 x] fun v => M.b * v := by
    have : Ioo (-M.ε) M.ε ∈ 𝓝 x := isOpen_Ioo.mem_nhds (abs_lt.mp hx)
    filter_upwards [this] with y hy
    exact hM.Y_lin y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  rw [hev.deriv_eq]; simp

theorem J_const {w : ℂ} (hw : ‖w‖ ≤ M.ε) : M.J w = M.a * M.b := by
  rw [J, X_deriv_lin hM ((abs_re_le_norm w).trans hw), Y_deriv_lin hM ((abs_im_le_norm w).trans hw)]

theorem J_pos (w : ℂ) : 0 < M.J w := mul_pos (hM.X_deriv_pos _) (hM.Y_deriv_pos _)

theorem J_smooth : ContDiff ℝ ∞ M.J :=
  ((contDiff_deriv_X hM).comp reCLM.contDiff).mul ((contDiff_deriv_Y hM).comp imCLM.contDiff)

theorem JF_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => M.JF p.1 p.2) :=
  (J_smooth hM).comp contDiff_snd

theorem Fmor_smooth : ContDiff ℝ ∞ M.Fmor := by
  unfold Fmor
  exact (ofRealCLM.contDiff.comp (hM.X_smooth.comp reCLM.contDiff)).add
    ((ofRealCLM.contDiff.comp (hM.Y_smooth.comp imCLM.contDiff)).mul contDiff_const)

lemma hasFDerivAt_Fmor (w : ℂ) :
    HasFDerivAt M.Fmor
      (ofRealCLM.comp ((deriv M.X w.re) • reCLM) +
        (ofRealCLM.comp ((deriv M.Y w.im) • imCLM)).smulRight I) w := by
  have hX : HasDerivAt M.X (deriv M.X w.re) w.re :=
    (hM.X_smooth.differentiable (by simp) _).hasDerivAt
  have hY : HasDerivAt M.Y (deriv M.Y w.im) w.im :=
    (hM.Y_smooth.differentiable (by simp) _).hasDerivAt
  have h1 : HasFDerivAt (fun w : ℂ => (M.X w.re : ℂ))
      (ofRealCLM.comp ((deriv M.X w.re) • reCLM)) w := by
    have := (hX.hasFDerivAt.comp w reCLM.hasFDerivAt)
    refine (ofRealCLM.hasFDerivAt.comp w this).congr_fderiv ?_
    ext1 z; simp; ring
  have h2 : HasFDerivAt (fun w : ℂ => (M.Y w.im : ℂ))
      (ofRealCLM.comp ((deriv M.Y w.im) • imCLM)) w := by
    have := (hY.hasFDerivAt.comp w imCLM.hasFDerivAt)
    refine (ofRealCLM.hasFDerivAt.comp w this).congr_fderiv ?_
    ext1 z; simp; ring
  have h3 := h2.mul_const I
  refine (h1.add h3).congr_fderiv ?_
  ext1 z; simp; ring

theorem Fmor_det (w : ℂ) : LinearMap.det (fderiv ℝ M.Fmor w : ℂ →ₗ[ℝ] ℂ) = M.J w := by
  rw [(hasFDerivAt_Fmor hM w).fderiv, Inner.det_eq_re_im]
  simp [J]

theorem Fmor_level (w : ℂ) : M.Rf (M.Fmor w).re + M.Wf (M.Fmor w).im = ‖w‖ ^ 2 := by
  rw [Fmor_re, Fmor_im, Rf_X hM, Wf_Y hM, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem Fmor_bijective : Function.Bijective M.Fmor := by
  constructor
  · intro w₁ w₂ h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Fmor_re, Fmor_im] at h1 h2
    exact Complex.ext ((X_strictMono hM).injective h1) ((Y_strictMono hM).injective h2)
  · intro z
    refine ⟨(invR M.X z.re : ℂ) + (invR M.Y z.im : ℂ) * I, Complex.ext ?_ ?_⟩
    · simp [X_apply_inv hM]
    · simp [Y_apply_inv hM]

/-! ### Polar coordinates and the slice formula -/

lemma K_continuous : Continuous M.K := by
  have h1 := (contDiff_deriv_X hM).continuous
  have h2 := (contDiff_deriv_Y hM).continuous
  unfold K; fun_prop

lemma J_continuous : Continuous M.J := (J_smooth hM).continuous

lemma Jbar_JF_sq (s : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Inner.Jbar M.JF s (ρ ^ 2) =
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, M.K (ρ * Real.cos φ, ρ * Real.sin φ) := by
  unfold Inner.Jbar JF
  rw [Real.sqrt_sq hρ]
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [J, K, Inner.Rot_ofReal_re, Inner.Rot_ofReal_im]

lemma Jbar_JF_continuous (s : ℝ) : Continuous (Inner.Jbar M.JF s) := by
  unfold Inner.Jbar JF
  refine continuous_const.mul ?_
  have hR := Inner.contDiff_Rot.continuous
  have hJ := J_continuous hM
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hJ.comp (hR.comp (continuous_snd.prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst))))

lemma angular_shift (ρ : ℝ) :
    ∫ θ in (-π)..π, M.K (ρ * Real.cos θ, ρ * Real.sin θ) =
      ∫ θ in (0 : ℝ)..2 * π, M.K (ρ * Real.cos θ, ρ * Real.sin θ) := by
  have hper : Function.Periodic (fun θ => M.K (ρ * Real.cos θ, ρ * Real.sin θ)) (2 * π) := by
    intro θ; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  exact this

theorem disk_integral_polar {E : ℝ} (hE : 0 ≤ E) :
    ∫ p, (Inner.diskR E).indicator M.K p =
      ∫ ρ in (0 : ℝ)..√E, ρ * ∫ θ in (-π)..π, M.K (ρ * Real.cos θ, ρ * Real.sin θ) := by
  rw [← integral_comp_polarCoord_symm]
  set g : ℝ × ℝ → ℝ := fun p => p.1 * M.K (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  have hg : Continuous g := by
    have := K_continuous hM
    simp only [g]; fun_prop
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • (Inner.diskR E).indicator M.K (polarCoord.symm p) =
        (Iic √E ×ˢ univ).indicator g p := by
    rintro ⟨ρ, θ⟩ ⟨hρ, -⟩
    simp only [mem_Ioi] at hρ
    have hmem : polarCoord.symm (ρ, θ) ∈ Inner.diskR E ↔
        (ρ, θ) ∈ Iic √E ×ˢ (univ : Set ℝ) := by
      simp only [Inner.diskR, polarCoord_symm_apply, mem_ofPred_eq, mem_prod, mem_Iic, mem_univ,
        and_true]
      rw [show (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 by
        nlinarith [Real.cos_sq_add_sin_sq θ]]
      rw [Real.le_sqrt hρ.le hE]
    by_cases h : polarCoord.symm (ρ, θ) ∈ Inner.diskR E
    · rw [indicator_of_mem h, indicator_of_mem (hmem.mp h)]
      simp [g, polarCoord_symm_apply, K, smul_eq_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mpr h')), smul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr,
    setIntegral_indicator (measurableSet_Iic.prod MeasurableSet.univ)]
  have hset : polarCoord.target ∩ Iic √E ×ˢ (univ : Set ℝ) = Ioc 0 √E ×ˢ Ioo (-π) π := by
    rw [polarCoord_target, prod_inter_prod, Ioi_inter_Iic, inter_univ]
  rw [hset, Measure.volume_eq_prod, setIntegral_prod]
  · rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg E)]
    refine setIntegral_congr_fun measurableSet_Ioc fun ρ _ => ?_
    simp only [g]
    rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  · have hc : IntegrableOn g (Icc 0 √E ×ˢ Icc (-π) π) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hc.mono_set (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)

theorem Acal_eq_disk (s : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    Acal M.JF s E = ∫ p, (Inner.diskR E).indicator M.K p := by
  rw [disk_integral_polar hM hE]
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := √E)
    (f := fun ρ : ℝ => ρ ^ 2) (f' := fun ρ => 2 * ρ) (g := Inner.Jbar M.JF s)
    (fun ρ _ => by simpa using hasDerivAt_pow 2 ρ) (by fun_prop) (Jbar_JF_continuous hM s)
  simp only [Function.comp_def, Real.sq_sqrt hE, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hsub
  rw [Acal, ← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ρ hρ => ?_
  rw [uIcc_of_le (Real.sqrt_nonneg E)] at hρ
  rw [Jbar_JF_sq hM s hρ.1, angular_shift hM]
  field_simp

lemma integrable_disk (E : ℝ) :
    Integrable ((Inner.diskR E).indicator M.K) (volume.prod volume) := by
  rw [← Measure.volume_eq_prod, integrable_indicator_iff (Inner.measurableSet_diskR E)]
  have hc : IntegrableOn M.K (Icc (-√E) √E ×ˢ Icc (-√E) √E) :=
    (K_continuous hM).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine hc.mono_set fun p hp => ?_
  simp only [Inner.diskR, mem_ofPred_eq] at hp
  have hE : 0 ≤ E := le_trans (by positivity) hp
  exact ⟨(Real.sq_le hE).mp (by nlinarith [sq_nonneg p.2]),
    (Real.sq_le hE).mp (by nlinarith [sq_nonneg p.1])⟩

lemma slice_integral {E : ℝ} (hE : 0 ≤ E) (v : ℝ) :
    ∫ u, (Inner.diskR E).indicator M.K (u, v) =
      (Icc (-√E) √E).indicator (fun v => deriv M.Y v * M.Lx (E - v ^ 2)) v := by
  by_cases hv : v ^ 2 ≤ E
  · have hvmem : v ∈ Icc (-√E) √E := (Real.sq_le hE).mp hv
    rw [indicator_of_mem hvmem]
    set r := √(E - v ^ 2)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hset : ∀ u, (u, v) ∈ Inner.diskR E ↔ u ∈ Icc (-r) r := by
      intro u
      simp only [Inner.diskR, mem_ofPred_eq]
      rw [mem_Icc, ← Real.sq_le (by linarith)]
      constructor <;> intro h <;> linarith
    have hfun : (fun u => (Inner.diskR E).indicator M.K (u, v)) =
        (Icc (-r) r).indicator (fun u => deriv M.Y v * deriv M.X u) := by
      funext u
      by_cases hu : u ∈ Icc (-r) r
      · rw [indicator_of_mem ((hset u).mpr hu), indicator_of_mem hu, K, mul_comm]
      · rw [indicator_of_notMem (fun h => hu ((hset u).mp h)), indicator_of_notMem hu]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
    congr 1
    have hd := hM.X_smooth.differentiable (by simp)
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x)
      ((contDiff_deriv_X hM).continuous.intervalIntegrable _ _)]
    rfl
  · have hvmem : v ∉ Icc (-√E) √E := fun h => hv ((Real.sq_le hE).mpr h)
    rw [indicator_of_notMem hvmem]
    have : ∀ u, (u, v) ∉ Inner.diskR E := by
      intro u hu; simp only [Inner.diskR, mem_ofPred_eq] at hu; apply hv; nlinarith [sq_nonneg u]
    simp [indicator_of_notMem (this _)]

/-- **Slice formula.** `𝓐(E) = ∫_{-√E}^{√E} Y'(v) (X(√(E-v²)) - X(-√(E-v²))) dv`. -/
theorem Acal_eq_slices (s : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    Acal M.JF s E = ∫ v in (-√E)..√E, deriv M.Y v * M.Lx (E - v ^ 2) := by
  rw [Acal_eq_disk hM s hE, Measure.volume_eq_prod, integral_prod_symm _ (integrable_disk hM E)]
  simp_rw [slice_integral hM hE]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.sqrt_nonneg E])]

lemma Lx_continuous : Continuous M.Lx := by
  have := hM.X_smooth.continuous
  unfold Lx; fun_prop

lemma Lx_nonneg (s : ℝ) : 0 ≤ M.Lx s := by
  unfold Lx
  have := (X_strictMono hM).monotone (show -√s ≤ √s by linarith [Real.sqrt_nonneg s])
  linarith

lemma Lx_mono {s t : ℝ} (h : s ≤ t) : M.Lx s ≤ M.Lx t := by
  unfold Lx
  have h1 := Real.sqrt_le_sqrt h
  have := (X_strictMono hM).monotone h1
  have := (X_strictMono hM).monotone (neg_le_neg h1)
  linarith

lemma Lx_ge (s : ℝ) : M.X √s ≤ M.Lx s := by
  unfold Lx
  have := (X_strictMono hM).monotone (show -√s ≤ 0 by linarith [Real.sqrt_nonneg s])
  rw [X_zero hM] at this
  linarith

lemma Lx_eq_zero {s : ℝ} (hs : s ≤ 0) : M.Lx s = 0 := by
  simp [Lx, Real.sqrt_eq_zero'.mpr hs]

/-- `𝓐(E) ≥ 2εb (X(√(E - ε²)))` for `E ≥ ε²`. -/
theorem Acal_ge (s : ℝ) {E : ℝ} (hE : M.ε ^ 2 ≤ E) :
    2 * M.ε * M.b * M.X √(E - M.ε ^ 2) ≤ Acal M.JF s E := by
  have hε := hM.ε_pos
  have hE0 : 0 ≤ E := le_trans (sq_nonneg _) hE
  rw [Acal_eq_slices hM s hE0]
  set f : ℝ → ℝ := fun v => deriv M.Y v * M.Lx (E - v ^ 2)
  have hfc : Continuous f :=
    (contDiff_deriv_Y hM).continuous.mul ((Lx_continuous hM).comp (by fun_prop))
  have hf0 : ∀ v, 0 ≤ f v := fun v => mul_nonneg (hM.Y_deriv_pos v).le (Lx_nonneg hM _)
  have hεE : M.ε ≤ √E := by
    rw [← Real.sqrt_sq hε.le]; exact Real.sqrt_le_sqrt hE
  have h1 : ∫ v in (-M.ε)..M.ε, f v ≤ ∫ v in (-√E)..√E, f v :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hεE
      (Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
  have h2 : ∫ v in (-M.ε)..M.ε, (M.b * M.Lx (E - M.ε ^ 2)) ≤ ∫ v in (-M.ε)..M.ε, f v := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hfc.intervalIntegrable _ _) fun v hv => ?_
    have hv' : |v| ≤ M.ε := abs_le.mpr hv
    simp only [f]
    rw [Y_deriv_lin hM hv']
    refine mul_le_mul_of_nonneg_left (Lx_mono hM ?_) hM.b_pos.le
    have : v ^ 2 ≤ M.ε ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv' 2
    linarith
  have h3 : ∫ v in (-M.ε)..M.ε, (M.b * M.Lx (E - M.ε ^ 2)) = 2 * M.ε * (M.b * M.Lx (E - M.ε ^ 2)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h4 := Lx_ge hM (E - M.ε ^ 2)
  have h5 : 0 ≤ 2 * M.ε * M.b := by have := hM.b_pos; positivity
  have : 2 * M.ε * M.b * M.X √(E - M.ε ^ 2) ≤ 2 * M.ε * (M.b * M.Lx (E - M.ε ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h4 h5; linarith
  linarith

theorem Acal_tendsto (s : ℝ) : Tendsto (Acal M.JF s) atTop atTop := by
  have hε := hM.ε_pos
  have hc : 0 < 2 * M.ε * M.b := by have := hM.b_pos; positivity
  have hX : Tendsto (fun E => M.X √(E - M.ε ^ 2)) atTop atTop :=
    hM.X_top.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id))
  have hlin := hX.const_mul_atTop hc
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [eventually_ge_atTop (M.ε ^ 2)] with E hE
  exact Acal_ge hM s hE

/-- The density is flat. -/
theorem flat : FlatDensity M.JF (-1) 1 (M.a * M.b) M.ε where
  smooth := JF_smooth hM
  pos := fun _ _ w => J_pos hM w
  flat := fun _ _ _ hw => J_const hM hw
  j_pos := mul_pos hM.a_pos hM.b_pos
  ρ₀_pos := hM.ε_pos
  tendsto := fun s _ => Acal_tendsto hM s

/-! ### The inner map -/

theorem finner_smooth : ContDiff ℝ ∞ M.finner :=
  (Inner.normalize_smooth_of_const (flat hM) zero_mem (Fmor_smooth hM) (Fmor_det hM)).1

theorem finner_symplectic (z : ℂ) :
    LinearMap.det (fderiv ℝ M.finner z : ℂ →ₗ[ℝ] ℂ) = 1 :=
  (Inner.normalize_smooth_of_const (flat hM) zero_mem (Fmor_smooth hM) (Fmor_det hM)).2.1 z

theorem finner_bijective : Function.Bijective M.finner := by
  have hJ := flat hM
  have hT : Function.Bijective (TrotInv M.JF 0) :=
    ⟨fun a b h => by
      rw [← Inner.Trot_TrotInv hJ zero_mem a, h, Inner.Trot_TrotInv hJ zero_mem b],
     fun y => ⟨Trot M.JF 0 y, Inner.TrotInv_Trot hJ zero_mem y⟩⟩
  exact (Fmor_bijective hM).comp (hT.comp (Inner.Darea_bijective hJ zero_mem))

/-- `R(Re f) + W(Im f) = E(π|z|²)`. -/
theorem finner_level (z : ℂ) :
    M.Rf (M.finner z).re + M.Wf (M.finner z).im = Einv M.JF 0 (π * ‖z‖ ^ 2) := by
  rw [finner, Fmor_level hM, Inner.normalize_circle (flat hM) zero_mem]

/-- `f(z) = (a/√(ab)) Re z + i (b/√(ab)) Im z` for `|z| ≤ √(ab) ε`. -/
theorem finner_linear {z : ℂ} (hz : ‖z‖ ≤ √(M.a * M.b) * M.ε) :
    M.finner z = ((M.a / √(M.a * M.b) * z.re : ℝ) : ℂ) +
      ((M.b / √(M.a * M.b) * z.im : ℝ) : ℂ) * I := by
  have hsj : 0 < √(M.a * M.b) := Real.sqrt_pos.2 (mul_pos hM.a_pos hM.b_pos)
  rw [finner, Inner.normalize_eq_of_const (flat hM) zero_mem M.Fmor hz]
  set w := z / (√(M.a * M.b) : ℂ)
  have hw : ‖w‖ ≤ M.ε := by
    simp only [w, norm_div, Complex.norm_real, Real.norm_of_nonneg hsj.le]
    rw [div_le_iff₀ hsj]; linarith
  have hre : w.re = z.re / √(M.a * M.b) := by simp [w, Complex.div_ofReal_re]
  have him : w.im = z.im / √(M.a * M.b) := by simp [w, Complex.div_ofReal_im]
  apply Complex.ext
  · rw [Fmor_re, hM.X_lin _ ((abs_re_le_norm w).trans hw), hre]
    simp; ring
  · rw [Fmor_im, hM.Y_lin _ ((abs_im_le_norm w).trans hw), him]
    simp; ring

theorem finner_zero : M.finner 0 = 0 := by
  have h := finner_linear hM (z := 0) (by
    simp only [norm_zero]; exact mul_nonneg (Real.sqrt_nonneg _) hM.ε_pos.le)
  simpa using h

/-! ### The area identity -/

lemma volume_slice (E y : ℝ) :
    volume {x : ℝ | M.Rf x + M.Wf y ≤ E} = ENNReal.ofReal (M.Lx (E - M.Wf y)) := by
  rcases le_or_gt 0 (E - M.Wf y) with h | h
  · have hset : {x : ℝ | M.Rf x + M.Wf y ≤ E} =
        Icc (M.X (-√(E - M.Wf y))) (M.X √(E - M.Wf y)) := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc]
      rw [← Rf_le_iff hM h]
      constructor <;> intro h' <;> linarith
    rw [hset, Real.volume_Icc, Lx]
  · have hset : {x : ℝ | M.Rf x + M.Wf y ≤ E} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [Rf_nonneg hM x]
    rw [hset, measure_empty, Lx_eq_zero hM h.le, ENNReal.ofReal_zero]

lemma Wf_ge_of_le {E y : ℝ} (hE : 0 ≤ E) (hy : y ≤ M.Y (-√E)) : E ≤ M.Wf y := by
  by_contra h
  push Not at h
  have := ((Wf_le_iff hM hE y).mp h.le).1
  have hy' : y = M.Y (-√E) := le_antisymm hy this
  rw [hy', Wf_Y hM, neg_sq, Real.sq_sqrt hE] at h
  exact lt_irrefl _ h

lemma Wf_ge_of_ge {E y : ℝ} (hE : 0 ≤ E) (hy : M.Y √E ≤ y) : E ≤ M.Wf y := by
  by_contra h
  push Not at h
  have := ((Wf_le_iff hM hE y).mp h.le).2
  have hy' : y = M.Y √E := le_antisymm this hy
  rw [hy', Wf_Y hM, Real.sq_sqrt hE] at h
  exact lt_irrefl _ h

/-- **Area identity.** `𝓐(E) = area{(x, y) : R(x) + W(y) ≤ E}`. -/
theorem Acal_eq_area (s : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    volume {p : ℝ × ℝ | M.Rf p.1 + M.Wf p.2 ≤ E} = ENNReal.ofReal (Acal M.JF s E) := by
  have hR := Rf_continuous hM
  have hV := Wf_continuous hM
  have hmeas : MeasurableSet {p : ℝ × ℝ | M.Rf p.1 + M.Wf p.2 ≤ E} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  simp only [preimage_ofPred_eq]
  simp_rw [volume_slice hM E]
  set a := M.Y (-√E)
  set b := M.Y √E
  have hab : a ≤ b := (Y_strictMono hM).monotone (by linarith [Real.sqrt_nonneg E])
  set f : ℝ → ℝ := fun y => M.Lx (E - M.Wf y)
  have hfc : Continuous f := (Lx_continuous hM).comp (continuous_const.sub hV)
  have hfi : f = (Icc a b).indicator f := by
    funext y
    by_cases hy : y ∈ Icc a b
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      apply Lx_eq_zero hM
      rw [mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hy | hy
      · linarith [Wf_ge_of_le hM hE hy.le]
      · linarith [Wf_ge_of_ge hM hE hy.le]
  have hint : Integrable f := by
    rw [hfi, integrable_indicator_iff measurableSet_Icc]
    exact hfc.continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => Lx_nonneg hM _)]
  congr 1
  rw [hfi, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, Acal_eq_slices hM s hE]
  have hYd : ∀ v, HasDerivAt M.Y (deriv M.Y v) v := fun v =>
    (hM.Y_smooth.differentiable (by simp) v).hasDerivAt
  rw [← intervalIntegral.integral_comp_mul_deriv (fun v _ => hYd v)
    (contDiff_deriv_Y hM).continuous.continuousOn hfc]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [Function.comp_apply, f, Wf_Y hM]
  ring

/-- `E(I) < E'` whenever the sublevel set at `E' ≥ 0` has area `> I`. -/
theorem Einv_lt_of_area {I E' : ℝ} (hE' : 0 ≤ E')
    (harea : ENNReal.ofReal I < volume {p : ℝ × ℝ | M.Rf p.1 + M.Wf p.2 ≤ E'}) :
    Einv M.JF 0 I < E' := by
  have hJ := flat hM
  rw [Acal_eq_area hM 0 hE'] at harea
  have h1 : I < Acal M.JF 0 E' := by
    by_contra hc; push Not at hc
    exact absurd harea (not_lt.mpr (ENNReal.ofReal_le_ofReal hc))
  rw [← Inner.Acal_Einv hJ zero_mem I] at h1
  exact (Inner.Acal_strictMono hJ zero_mem).lt_iff_lt.mp h1

end hyp

end MorsePair

end SymplecticPacking.Branch2.Planar
