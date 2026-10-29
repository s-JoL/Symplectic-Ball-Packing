import SymplecticPacking.HighDim.Comparator.PlanarMorseInverse
import SymplecticPacking.Qhat.Normal

/-!
# Area available to the parameterised Morse normalisation

The rectangle is controlled using oscillation of the log-sum-exp potential.
Its additive log-cardinality shift cancels; an absolute bound on that potential
would be false for large tolerances.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set MeasureTheory Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)

theorem drect_bounds (hξ : 0 < D.xi) (hL : 0 ≤ D.L) :
    0 < D.drect ∧ D.drect ≤ 1 / 256 := by
  have hp := D.eta_pos hξ hL
  have hb := D.eta_le
  unfold drect
  constructor <;> linarith

/-- A bound on the affine data bounds oscillation, without a log-cardinality error. -/
theorem U0_oscillation (hξ : 0 < D.xi) (hne : D.pieces y ≠ [])
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |D.U0 y u - D.U0 y v| ≤ D.M := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hslope : ∀ p ∈ D.pieces y, |p.2| ≤ D.M := by
    intro p hp
    have hh := hbM p hp
    linarith [abs_nonneg p.1]
  have hd : ∀ t, |deriv (D.U0 y) t| ≤ D.M := by
    intro t
    rw [D.U0_eq_lse_potential y]
    exact LSE.potential_deriv_abs_le hne (D.clse_pos hξ).ne' hM hslope t
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (D.U0_smooth y hne).differentiable (by simp) t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hd t) hv hu
  have huv : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  simpa only [Real.norm_eq_abs] using h.trans (mul_le_of_le_one_right hM huv)

theorem V_rectangle_bound (hξ : 0 < D.xi) (hL : 0 ≤ D.L) {θ : ℝ}
    (hθ : θ ∈ Icc (-(1 / 2) + D.drect) (1 / 2 - D.drect)) :
    D.V θ ≤ D.nu / (2 * D.drect) := by
  obtain ⟨hd, hd'⟩ := D.drect_bounds hξ hL
  have hν := D.nu_pos hξ hL
  have hsq : θ ^ 2 ≤ (1 / 2 - D.drect) ^ 2 := by
    nlinarith [hθ.1, hθ.2, mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hθ.1)]
  have hden : D.drect / 2 ≤ 1 / 4 - θ ^ 2 := by
    nlinarith [mul_nonneg hd.le (by linarith : (0 : ℝ) ≤ 1 / 2 - D.drect)]
  have hden0 : 0 < 1 / 4 - θ ^ 2 := by linarith
  unfold V
  rw [div_le_div_iff₀ hden0 (by positivity)]
  have h1 : θ ^ 2 ≤ 1 / 4 := by linarith
  have hh := mul_le_mul_of_nonneg_left hden hν.le
  nlinarith [mul_nonneg hν.le (sub_nonneg.mpr h1), mul_nonneg hd.le hν.le]

/-- The prescribed rectangle lies in the modified-energy sublevel used in the definition
of `Erect`. This is proved for the uniform modification. -/
theorem rectangle_energy_bound (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
    {P θ : ℝ} (hP : P ∈ Icc D.drect (1 - D.drect))
    (hθ : θ ∈ Icc (-(1 / 2) + D.drect) (1 / 2 - D.drect)) :
    D.ftU y (P - D.vstar y) + D.wellV.ft θ ≤ D.Erect := by
  obtain ⟨hd, _⟩ := D.drect_bounds hξ hL
  have hk := D.kappa_pos hξ hL
  have hv := (D.vstar_spec y hξ hL hne hb).1
  have hP0 : 0 < P := lt_of_lt_of_le hd hP.1
  have hP1 : 0 < 1 - P := by linarith [hP.2]
  have h0 := D.U0_oscillation y hξ hne hbM
    (show P ∈ Icc (0 : ℝ) 1 from ⟨hP0.le, by linarith⟩) ⟨hv.1.le, hv.2.le⟩
  have h1 : 1 / P ≤ 1 / D.drect := one_div_le_one_div_of_le hd hP.1
  have h2 : 1 / (1 - P) ≤ 1 / D.drect := one_div_le_one_div_of_le hd (by linarith [hP.2])
  have hvs : 0 < D.vstar y := hv.1
  have hv1 : 0 < 1 - D.vstar y := by linarith [hv.2]
  have hbar : D.kappa * (1 / D.vstar y + 1 / (1 - D.vstar y)) ≥ 0 := by positivity
  have hU : D.U y P - D.U y (D.vstar y) ≤ D.M + 2 * D.kappa / D.drect := by
    unfold U
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hk.le
    have heq : D.kappa * (1 / D.drect + 1 / D.drect) = 2 * D.kappa / D.drect := by ring
    rw [heq] at hh
    linarith [(abs_le.mp h0).2]
  have hft := (abs_le.mp (D.ftU_close y hξ hL hne hb (P - D.vstar y))).2
  simp only [gU, add_sub_cancel] at hft
  have hV := D.V_rectangle_bound hξ hL hθ
  have hftV := (abs_le.mp (Branch2.Planar.Well.ft_close (D.wellV_hyp y hξ hL hne hb) θ)).2
  have hV0 : D.V 0 = 0 := by simp [V]
  change D.wellV.ft θ - (D.V (0 + θ) - D.V 0) ≤ D.tol at hftV
  rw [zero_add, hV0, sub_zero] at hftV
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  unfold Erect
  linarith

namespace AreaGate

def productMap (X Y : ℝ → ℝ) (w : ℂ) : ℂ := (X w.re : ℂ) + (Y w.im : ℂ) * I

theorem productMap_smooth {X Y : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (productMap X Y) :=
  (ofRealCLM.contDiff.comp (hX.comp reCLM.contDiff)).add
    ((ofRealCLM.contDiff.comp (hY.comp imCLM.contDiff)).mul contDiff_const)

theorem productMap_det {X Y : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (w : ℂ) :
    LinearMap.det (fderiv ℝ (productMap X Y) w : ℂ →ₗ[ℝ] ℂ) = deriv X w.re * deriv Y w.im := by
  have hx : HasDerivAt X (deriv X w.re) w.re := (hX.differentiable (by simp) _).hasDerivAt
  have hy : HasDerivAt Y (deriv Y w.im) w.im := (hY.differentiable (by simp) _).hasDerivAt
  have h1 : HasFDerivAt (fun w : ℂ => (X w.re : ℂ))
      (ofRealCLM.comp ((deriv X w.re) • reCLM)) w := by
    have hh := hx.hasFDerivAt.comp w reCLM.hasFDerivAt
    refine (ofRealCLM.hasFDerivAt.comp w hh).congr_fderiv ?_
    ext1 z; simp; ring
  have h2 : HasFDerivAt (fun w : ℂ => (Y w.im : ℂ))
      (ofRealCLM.comp ((deriv Y w.im) • imCLM)) w := by
    have hh := hy.hasFDerivAt.comp w imCLM.hasFDerivAt
    refine (ofRealCLM.hasFDerivAt.comp w hh).congr_fderiv ?_
    ext1 z; simp; ring
  have hf : HasFDerivAt (productMap X Y)
      (ofRealCLM.comp ((deriv X w.re) • reCLM) +
        (ofRealCLM.comp ((deriv Y w.im) • imCLM)).smulRight I) w := by
    refine (h1.add (h2.mul_const I)).congr_fderiv ?_
    ext1 z; simp; ring
  rw [hf.fderiv, Inner.det_eq_re_im]
  simp

theorem productMap_injective {X Y : ℝ → ℝ} (hX : StrictMono X) (hY : StrictMono Y) :
    Function.Injective (productMap X Y) := by
  intro w z h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [productMap, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_mul, zero_add] at hre him
  exact Complex.ext (hX.injective hre) (hY.injective him)

def rectangle (a b c d : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d)

theorem rectangle_area {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (volume (rectangle a b c d)).toReal = (b - a) * (d - c) := by
  rw [rectangle, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]
  simp [Real.volume_Icc, ENNReal.toReal_ofReal, sub_nonneg.mpr hab, sub_nonneg.mpr hcd]

/-- Image area bounds the polar area integral. No properness of the coordinate maps
at infinity is needed; their derivatives and the compact source disk suffice. -/
theorem rectangle_le_acal {X Y : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hdX : ∀ t, 0 < deriv X t) (hdY : ∀ t, 0 < deriv Y t)
    {a b c d E : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hE : 0 ≤ E)
    (hrect : rectangle a b c d ⊆ productMap X Y '' Metric.closedBall 0 √E) :
    (b - a) * (d - c) ≤
      Inner.Acal (fun _ w => deriv X w.re * deriv Y w.im) 0 E := by
  have hF := productMap_smooth hX hY
  have hinj := productMap_injective (strictMono_of_deriv_pos hdX) (strictMono_of_deriv_pos hdY)
  have hdet : ∀ w, 0 ≤ LinearMap.det (fderiv ℝ (productMap X Y) w : ℂ →ₗ[ℝ] ℂ) := by
    intro w
    rw [productMap_det hX hY]
    exact (mul_pos (hdX _) (hdY _)).le
  have harea := Qhat.integral_det_eq_volume (hF.differentiable (by simp)) hinj hdet
    (S := Metric.closedBall 0 √E) measurableSet_closedBall
  have hc : Continuous (fun w : ℂ => deriv X w.re * deriv Y w.im) :=
    (((contDiff_infty_iff_deriv.mp hX).2).continuous.comp continuous_re).mul
      (((contDiff_infty_iff_deriv.mp hY).2).continuous.comp continuous_im)
  simp_rw [productMap_det hX hY] at harea
  rw [Qhat.integral_closedBall_eq_Acal hc (Real.sqrt_nonneg E), Real.sq_sqrt hE] at harea
  rw [harea, ← rectangle_area hab hcd]
  apply ENNReal.toReal_mono
    (ne_of_lt ((isCompact_closedBall (0 : ℂ) √E).image hF.continuous).measure_lt_top)
  exact measure_mono hrect

end AreaGate

namespace AreaGate

theorem acal_const (a E : ℝ) : Inner.Acal (fun _ _ => a) 0 E = π * a * E := by
  simp only [Inner.Acal, Inner.Jbar, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp
  <;> ring

theorem acal_mono {J : ℂ → ℝ} (hc : Continuous J) (hp : ∀ w, 0 ≤ J w)
    {E F : ℝ} (hE : 0 ≤ E) (hEF : E ≤ F) :
    Inner.Acal (fun _ => J) 0 E ≤ Inner.Acal (fun _ => J) 0 F := by
  have hF : 0 ≤ F := hE.trans hEF
  have hEid := Qhat.integral_closedBall_eq_Acal hc (Real.sqrt_nonneg E)
  have hFid := Qhat.integral_closedBall_eq_Acal hc (Real.sqrt_nonneg F)
  rw [Real.sq_sqrt hE] at hEid
  rw [Real.sq_sqrt hF] at hFid
  rw [← hEid, ← hFid]
  exact setIntegral_mono_set
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) √F))
    (Filter.Eventually.of_forall fun w => hp w)
    (Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt hEF)).eventuallySubset

theorem acal_linear_lower {J K : ℂ → ℝ} (hJ : Continuous J) (hK : Continuous K)
    {a b E : ℝ} (hE : 0 ≤ E) (hpoint : ∀ w, a + b * K w ≤ J w) :
    π * a * E + b * Inner.Acal (fun _ => K) 0 E ≤ Inner.Acal (fun _ => J) 0 E := by
  let S := Metric.closedBall (0 : ℂ) √E
  have hc : IsCompact S := isCompact_closedBall _ _
  have hiK : IntegrableOn K S (volume : Measure ℂ) := hK.continuousOn.integrableOn_compact hc
  have hiJ : IntegrableOn J S (volume : Measure ℂ) := hJ.continuousOn.integrableOn_compact hc
  have hiA : IntegrableOn (fun _ : ℂ => a) S := continuousOn_const.integrableOn_compact hc
  have hm := setIntegral_mono_on (hiA.add (hiK.const_mul b)) hiJ
    measurableSet_closedBall (fun w _ => hpoint w)
  simp only [Pi.add_apply] at hm
  rw [integral_add hiA (hiK.const_mul b), integral_const_mul] at hm
  have hA : (∫ _ : ℂ in S, a) = π * a * E := by
    rw [Qhat.integral_closedBall_eq_Acal continuous_const (Real.sqrt_nonneg E),
      Real.sq_sqrt hE, acal_const]
  have hK' : (∫ w in S, K w) = Inner.Acal (fun _ => K) 0 E := by
    rw [Qhat.integral_closedBall_eq_Acal hK (Real.sqrt_nonneg E), Real.sq_sqrt hE]
  have hJ' : (∫ w in S, J w) = Inner.Acal (fun _ => J) 0 E := by
    rw [Qhat.integral_closedBall_eq_Acal hJ (Real.sqrt_nonneg E), Real.sq_sqrt hE]
  rwa [hA, hK', hJ'] at hm

theorem quadratic_gate {A B p s : ℝ} (hA : 0 < A) (hB : p < B) (hp : 0 < p)
    (hroom : p * B < A * (B - p)) : p < A * (1 - s) ^ 2 + B * s ^ 2 := by
  have hab : 0 < A + B := by linarith
  have he : (A + B) * (A * (1 - s) ^ 2 + B * s ^ 2 - p) =
      ((A + B) * s - A) ^ 2 + A * (B - p) - p * B := by ring
  have hh : 0 < (A + B) * (A * (1 - s) ^ 2 + B * s ^ 2 - p) := by
    rw [he]
    nlinarith [sq_nonneg ((A + B) * s - A)]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hab).mp hh)

end AreaGate

theorem Erect_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hM : 0 ≤ D.M) : 0 < D.Erect := by
  have hd := (D.drect_bounds hξ hL).1
  have hk := D.kappa_pos hξ hL
  have hn := D.nu_pos hξ hL
  have ht := D.tol_pos hξ
  unfold Erect
  positivity

/-- The inverse Morse coordinates put every point of the physical rectangle in the
image of the energy disk. Only the prescribed potentials are used here. -/
theorem rectangle_in_product_image (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M) :
    AreaGate.rectangle (D.drect - D.vstar y) (1 - D.drect - D.vstar y)
      (-(1 / 2) + D.drect) (1 / 2 - D.drect) ⊆
      AreaGate.productMap (D.XU y) D.XV '' Metric.closedBall 0 √D.Erect := by
  intro z hz
  change z.re ∈ Icc (D.drect - D.vstar y) (1 - D.drect - D.vstar y) ∧
    z.im ∈ Icc (-(1 / 2) + D.drect) (1 / 2 - D.drect) at hz
  have hd := (D.drect_bounds hξ hL).1
  have hx : z.re ∈ Ioo (-(D.vstar y)) (1 - D.vstar y) := by
    constructor <;> linarith [hz.1.1, hz.1.2]
  have hθ : z.im ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hW := D.modifiedWell_hyp y hξ hL hne hb
  have hV := D.wellV_hyp y hξ hL hne hb
  have hsu : D.SigU y z.re ^ 2 = D.ftU y z.re := by
    rw [← D.modifiedWell_Sig y hξ hL hne hb, ← D.modifiedWell_ft y hξ hL hne hb]
    exact Branch2.Planar.Well.Sig_sq hW (by
      simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, modifiedWell, sub_zero] using hx)
  have hsv : D.wellV.Sig z.im ^ 2 = D.wellV.ft z.im :=
    Branch2.Planar.Well.Sig_sq hV (by
      simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using hθ)
  let w : ℂ := (D.SigU y z.re : ℂ) + (D.wellV.Sig z.im : ℂ) * I
  have he := D.rectangle_energy_bound y hξ hL hne hb hbM
    (P := z.re + D.vstar y) (θ := z.im)
    (show z.re + D.vstar y ∈ Icc D.drect (1 - D.drect) from
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩) hz.2
  simp only [add_sub_cancel_right] at he
  have hnorm : ‖w‖ ^ 2 ≤ D.Erect := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    dsimp [w]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    nlinarith [hsu, hsv]
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hE := D.Erect_pos hξ hL hM
  refine ⟨w, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [Real.sq_sqrt hE.le, Real.sqrt_nonneg D.Erect, norm_nonneg w]
  · apply Complex.ext
    · simpa [AreaGate.productMap, w] using D.XU_SigU y hξ hL hne hb hx
    · simpa [AreaGate.productMap, w, XV] using Branch2.Planar.Well.X_Sig hV (by
        simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using hθ)

/-- The area of the terminal Morse density at `Erect` contains the full rectangle.
This remains valid though the inverse coordinate maps have bounded ranges. -/
theorem terminal_rectangle_area (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M) :
    D.Amin ≤ Inner.Acal (D.Js y) 1 D.Erect := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hd := (D.drect_bounds hξ hL).2
  have h := AreaGate.rectangle_le_acal (D.XU_smooth y hξ hL hne hb)
    (D.XV_smooth y hξ hL hne hb) (D.XU_deriv_pos y hξ hL hne hb)
    (Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb))
    (a := D.drect - D.vstar y) (b := 1 - D.drect - D.vstar y)
    (c := -(1 / 2) + D.drect) (d := 1 / 2 - D.drect)
    (by linarith) (by linarith) (D.Erect_pos hξ hL hM).le
    (D.rectangle_in_product_image y hξ hL hne hb hbM)
  have he : (1 - D.drect - D.vstar y - (D.drect - D.vstar y)) *
      (1 / 2 - D.drect - (-(1 / 2) + D.drect)) = D.Amin := by unfold Amin; ring
  rw [he] at h
  simpa only [Inner.Acal, Inner.Jbar, Js, sub_self, zero_mul, one_mul, zero_add] using h

theorem Amin_gt_pdag (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : D.pdag < D.Amin := by
  have he := D.eta_pos hξ hL
  unfold Amin pdag drect
  nlinarith [sq_nonneg D.eta]

theorem Js_slice_continuous (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) (s : ℝ) :
    Continuous (D.Js y s) := by
  have hx := ((contDiff_infty_iff_deriv.mp (D.XU_smooth y hξ hL hne hb)).2).continuous
  have hy := ((contDiff_infty_iff_deriv.mp (D.XV_smooth y hξ hL hne hb)).2).continuous
  unfold Js
  exact ((continuous_const.add (continuous_const.mul (hx.comp continuous_re)))).mul
    (continuous_const.add (continuous_const.mul (hy.comp continuous_im)))

theorem Js_quadratic_lower (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (w : ℂ) :
    (1 - s) ^ 2 * D.j0 y + s ^ 2 * D.Js y 1 w ≤ D.Js y s w := by
  have ha : 0 ≤ D.a0 y := by unfold a0; positivity
  have hb0 := (D.b0_pos_of_pieces y hξ hL hne hb).le
  have hx := (D.XU_deriv_pos y hξ hL hne hb w.re).le
  have hy := (Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb) w.im).le
  have hcross : 0 ≤ (1 - s) * s * (D.a0 y * deriv D.XV w.im + D.b0 * deriv (D.XU y) w.re) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hs.1)
      (add_nonneg (mul_nonneg ha hy) (mul_nonneg hb0 hx))
  have he : D.Js y s w - ((1 - s) ^ 2 * D.j0 y + s ^ 2 * D.Js y 1 w) =
      (1 - s) * s * (D.a0 y * deriv D.XV w.im + D.b0 * deriv (D.XU y) w.re) := by
    simp only [Js, j0, sub_self, zero_mul, one_mul, zero_add]
    ring
  exact sub_nonneg.mp (he ▸ hcross)

/-- The single energy bound from the construction works at every interpolation time.
This proves the finite-area endpoint case, as well as every intermediate density. -/
theorem Ebar_area_gate (hξ : 0 < D.xi) (hL : 0 ≤ D.L)
    (hne : D.pieces y ≠ []) (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    D.pdag < Inner.Acal (D.Js y) s D.Ebar := by
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  have hαmax := D.alphaMax_pos_of_pieces y hξ hL hne hb
  have ham : 0 < D.amin := Real.sqrt_pos.mpr (div_pos two_pos hαmax)
  have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
  have ha_le : D.amin ≤ D.a0 y :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left two_pos.le ha (D.alphaU_bounds y hξ hL hne hb).2)
  have hK : 0 < D.Kmin := by unfold Kmin; positivity
  have hKle : D.Kmin ≤ π * D.j0 y := by
    unfold Kmin j0
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ha_le Real.pi_pos.le) hb0.le
  have hp := D.pdag_pos hξ hL
  have hA := D.Amin_gt_pdag hξ hL
  have hden : 0 < D.Kmin * (D.Amin - D.pdag) := mul_pos hK (sub_pos.mpr hA)
  obtain ⟨p, hpmem⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hpmem)
  have hrect := D.Erect_pos hξ hL hM
  have hfrac : 0 < D.pdag * D.Amin / (D.Kmin * (D.Amin - D.pdag)) :=
    div_pos (mul_pos hp (hp.trans hA)) hden
  have hEE : D.Erect ≤ D.Ebar := by unfold Ebar; linarith
  have hE : 0 < D.Ebar := hrect.trans_le hEE
  have hroom : D.pdag * D.Amin < (D.Kmin * D.Ebar) * (D.Amin - D.pdag) := by
    have hh : D.pdag * D.Amin / (D.Kmin * (D.Amin - D.pdag)) < D.Ebar := by
      unfold Ebar
      linarith
    have hh' := (div_lt_iff₀ hden).mp hh
    nlinarith only [hh']
  have hterminal := D.terminal_rectangle_area y hξ hL hne hb hbM
  have hpositive : ∀ w, 0 ≤ D.Js y 1 w := by
    intro w
    simp only [Js, sub_self, zero_mul, one_mul, zero_add]
    exact (mul_pos (D.XU_deriv_pos y hξ hL hne hb _) 
      (Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb) _)).le
  have hmono := AreaGate.acal_mono (D.Js_slice_continuous y hξ hL hne hb 1) hpositive hrect.le hEE
  have hterminal' : D.Amin ≤ Inner.Acal (D.Js y) 1 D.Ebar := by
    simpa only [Inner.Acal, Inner.Jbar] using hterminal.trans hmono
  have hlower := AreaGate.acal_linear_lower
    (D.Js_slice_continuous y hξ hL hne hb s) (D.Js_slice_continuous y hξ hL hne hb 1)
    hE.le (D.Js_quadratic_lower y hξ hL hne hb hs)
  have hconst := mul_le_mul_of_nonneg_right hKle (mul_nonneg hE.le (sq_nonneg (1 - s)))
  have hterm := mul_le_mul_of_nonneg_right hterminal' (sq_nonneg s)
  have hquad := AreaGate.quadratic_gate (mul_pos hK hE) hA hp hroom (s := s)
  apply hquad.trans_le
  have hlower' : π * D.j0 y * (D.Ebar * (1 - s) ^ 2) +
      Inner.Acal (D.Js y) 1 D.Ebar * s ^ 2 ≤ Inner.Acal (D.Js y) s D.Ebar := by
    simpa only [Inner.Acal, Inner.Jbar, mul_assoc, mul_left_comm, mul_comm] using hlower
  have hh := (add_le_add hconst hterm).trans hlower'
  simpa only [mul_assoc] using hh

end SymplecticPacking.HighDim.PlanarGen.Input

namespace SymplecticPacking.HighDim.PlanarGen

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)

/-- The slice input supplies the value envelope used by the area gate. -/
theorem sliceInput_value_bound {m q : ℕ} (Δ : Polytope m q) (F : PolyFn m) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) {R : ℝ} (hR : 0 ≤ R) (η₀ ξ : ℝ)
    (y : Moments m) (hy : ∀ i, |y i| ≤ 4 * R) (hell0 : 0 ≤ ell y)
    (hell : ell y ≤ lenBound Δ j R) :
    ∀ p ∈ (sliceInput Δ F j ell Lν R η₀ ξ).pieces y,
      |p.1| + |p.2| ≤ (sliceInput Δ F j ell Lν R η₀ ξ).M := by
  have hlen : 0 ≤ lenBound Δ j R := hell0.trans hell
  have hentry (a : AffinePiece m) :
      0 ≤ |a.const| + 4 * R * (∑ i, |a.coef i|) + |a.coef j| * lenBound Δ j R := by
    positivity
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  have hyp : ∀ i, |Function.update y j 0 i| ≤ 4 * R := by
    intro i
    by_cases hi : i = j
    · subst i; simp only [Function.update_self, abs_zero]; positivity
    · simpa only [Function.update_of_ne hi] using hy i
  have hsum : |∑ i, a.coef i * Function.update y j 0 i| ≤ 4 * R * ∑ i, |a.coef i| := by
    calc |∑ i, a.coef i * Function.update y j 0 i|
        ≤ ∑ i, |a.coef i * Function.update y j 0 i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a.coef i| * (4 * R) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hyp i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hinter : |a.eval (Function.update y j 0)| ≤ |a.const| + 4 * R * ∑ i, |a.coef i| := by
    unfold AffinePiece.eval
    exact (abs_add_le _ _).trans (by linarith)
  have hslope : |a.coef j * ell y| ≤ |a.coef j| * lenBound Δ j R := by
    rw [abs_mul, abs_of_nonneg hell0]
    exact mul_le_mul_of_nonneg_left hell (abs_nonneg _)
  have hs := List.single_le_sum (l := F.map fun b =>
      |b.const| + 4 * R * (∑ i, |b.coef i|) + |b.coef j| * lenBound Δ j R)
    (fun x hx => by obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx; exact hentry b)
    _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  change |a.eval (Function.update y j 0)| + |a.coef j * ell y| ≤
    (F.map fun b => |b.const| + 4 * R * (∑ i, |b.coef i|) + |b.coef j| * lenBound Δ j R).sum + 1
  linarith

end SymplecticPacking.HighDim.PlanarGen
