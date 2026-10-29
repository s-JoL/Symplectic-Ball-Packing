import SymplecticPacking.BranchSmall.ProjectiveCoordinates

/-!
# Linear growth after projective descent

The normal component of a smooth homogeneous representative vanishes at infinity.
Sup-norm normalization converts its uniform ball bound into affine linear growth.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {m : ℕ}

def normAffineLift (x : Affine m) : HomogeneousInput m :=
  ‖complexAffineLift (affineComplex m x)‖⁻¹ • complexAffineLift (affineComplex m x)

theorem normAffineLift_properties (x : Affine m) :
    ‖normAffineLift x‖ = 1 ∧ normAffineLift x none ≠ 0 ∧ returnQuotient m (normAffineLift x) = x ∧
      complexCartesian (normAffineLift x) ∈ phaseShell 1 (Fintype.card (Option (Option (Fin m))) : ℝ) := by
  let U : HomogeneousInput m := complexAffineLift (affineComplex m x)
  let r : ℝ := ‖U‖
  have hr1 : 1 ≤ r := by
    have hn := norm_le_pi_norm U none
    simpa only [U, complexAffineLift_none, norm_one] using hn
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let σ : ℝ := r⁻¹
  have hσ : 0 < σ := inv_pos.mpr hr
  let z : HomogeneousInput m := σ • U
  have hznorm : ‖z‖ = 1 := by
    rw [show z = σ • U from rfl, norm_smul, Real.norm_of_nonneg hσ.le]
    exact inv_mul_cancel₀ hr.ne'
  have hzn : z none = (σ : ℂ) := by
    simp only [z, U, Pi.smul_apply, complexAffineLift_none, Complex.real_smul, mul_one]
  have hz0 : z none ≠ 0 := by rw [hzn]; exact Complex.ofReal_ne_zero.mpr hσ.ne'
  have hzQ : returnQuotient m z = x := by
    have he : z = (σ : ℂ) • complexAffineLift (affineComplex m x) := by
      ext i
      simp only [z, U, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    unfold returnQuotient
    rw [he, complexAffineQuotient_smul _ (Complex.ofReal_ne_zero.mpr hσ.ne'),
      complexAffineQuotient_lift, ← affineComplexEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hznorm, hz0, hzQ, ?_⟩
  have hn := complex_phaseSq_norm_bounds z
  rw [hznorm, one_pow, mul_one] at hn
  exact hn

def projectedField (Y : ℝ → HomogeneousInput m → HomogeneousInput m) (s : ℝ) (x : Affine m) : Affine m :=
  fderiv ℝ (returnQuotient m) (normAffineLift x) (Y s (normAffineLift x))

theorem projectedField_linearGrowth {Y : ℝ → HomogeneousInput m → HomogeneousInput m}
    (hY : ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => Y p.1 p.2))
    (hYzero : ∀ s z, z none = 0 → Y s z none = 0) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : Affine m,
      ‖projectedField Y s x‖ ≤ C * (1 + ‖x‖) := by
  obtain ⟨L, hL, hLb⟩ := smooth_homogeneous_normal_bound hY hYzero
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : HomogeneousInput m) 1)).exists_bound_of_continuousOn hY.continuous.continuousOn
  let M₀ : ℝ := max M 0
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  let C : ℝ := M₀ + L
  have hC : 0 ≤ C := add_nonneg hM₀ hL
  refine ⟨C, ?_⟩
  intro s hs x
  let U : HomogeneousInput m := complexAffineLift (affineComplex m x)
  let r : ℝ := ‖U‖
  have hr1 : 1 ≤ r := by
    have hn := norm_le_pi_norm U none
    simpa only [U, complexAffineLift_none, norm_one] using hn
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let σ : ℝ := r⁻¹
  have hσ : 0 < σ := inv_pos.mpr hr
  let z : HomogeneousInput m := σ • U
  have hznorm : ‖z‖ = 1 := by
    rw [show z = σ • U from rfl, norm_smul, Real.norm_of_nonneg hσ.le]
    exact inv_mul_cancel₀ hr.ne'
  have hzn : z none = (σ : ℂ) := by
    simp only [z, U, Pi.smul_apply, complexAffineLift_none, Complex.real_smul, mul_one]
  have hz0 : z none ≠ 0 := by rw [hzn]; exact Complex.ofReal_ne_zero.mpr hσ.ne'
  have hYnorm : ‖Y s z‖ ≤ M₀ := by
    apply (hM (s, z) ⟨hs, ?_⟩).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hznorm.le
  have hYn : ‖Y s z none‖ ≤ L * σ := by
    have hn := hLb s hs z hznorm.le
    simpa only [hzn, Complex.norm_real, Real.norm_of_nonneg hσ.le] using hn
  have hrBound : r ≤ 1 + ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 + ‖x‖)).2
    intro i
    cases i with
    | none => change ‖(1 : ℂ)‖ ≤ 1 + ‖x‖; simp
    | some j =>
      change ‖affineComplex m x j‖ ≤ 1 + ‖x‖
      exact ((norm_le_pi_norm (affineComplex m x) j).trans_eq (affineComplex_norm x)).trans (by linarith [norm_nonneg x])
  have hscale : 1 ≤ (1 + ‖x‖) * σ := by
    change 1 ≤ (1 + ‖x‖) * r⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    simpa only [one_mul] using hrBound
  change ‖fderiv ℝ (returnQuotient m) z (Y s z)‖ ≤ C * (1 + ‖x‖)
  rw [returnQuotient_fderiv_norm z (Y s z) hz0]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (by positivity))).2
  intro j
  change ‖fderiv ℝ complexAffineQuotient (σ • complexAffineLift (affineComplex m x)) (Y s z) j‖ ≤ _
  rw [complexAffineQuotient_fderiv_scaled x hσ, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hσ.le]
  apply (div_le_iff₀ hσ).2
  have hnum : ‖Y s z (some j) - affineComplex m x j * Y s z none‖ ≤ M₀ + ‖x‖ * (L * σ) := by
    calc
      _ ≤ ‖Y s z (some j)‖ + ‖affineComplex m x j‖ * ‖Y s z none‖ := by
        simpa only [norm_mul] using norm_sub_le (Y s z (some j)) (affineComplex m x j * Y s z none)
      _ ≤ _ := add_le_add ((norm_le_pi_norm (Y s z) (some j)).trans hYnorm)
        (mul_le_mul ((norm_le_pi_norm (affineComplex m x) j).trans_eq (affineComplex_norm x))
          hYn (norm_nonneg _) (norm_nonneg _))
  apply hnum.trans
  have hMM : M₀ ≤ M₀ * ((1 + ‖x‖) * σ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hM₀
  have hLL : 0 ≤ L * σ := mul_nonneg hL hσ.le
  change M₀ + ‖x‖ * (L * σ) ≤ (M₀ + L) * (1 + ‖x‖) * σ
  nlinarith

end SymplecticPacking.BranchSmall.VT
