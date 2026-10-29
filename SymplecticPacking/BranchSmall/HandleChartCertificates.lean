import OAI.Geometry.BallPacking.Annuli.AnnularChartNormalization

/-!
# Numerical certificates for the quadric handle charts

Fixed numerical certificates for the native quadric handle charts.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall
open Set
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

/-- An elementary bound for the displayed quadratic branch expression. -/
theorem baseSquare_real_bounds {z : ℂ} (hz : z ≠ 0)
    (hn : ‖z‖ ≤ 4 / 3) (hi : ‖z⁻¹‖ ≤ 4 / 3) :
    0 < (baseSquare z).re ∧ (baseSquare z).re < 3 := by
  have he : (4 : ℂ) * baseSquare z - 6 = z ^ 2 + (z⁻¹) ^ 2 := by
    unfold baseSquare plus
    field_simp
    ring
  have hre := congrArg Complex.re he
  norm_num only [Complex.sub_re, Complex.add_re, Complex.mul_re, zero_mul, sub_zero] at hre
  rw [show (4:ℂ).re = 4 by norm_num, show (4:ℂ).im = 0 by norm_num,
    show (6:ℂ).re = 6 by norm_num] at hre
  simp only [zero_mul, sub_zero] at hre
  have h1 := (abs_le.mp (Complex.abs_re_le_norm (z ^ 2)))
  have h2 := (abs_le.mp (Complex.abs_re_le_norm ((z⁻¹) ^ 2)))
  rw [norm_pow] at h1 h2
  have hsq : ‖z‖ ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by nlinarith [norm_nonneg z]
  have hisq : ‖z⁻¹‖ ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by nlinarith [norm_nonneg (z⁻¹)]
  constructor <;> nlinarith

/-- The whole closed annulus of half-width `1/4` lies in the fixed-root sheet. -/
theorem annulus_quarter_native (m : ℕ) {z : ℂ}
    (hz : z ∈ complexClosedAnnulus (1 / 4)) : z ∈ annulusDomain m := by
  have hnorm : (3 / 4 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 5 / 4 := by
    norm_num only [complexClosedAnnulus, Set.mem_setOf_eq] at hz
    exact hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith [hnorm.1])
  have hn : ‖z‖ ≤ 4 / 3 := by linarith [hnorm.2]
  have hi : ‖z⁻¹‖ ≤ 4 / 3 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (by linarith [hnorm.1])]
    linarith [hnorm.1]
  have hb := baseSquare_real_bounds hz0 hn hi
  refine ⟨hz0, hb.1, ?_⟩
  intro j hj
  have hj' : (3 : ℝ) ≤ (parameters m j).re := by
    simp only [parameters, Complex.add_re, Complex.natCast_re, Complex.one_re]
    norm_cast
    omega
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith [hb.2]

theorem exp_half_lt_seven_quarters : Real.exp (1 / 2) < 7 / 4 := by
  have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [Real.exp_pos (1 / 2), Real.exp_one_lt_three]

/-- Uniform control of the transverse polynomial on the doubled numerical band. -/
theorem cylinder_half_native (m : ℕ) (q : HandleCylinder)
    (hq : q.1 ∈ Icc (-(1 / 2)) (1 / 2)) :
    cylinderComplexMap q ∈ transverseAnnulusDomain m := by
  have hn : ‖cylinderComplexMap q‖ = Real.exp q.1 := cylinderComplexMap_norm q
  have hi : ‖(cylinderComplexMap q)⁻¹‖ = Real.exp (-q.1) := by
    rw [norm_inv, hn, Real.exp_neg]
  have hplus : ‖plus (cylinderComplexMap q)‖ ≤ 11 / 8 := by
    have htri : ‖plus (cylinderComplexMap q)‖ ≤
        (Real.exp q.1 + Real.exp (-q.1)) / 2 := by
      unfold plus
      rw [norm_div]
      rw [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      exact (div_le_div_iff_of_pos_right (by norm_num)).mpr (by simpa only [hn, hi] using
        (norm_add_le (cylinderComplexMap q) ((cylinderComplexMap q)⁻¹)))
    have he := exp_half_lt_seven_quarters
    have hp : Real.exp q.1 ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hq.2
    have hm : Real.exp (-q.1) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [hq.1])
    by_cases hs : 0 ≤ q.1
    · have hsmall : Real.exp (-q.1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · have hsmall : Real.exp q.1 ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
  refine ⟨cylinderComplexMap_ne_zero q, ?_⟩
  intro j hj
  have hj' : (2 : ℝ) ≤ (parameters m j).re := by
    simp only [parameters, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have hjval : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr (fun h => hj (Fin.ext h))
    exact_mod_cast (show 2 ≤ j.val + 1 by omega)
  have hr := Complex.re_le_norm (plus (cylinderComplexMap q) ^ 2)
  rw [norm_pow] at hr
  have hnorm := norm_nonneg (plus (cylinderComplexMap q))
  simp only [Complex.sub_re]
  nlinarith

end SymplecticPacking.BranchSmall
