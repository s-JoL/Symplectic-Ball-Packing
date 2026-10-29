import SymplecticPacking.BranchSmall.ReturnPotential

/-!
# Positivity of the bundle potential

The joined Veronese map gives a holomorphic immersion. Its Fubini--Study potential
identifies the bundle form with a positive combination of pullbacks.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

variable {q : ℕ}

def bundlePolynomial (y : Tot q) : NormalPolynomialIndex q → ℂ :=
  joinedVeronese (affineComplex q y.1, y.2)

theorem bundlePolynomial_contDiff : ContDiff ℂ ∞ (bundlePolynomial (q := q)) :=
  joinedVeronese_smooth.comp (((affineComplex q).contDiff.comp contDiff_fst).prodMk contDiff_snd)

theorem bundlePolynomial_sq (y : Tot q) :
    1 + phaseSq (complexCartesian (bundlePolynomial y)) = (1 + nsq y.1) ^ 2 + wsq y.2 := by
  rw [bundlePolynomial, joinedVeronese_sq, complexCartesian_affineComplex,
    ← nsq_eq_phaseSq, complexCartesian_sq]
  rfl

theorem bundlePot_decomposition (b : ℝ) :
    bundlePot (q := q) b = fun y =>
      (1 - 2 * b) * Real.log (1 + nsq y.1) + b * fsPotential (bundlePolynomial y) := by
  funext y
  have hpos := one_add_nsq_pos y.1
  have hw := wsq_nonneg y.2
  have heq : 1 + wsq y.2 / (1 + nsq y.1) ^ 2 =
      ((1 + nsq y.1) ^ 2 + wsq y.2) / (1 + nsq y.1) ^ 2 := by field_simp
  have hlog : Real.log (1 + wsq y.2 / (1 + nsq y.1) ^ 2) =
      Real.log ((1 + nsq y.1) ^ 2 + wsq y.2) - 2 * Real.log (1 + nsq y.1) := by
    rw [heq, Real.log_div (by positivity : (1 + nsq y.1) ^ 2 + wsq y.2 ≠ 0)
      (pow_ne_zero 2 hpos.ne'), Real.log_pow]
    norm_num
  simp only [bundlePot, fsPotential, bundlePolynomial_sq, hlog]
  ring

theorem bundlePolynomial_hasFDerivAt (y : Tot q) :
    HasFDerivAt bundlePolynomial
      ((joinedVeroneseDerivative (affineComplex q y.1, y.2)).comp
        (((affineComplex q).comp (ContinuousLinearMap.fst ℂ _ _)).prod
          (ContinuousLinearMap.snd ℂ _ _))) y :=
  (joinedVeronese_hasFDerivAt _).comp y
    ((((affineComplex q).hasFDerivAt).comp y hasFDerivAt_fst).prodMk hasFDerivAt_snd)

theorem bundlePolynomial_derivative_injective (y : Tot q) :
    Function.Injective (fderiv ℂ bundlePolynomial y) := by
  rw [(bundlePolynomial_hasFDerivAt y).fderiv]
  intro v w h
  apply Prod.ext
  · apply Prod.ext
    · have hh := congrArg (fun f => f (.inl (.inl (false, none)))) h
      exact hh
    · funext j
      have hh := congrArg (fun f => f (.inl (.inl (false, some j)))) h
      exact hh
  · funext j
    have hh := congrArg (fun f => f (.inr j)) h
    exact hh

def bundlePhaseCoordinates : Tot q →L[ℝ] ConeTarget q :=
  ((affinePhase q).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((complexCartesian (ι := Fin q)).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ _ _))

theorem bundlePot_dc (b : ℝ) :
    dcForm (bundlePot (q := q) b) =
      primitivePullback (conePrimitive (1 / Real.pi) b) bundlePhaseCoordinates := by
  let L : Tot q →L[ℂ] ((Option (Fin q) → ℂ) × (Fin q → ℂ)) :=
    ((affineComplex q).comp (ContinuousLinearMap.fst ℂ _ _)).prod (ContinuousLinearMap.snd ℂ _ _)
  have hbase : ContDiff ℝ ∞ (fun y : Tot q => Real.log (1 + nsq y.1)) :=
    ((contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne').comp contDiff_fst
  have hj : ContDiff ℝ ∞ (fsPotential ∘ bundlePolynomial (q := q)) :=
    fsPotential_contDiff.comp (bundlePolynomial_contDiff.restrict_scalars ℝ)
  rw [bundlePot_decomposition]
  change dcForm (fun y => (1 - 2 * b) * Real.log (1 + nsq y.1) +
    b * (fsPotential ∘ bundlePolynomial) y) = _
  rw [dcForm_add ((hbase.differentiable (by simp)).const_mul _) ((hj.differentiable (by simp)).const_mul _),
    dcForm_const_mul (hbase.differentiable (by simp)), dcForm_const_mul (hj.differentiable (by simp)),
    fsPotential_comp_dc (bundlePolynomial_contDiff.differentiable (by simp))]
  have hbaseD : dcForm (fun y : Tot q => Real.log (1 + nsq y.1)) =
      SymplecticPacking.Forms.pull1 (ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ))
        (ambientFSPrimitive (1 / Real.pi)) := by
    rw [← dcForm_logPot]
    exact (dcForm_comp_holomorphic
      (ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ)).differentiable
      (((contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne').differentiable
        (by simp))).symm
  rw [hbaseD]
  funext y
  apply ContinuousLinearMap.ext
  intro v
  have h := joinedVeronese_primitive (1 / Real.pi) b (L y) (L v)
  have hd := (complexCartesian (ι := NormalPolynomialIndex q)).toContinuousLinearMap.hasFDerivAt.comp y
    ((bundlePolynomial_hasFDerivAt y).restrictScalars ℝ)
  change HasFDerivAt (fun z => complexCartesian (bundlePolynomial z)) _ y at hd
  simp only [primitivePullback, ContinuousLinearMap.comp_apply] at h
  rw [joinedVeronese_real_derivative] at h
  simp only [primitivePullback, ContinuousLinearMap.comp_apply, hd.fderiv,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    bundlePhaseCoordinates, SymplecticPacking.Forms.pull1_apply,
    ((ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ)).hasFDerivAt.restrictScalars ℝ).fderiv,
    Pi.add_apply, Pi.smul_apply, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.fderiv]
  simpa only [bundlePolynomial, L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, complexCartesian_affineComplex, ambientFSPrimitive,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe] using h

theorem bundleForm_pos {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (y v : Tot q) (hv : v ≠ 0) : 0 < bundleForm b y v (Complex.I • v) := by
  have hbase : ContDiff ℝ ∞ (fun y : Tot q => Real.log (1 + nsq y.1)) :=
    ((contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne').comp contDiff_fst
  have hj : ContDiff ℝ ∞ (fsPotential ∘ bundlePolynomial (q := q)) :=
    fsPotential_contDiff.comp (bundlePolynomial_contDiff.restrict_scalars ℝ)
  have hbaseN : 0 ≤ ddcForm (fun y : Tot q => Real.log (1 + nsq y.1)) y v (Complex.I • v) := by
    change 0 ≤ ddcForm ((fun z : Affine q => Real.log (1 + nsq z)) ∘
      (ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ))) y v (Complex.I • v)
    rw [ddcForm_comp_holomorphic (ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ)).differentiable
      ((ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ)).contDiff.restrict_scalars ℝ)
      ((contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne')]
    rw [((ContinuousLinearMap.fst ℂ (Affine q) (Fin q → ℂ)).hasFDerivAt.restrictScalars ℝ).fderiv]
    change 0 ≤ ddcForm (fun z : Affine q => Real.log (1 + nsq z)) y.1 v.1 (Complex.I • v.1)
    rw [ddcForm_logPot, affinePhase_I]
    by_cases hv0 : v.1 = 0
    · simp [hv0]
    · exact (affineFSForm_positive (one_div_pos.mpr Real.pi_pos) _ _
        (fun h => hv0 (affinePhase_injective q (h.trans (map_zero _).symm)))).le
  have hjP : 0 < ddcForm (fsPotential ∘ bundlePolynomial) y v (Complex.I • v) := by
    rw [ddcForm_comp_holomorphic (bundlePolynomial_contDiff.differentiable (by simp))
      (bundlePolynomial_contDiff.restrict_scalars ℝ) fsPotential_contDiff]
    have hI : fderiv ℝ bundlePolynomial y (Complex.I • v) =
        Complex.I • fderiv ℝ bundlePolynomial y v := by
      rw [(bundlePolynomial_contDiff.differentiable (by simp) y).fderiv_restrictScalars ℝ]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
    rw [hI]
    apply fsPotential_ddc_pos
    rw [(bundlePolynomial_contDiff.differentiable (by simp) y).fderiv_restrictScalars ℝ]
    intro h
    apply hv
    apply bundlePolynomial_derivative_injective y
    simpa only [map_zero, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe] using h
  unfold bundleForm
  rw [bundlePot_decomposition]
  change 0 < ddcForm (fun y => (1 - 2 * b) * Real.log (1 + nsq y.1) +
    b * (fsPotential ∘ bundlePolynomial) y) y v (Complex.I • v)
  rw [ddcForm_add (contDiff_const.mul hbase) (contDiff_const.mul hj), ddcForm_const_mul hbase,
    ddcForm_const_mul hj]
  change 0 < (1 - 2 * b) * _ + b * _
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hbaseN) (mul_pos hb0 hjP)

end SymplecticPacking.BranchSmall.VT
