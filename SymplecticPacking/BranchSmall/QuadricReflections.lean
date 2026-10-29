import SymplecticPacking.BranchSmall.ProjectiveCoordinates

/-!
# Coordinate reflections of the explicit diagonal-quadric models
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Function ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

variable {m : ℕ}

def signOutput (u : Option (Option (Fin m)) → ℂ) : Option (NormalPolynomialIndex m) → ℂ
  | none => 1
  | some (.inl (.inl i)) => u none * u (some i.2)
  | some (.inl (.inr i)) => u (some i.1) * u (some i.2)
  | some (.inr _) => 1

theorem signOutput_unit (u : Option (Option (Fin m)) → ℂ)
    (hu : ∀ i, Complex.normSq (u i) = 1) (i) : Complex.normSq (signOutput u i) = 1 := by
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp only [signOutput, map_one, map_mul, hu, mul_one]

theorem homogeneousPolynomial_sign (a : Fin m → ℂ) (t : ℝ)
    (u : Option (Option (Fin m)) → ℂ) (hu : ∀ i, u i ^ 2 = 1) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (complexDiagonal u z) =
      complexDiagonal (signOutput u) (homogeneousPolynomial a t z) := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp only [homogeneousPolynomial, complexDiagonal_apply, signOutput, mul_pow, hu, one_mul]
  all_goals ring

def coordinateSign (i : Option (Fin m)) (j : Option (Fin m)) : ℂ := if j = i then -1 else 1

theorem coordinateSign_sq (i j : Option (Fin m)) : coordinateSign i j ^ 2 = 1 := by
  unfold coordinateSign
  split_ifs <;> norm_num

theorem coordinateSign_unit (i j : Option (Fin m)) : Complex.normSq (coordinateSign i j) = 1 := by
  unfold coordinateSign
  split_ifs <;> norm_num

def homogeneousCoordinateSign (i : Option (Fin m)) : Option (Option (Fin m)) → ℂ
  | none => 1
  | some j => coordinateSign i j

theorem homogeneousCoordinateSign_sq (i) (j) : homogeneousCoordinateSign (m := m) i j ^ 2 = 1 := by
  cases j with
  | none => norm_num [homogeneousCoordinateSign]
  | some j => exact coordinateSign_sq i j

theorem homogeneousCoordinateSign_unit (i) (j) : Complex.normSq (homogeneousCoordinateSign (m := m) i j) = 1 := by
  cases j with
  | none => norm_num [homogeneousCoordinateSign]
  | some j => exact coordinateSign_unit i j

def affineReflection (i : Option (Fin m)) : Affine m →L[ℝ] Affine m :=
  (affineComplexEquiv m).symm.toContinuousLinearMap.comp
    ((complexDiagonal (coordinateSign i)).comp (affineComplexEquiv m).toContinuousLinearMap)

theorem affineReflection_coordinates (i : Option (Fin m)) (z : Affine m) :
    affineComplex m (affineReflection i z) = complexDiagonal (coordinateSign i) (affineComplex m z) := by
  change affineComplex m ((affineComplexEquiv m).symm
    (complexDiagonal (coordinateSign i) (affineComplexEquiv m z))) = _
  simpa only [affineComplexEquiv_apply] using
    (affineComplexEquiv m).apply_symm_apply (complexDiagonal (coordinateSign i) (affineComplexEquiv m z))

theorem affineReflection_involutive (i : Option (Fin m)) (z : Affine m) :
    affineReflection i (affineReflection i z) = z := by
  apply (affineComplexEquiv m).injective
  simp only [affineComplexEquiv_apply, affineReflection_coordinates]
  funext j
  simp only [complexDiagonal_apply, ← mul_assoc, ← pow_two, coordinateSign_sq, one_mul]

theorem affineReflection_norm (i : Option (Fin m)) (z : Affine m) : ‖affineReflection i z‖ = ‖z‖ := by
  rw [← affineComplex_norm, affineReflection_coordinates, ← affineComplex_norm z]
  have hu (j : Option (Fin m)) : ‖coordinateSign i j‖₊ = 1 := by
    unfold coordinateSign
    split_ifs <;> simp
  simp only [Pi.norm_def, complexDiagonal_apply, nnnorm_mul, hu, one_mul]

theorem affineReflection_fixed (i : Option (Fin m)) (z : Affine m) :
    affineReflection i z = z ↔ affineComplex m z i = 0 := by
  constructor
  · intro hz
    have hh := congrArg (fun z => affineComplex m z i) hz
    rw [affineReflection_coordinates] at hh
    simp only [complexDiagonal_apply, coordinateSign, ite_true, neg_one_mul] at hh
    have he : (2 : ℂ) * affineComplex m z i = 0 := by linear_combination -hh
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · intro hz
    apply (affineComplexEquiv m).injective
    simp only [affineComplexEquiv_apply, affineReflection_coordinates]
    funext j
    simp only [complexDiagonal_apply, coordinateSign]
    by_cases hji : j = i
    · subst j
      simp only [ite_true, hz, mul_zero]
    · simp only [ite_eq_right hji, one_mul]


theorem affineReflection_equations (a : Fin m → ℂ) (i : Option (Fin m)) (z : Affine m) :
    equations a (affineReflection i z) = equations a z := by
  have hc (j : Option (Fin m)) :
      affineComplex m (affineReflection i z) j = coordinateSign i j * affineComplex m z j := by
    rw [affineReflection_coordinates, complexDiagonal_apply]
  funext j
  have h0 := hc none
  have hj := hc (some j)
  change (affineReflection i z).1 = coordinateSign i none * z.1 at h0
  change (affineReflection i z).2 j = coordinateSign i (some j) * z.2 j at hj
  simp only [equations, h0, hj, mul_pow, coordinateSign_sq, one_mul]

theorem affineReflection_nsq (i : Option (Fin m)) (z : Affine m) :
    nsq (affineReflection i z) = nsq z := by
  rw [nsq_eq_phaseSq, nsq_eq_phaseSq, ← complexCartesian_affineComplex,
    ← complexCartesian_affineComplex, affineReflection_coordinates,
    ← phaseDiagonal_cartesian]
  change phaseDot (phaseDiagonal (coordinateSign i) _) (phaseDiagonal (coordinateSign i) _) = _
  exact phaseDiagonal_dot _ (coordinateSign_unit i) _ _

theorem returnQuotient_reflection (i : Option (Fin m)) (z : HomogeneousInput m) :
    returnQuotient m (complexDiagonal (homogeneousCoordinateSign i) z) =
      affineReflection i (returnQuotient m z) := by
  apply (affineComplexEquiv m).injective
  simp only [affineComplexEquiv_apply, affineReflection_coordinates]
  have hA (z : HomogeneousInput m) : affineComplex m (returnQuotient m z) = complexAffineQuotient z := by
    rw [← affineComplexEquiv_apply, returnQuotient, ContinuousLinearEquiv.apply_symm_apply]
  rw [hA, hA]
  funext j
  simp only [complexAffineQuotient, complexDiagonal_apply, homogeneousCoordinateSign, one_mul]
  ring

theorem returnQuotient_reflection_fderiv (i : Option (Fin m)) (z v : HomogeneousInput m)
    (hz : z none ≠ 0) :
    fderiv ℝ (returnQuotient m) (complexDiagonal (homogeneousCoordinateSign i) z)
      (complexDiagonal (homogeneousCoordinateSign i) v) =
      affineReflection i (fderiv ℝ (returnQuotient m) z v) := by
  let R := complexDiagonal (homogeneousCoordinateSign i)
  have hRz : R z none ≠ 0 := by simpa only [R, complexDiagonal_apply, homogeneousCoordinateSign, one_mul] using hz
  have hQ := (returnQuotient_contDiffAt hz).differentiableAt (by simp)
  have hQR := (returnQuotient_contDiffAt hRz).differentiableAt (by simp)
  have he : returnQuotient m ∘ R = affineReflection i ∘ returnQuotient m :=
    funext fun z => returnQuotient_reflection i z
  have hd := fderiv_comp z hQR R.differentiableAt
  rw [he, fderiv_comp z (affineReflection i).differentiableAt hQ, (affineReflection i).fderiv] at hd
  rw [R.fderiv] at hd
  simpa only [ContinuousLinearMap.comp_apply] using (congrArg (fun L => L v) hd).symm

theorem homogeneousReturn_reflection (a : Fin m → ℂ) (t : ℝ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (i : Option (Fin m))
    (z : HomogeneousInput m) (hz : z ≠ 0) :
    complexCartesian.symm (homogeneousConeField (homogeneousCartesian a t) (1 / Real.pi) b 1
      (complexCartesian (complexDiagonal (homogeneousCoordinateSign i) z))) =
    complexDiagonal (homogeneousCoordinateSign i)
      (complexCartesian.symm (homogeneousConeField (homogeneousCartesian a t) (1 / Real.pi) b 1
        (complexCartesian z))) := by
  let u := homogeneousCoordinateSign i
  have hzc : complexCartesian z ≠ 0 := fun he => hz (complexCartesian.injective (he.trans (map_zero _).symm))
  have he := homogeneousConeField_linear_invariant (s := 1) (d := b)
    (homogeneousCartesian_smooth a t) (fun _ hz => homogeneousCartesian_nonzero a t hz)
    (homogeneousCartesian_euler a t) (homogeneousCartesian_J a t)
    (phaseUnitDiagonal u (homogeneousCoordinateSign_unit i)) (phaseDiagonal (signOutput u))
    (homogeneousCartesian_diagonal a t u (homogeneousCoordinateSign_unit i) (signOutput u)
      (homogeneousPolynomial_sign a t u (homogeneousCoordinateSign_sq i)))
    (phaseDiagonal_dot _ (homogeneousCoordinateSign_unit i)) (phaseDiagonal_area _ (homogeneousCoordinateSign_unit i))
    (phaseDiagonal_dot _ (signOutput_unit u (homogeneousCoordinateSign_unit i)))
    (phaseDiagonal_area _ (signOutput_unit u (homogeneousCoordinateSign_unit i)))
    (one_div_pos.mpr Real.pi_pos) (by simpa only [one_mul] using hb0)
    (by simpa only [one_mul] using hb) hzc
  have hh := congrArg (fun p => complexCartesian.symm p) he
  simpa only [phaseUnitDiagonal_apply, phaseDiagonal_cartesian, phaseDiagonal,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hh

theorem normalReturnField_reflection (a : Fin m → ℂ) (t : ℝ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (i : Option (Fin m)) (z : Affine m) :
    normalReturnField a b t (affineReflection i z) = affineReflection i (normalReturnField a b t z) := by
  let Z : HomogeneousInput m := complexAffineLift (affineComplex m z)
  let R := complexDiagonal (homogeneousCoordinateSign i)
  have hZ : Z none ≠ 0 := one_ne_zero
  have hZ0 : Z ≠ 0 := fun he => hZ (congrFun he none)
  have hRZ : R Z none ≠ 0 := by simp only [R, complexDiagonal_apply, homogeneousCoordinateSign, Z, complexAffineLift_none, one_mul, ne_eq, one_ne_zero, not_false_eq_true]
  have hQ : returnQuotient m Z = z := by
    unfold returnQuotient
    rw [complexAffineQuotient_lift, ← affineComplexEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hQR : returnQuotient m (R Z) = affineReflection i z := by rw [returnQuotient_reflection, hQ]
  have h1 := normalReturnField_eq_homogeneous a t hb0 hb Z hZ
  have h2 := normalReturnField_eq_homogeneous a t hb0 hb (R Z) hRZ
  rw [hQ] at h1
  rw [hQR, homogeneousReturn_reflection a t hb0 hb i Z hZ0,
    returnQuotient_reflection_fderiv i Z _ hZ, ← h1] at h2
  exact h2

end SymplecticPacking.BranchSmall.VT
