import SymplecticPacking.General.Ham.Linear.Blocks

/-!
# The unitary part of `Sp(2n)`: rotations and the Cayley path

A matrix of *unitary type* is orthogonal and commutes with `J`; these form the image of `U(n)`
in `Sp(2n)` (under `z = q + i p`). The scalar rotations `rot θ = cos θ + sin θ · J` (multiplication
by `e^{iθ}`) are of unitary type. For a skew-symmetric `X` commuting with `J`, the Cayley path
`cayley X σ = (1 + σX)(1 - σX)⁻¹` is defined for every `σ` (since `1 - σX` is invertible), is of
unitary type, and joins `1` (at `σ = 0`) to `cayley X 1`; for `X = cayleyOf V = (V-1)(V+1)⁻¹`,
`cayley X 1 = V` whenever `V + 1` is invertible.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix
open scoped ContDiff

variable {n : ℕ}

/-- Orthogonal and commuting with `J` (the image of `U(n)` in `Sp(2n)`). -/
def IsUnitaryType (M : Mat n) : Prop := Mᵀ * M = 1 ∧ M * Jm n = Jm n * M

lemma Jm_transpose : (Jm n)ᵀ = -Jm n := Matrix.J_transpose (Fin n) ℝ
lemma Jm_sq : Jm n * Jm n = -1 := Matrix.J_squared (Fin n) ℝ

theorem IsUnitaryType.mem_Sp {M : Mat n} (h : IsUnitaryType M) : M ∈ Sp n := by
  rw [SymplecticGroup.mem_iff']
  calc Mᵀ * Jm n * M = Mᵀ * (Jm n * M) := Matrix.mul_assoc _ _ _
    _ = Mᵀ * (M * Jm n) := by rw [h.2]
    _ = Mᵀ * M * Jm n := (Matrix.mul_assoc _ _ _).symm
    _ = Jm n := by rw [h.1, Matrix.one_mul]

theorem IsUnitaryType.mul {M N : Mat n} (hM : IsUnitaryType M) (hN : IsUnitaryType N) :
    IsUnitaryType (M * N) := by
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM.1, Matrix.one_mul, hN.1]
  · rw [Matrix.mul_assoc, hN.2, ← Matrix.mul_assoc, hM.2, Matrix.mul_assoc]

lemma IsUnitaryType.mul_transpose {M : Mat n} (h : IsUnitaryType M) : M * Mᵀ = 1 :=
  mul_eq_one_comm.mp h.1

/-! ### Rotations -/

/-- `rot θ = cos θ · 1 + sin θ · J`, multiplication by `e^{iθ}`. -/
def rot (θ : ℝ) : Mat n := Real.cos θ • (1 : Mat n) + Real.sin θ • Jm n

lemma rot_zero : rot (n := n) 0 = 1 := by simp [rot]

lemma rot_mul_rot (a b : ℝ) : rot (n := n) a * rot b = rot (a + b) := by
  simp only [rot, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Jm_sq, smul_smul, Real.cos_add, Real.sin_add, smul_neg, sub_smul, add_smul]
  module

lemma rot_transpose (θ : ℝ) : (rot (n := n) θ)ᵀ = rot (-θ) := by
  simp only [rot, transpose_add, transpose_smul, transpose_one, Jm_transpose, Real.cos_neg,
    Real.sin_neg, smul_neg, neg_smul]

lemma rot_comm_J (θ : ℝ) : rot (n := n) θ * Jm n = Jm n * rot θ := by
  simp only [rot, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

theorem rot_isUnitaryType (θ : ℝ) : IsUnitaryType (rot (n := n) θ) :=
  ⟨by rw [rot_transpose, rot_mul_rot, neg_add_cancel, rot_zero], rot_comm_J θ⟩

lemma smoothEntries_rot (θ : ℝ) : SmoothEntries fun σ : ℝ => rot (n := n) (σ * θ) := by
  have hc : ContDiff ℝ ∞ (fun σ : ℝ => Real.cos (σ * θ)) :=
    Real.contDiff_cos.comp (contDiff_id.mul contDiff_const)
  have hs : ContDiff ℝ ∞ (fun σ : ℝ => Real.sin (σ * θ)) :=
    Real.contDiff_sin.comp (contDiff_id.mul contDiff_const)
  exact (SmoothEntries.smul hc (SmoothEntries.const _)).add
    (SmoothEntries.smul hs (SmoothEntries.const _))

/-! ### Cancellation -/

lemma cancel_right {P Q B : Mat n} (hB : B.det ≠ 0) (h : P * B = Q * B) : P = Q := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  calc P = P * B * B⁻¹ := (Matrix.mul_nonsing_inv_cancel_right B P hu).symm
    _ = Q * B * B⁻¹ := by rw [h]
    _ = Q := Matrix.mul_nonsing_inv_cancel_right B Q hu

lemma cancel_left {P Q B : Mat n} (hB : B.det ≠ 0) (h : B * P = B * Q) : P = Q := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  calc P = B⁻¹ * (B * P) := (Matrix.nonsing_inv_mul_cancel_left B P hu).symm
    _ = B⁻¹ * (B * Q) := by rw [h]
    _ = Q := Matrix.nonsing_inv_mul_cancel_left B Q hu

lemma mul_inv_mul_cancel {P B : Mat n} (hB : B.det ≠ 0) : P * B⁻¹ * B = P :=
  Matrix.nonsing_inv_mul_cancel_right B P (isUnit_iff_ne_zero.mpr hB)

/-! ### The Cayley path -/

/-- `1 - σ X` is invertible for skew-symmetric `X` (`v ⬝ (1 - σX) v = |v|²`). -/
theorem det_one_sub_smul_ne_zero {X : Mat n} (hX : Xᵀ = -X) (σ : ℝ) :
    (1 - σ • X).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : v = σ • (X *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hv
    exact hv
  have hskew : v ⬝ᵥ (X *ᵥ v) = 0 := by
    have h2 : v ⬝ᵥ (X *ᵥ v) = -(v ⬝ᵥ (X *ᵥ v)) := by
      calc v ⬝ᵥ (X *ᵥ v) = (Xᵀ *ᵥ v) ⬝ᵥ v := by
            rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
        _ = -(v ⬝ᵥ (X *ᵥ v)) := by
            rw [hX, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have h3 : v ⬝ᵥ v = 0 := by
    calc v ⬝ᵥ v = v ⬝ᵥ (σ • (X *ᵥ v)) := by rw [← h1]
      _ = 0 := by rw [dotProduct_smul, hskew, smul_zero]
  exact hv0 (dotProduct_self_eq_zero.mp h3)

/-- The Cayley path `(1 + σX)(1 - σX)⁻¹`. -/
def cayley (X : Mat n) (σ : ℝ) : Mat n := (1 + σ • X) * (1 - σ • X)⁻¹

lemma cayley_zero (X : Mat n) : cayley X 0 = 1 := by simp [cayley]

/-- The Cayley path of a skew-symmetric `X` commuting with `J` is of unitary type. -/
theorem cayley_isUnitaryType {X : Mat n} (hX : Xᵀ = -X) (hXJ : X * Jm n = Jm n * X) (σ : ℝ) :
    IsUnitaryType (cayley X σ) := by
  have hB : (1 - σ • X).det ≠ 0 := det_one_sub_smul_ne_zero hX σ
  have hCB : cayley X σ * (1 - σ • X) = 1 + σ • X := mul_inv_mul_cancel hB
  have hAT : (1 + σ • X)ᵀ = 1 - σ • X := by
    simp [transpose_add, transpose_smul, hX, sub_eq_add_neg]
  have hBT : (1 - σ • X)ᵀ = 1 + σ • X := by
    simp [transpose_sub, transpose_smul, hX, sub_eq_add_neg]
  have hAB : (1 + σ • X) * (1 - σ • X) = (1 - σ • X) * (1 + σ • X) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
    abel
  have hXJ' : ∀ c : ℝ, (1 + c • X) * Jm n = Jm n * (1 + c • X) := fun c => by
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hXJ]
  refine ⟨?_, ?_⟩
  · apply cancel_right hB
    apply cancel_left (B := (1 - σ • X)ᵀ) (by rw [det_transpose]; exact hB)
    rw [Matrix.one_mul]
    calc (1 - σ • X)ᵀ * ((cayley X σ)ᵀ * cayley X σ * (1 - σ • X))
        = (cayley X σ * (1 - σ • X))ᵀ * (cayley X σ * (1 - σ • X)) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (1 - σ • X)ᵀ * (1 - σ • X) := by rw [hCB, hAT, hBT, hAB]
  · apply cancel_right hB
    have hJB : Jm n * (1 - σ • X) = (1 - σ • X) * Jm n := by
      have := hXJ' (-σ); simp only [neg_smul, ← sub_eq_add_neg] at this; exact this.symm
    rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hCB, hXJ' σ, Matrix.mul_assoc, hCB]

theorem smoothEntries_cayley {X : Mat n} (hX : Xᵀ = -X) : SmoothEntries (cayley X) := by
  unfold cayley
  refine SmoothEntries.mul ?_ (SmoothEntries.inv ?_ (det_one_sub_smul_ne_zero hX))
  · exact (SmoothEntries.const 1).add (SmoothEntries.smul contDiff_id (SmoothEntries.const X))
  · exact (SmoothEntries.const 1).sub (SmoothEntries.smul contDiff_id (SmoothEntries.const X))

/-- The Cayley transform `(V - 1)(V + 1)⁻¹`. -/
def cayleyOf (V : Mat n) : Mat n := (V - 1) * (V + 1)⁻¹

/-- For `V` of unitary type with `V + 1` invertible, `cayleyOf V` is skew-symmetric. -/
theorem cayleyOf_skew {V : Mat n} (hV : IsUnitaryType V) (hdet : (V + 1).det ≠ 0) :
    (cayleyOf V)ᵀ = -cayleyOf V := by
  have hXW : cayleyOf V * (V + 1) = V - 1 := mul_inv_mul_cancel hdet
  rw [← add_eq_zero_iff_eq_neg]
  apply cancel_right hdet
  apply cancel_left (B := (V + 1)ᵀ) (by rw [det_transpose]; exact hdet)
  rw [Matrix.zero_mul, Matrix.mul_zero, add_mul, mul_add]
  calc (V + 1)ᵀ * ((cayleyOf V)ᵀ * (V + 1)) + (V + 1)ᵀ * (cayleyOf V * (V + 1))
      = (cayleyOf V * (V + 1))ᵀ * (V + 1) + (V + 1)ᵀ * (cayleyOf V * (V + 1)) := by
        rw [transpose_mul, Matrix.mul_assoc]
    _ = 0 := by
        rw [hXW]
        simp only [transpose_add, transpose_sub, transpose_one, add_mul, mul_add, sub_mul,
          mul_sub, Matrix.one_mul, Matrix.mul_one, hV.1]
        abel

/-- For `V` commuting with `J`, so does `cayleyOf V`. -/
theorem cayleyOf_comm_J {V : Mat n} (hV : IsUnitaryType V) (hdet : (V + 1).det ≠ 0) :
    cayleyOf V * Jm n = Jm n * cayleyOf V := by
  have hXW : cayleyOf V * (V + 1) = V - 1 := mul_inv_mul_cancel hdet
  have hJW : Jm n * (V + 1) = (V + 1) * Jm n := by
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hV.2]
  apply cancel_right hdet
  rw [Matrix.mul_assoc, hJW, ← Matrix.mul_assoc, hXW, Matrix.mul_assoc, hXW]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hV.2]

/-- `cayley (cayleyOf V) 1 = V` when `V + 1` is invertible. -/
theorem cayley_cayleyOf_one {V : Mat n} (hV : IsUnitaryType V) (hdet : (V + 1).det ≠ 0) :
    cayley (cayleyOf V) 1 = V := by
  have hXW : cayleyOf V * (V + 1) = V - 1 := mul_inv_mul_cancel hdet
  have hsub : (1 - (1 : ℝ) • cayleyOf V) * (V + 1) = (2 : ℝ) • (1 : Mat n) := by
    rw [one_smul, sub_mul, Matrix.one_mul, hXW, two_smul]; abel
  have hB : (1 - (1 : ℝ) • cayleyOf V).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsub
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ two_ne_zero this.symm
  unfold cayley
  apply cancel_right hB
  rw [mul_inv_mul_cancel hB]
  apply cancel_right hdet
  rw [one_smul, add_mul, Matrix.one_mul, hXW, Matrix.mul_assoc, sub_mul, Matrix.one_mul, hXW]
  simp only [mul_add, mul_sub, Matrix.mul_one]
  abel

end SymplecticPacking.General.Ham.Linear
