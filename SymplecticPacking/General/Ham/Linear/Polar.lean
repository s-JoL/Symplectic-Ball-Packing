import SymplecticPacking.General.Ham.Linear.Unitary
import SymplecticPacking.Explicit

/-!
# Explicit polar-type decomposition of a symplectic matrix

For `M = [[a, b], [c, d]] ∈ Sp(2n)` let `p = aᵀa + cᵀc` (positive definite, since `M` is
invertible) and `P = √p` its positive square root (the definite description of the unique positive
semidefinite `P` with `P² = p`). Then `x = a P⁻¹`, `y = c P⁻¹` give a matrix
`U = [[x, -y], [y, x]]` of unitary type (`xᵀx + yᵀy = 1` and `xᵀy` symmetric, by the Lagrangian
relation `aᵀc = cᵀa`), and `Uᵀ M = [[P, P S], [0, P⁻¹]]` with `S` symmetric, i.e.

  `M = U · Dg(P, P⁻¹) · Up(S)`.

The positive-definite part is joined to `1` by `posPath P σ = 1 + sin²(πσ/2) (P - 1)`, positive
definite for every `σ`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix
open scoped ContDiff MatrixOrder

variable {n : ℕ}

/-- `p = aᵀa + cᵀc` for `M = [[a,b],[c,d]]`. -/
def gram (M : Mat n) : Sq n :=
  M.toBlocks₁₁ᵀ * M.toBlocks₁₁ + M.toBlocks₂₁ᵀ * M.toBlocks₂₁

open scoped Classical in
/-- The positive square root of `p`: the unique positive semidefinite `P` with `P * P = p`
(definite description; `1` if `p` is not positive semidefinite). -/
def posSqrt (p : Sq n) : Sq n :=
  if h : ∃! P : Sq n, 0 ≤ P ∧ P * P = p then Explicit.the h else 1

/-- Existence and uniqueness of the positive square root (`CFC.sqrt`, `CFC.sqrt_unique`). -/
theorem existsUnique_posSqrt {p : Sq n} (hp : 0 ≤ p) : ∃! P : Sq n, 0 ≤ P ∧ P * P = p :=
  ⟨CFC.sqrt p, ⟨CFC.sqrt_nonneg p, CFC.sqrt_mul_sqrt_self p hp⟩,
    fun _ hb => (CFC.sqrt_unique hb.2 hb.1).symm⟩

theorem posSqrt_spec {p : Sq n} (hp : 0 ≤ p) : 0 ≤ posSqrt p ∧ posSqrt p * posSqrt p = p := by
  have h := existsUnique_posSqrt hp
  rw [posSqrt, dif_pos h]
  exact Explicit.the_spec (P := fun P : Sq n => 0 ≤ P ∧ P * P = p) h

/-- `P = √(aᵀa + cᵀc)`. -/
def polarP (M : Mat n) : Sq n := posSqrt (gram M)

/-- The unitary part `U = [[a P⁻¹, -c P⁻¹], [c P⁻¹, a P⁻¹]]`. -/
def polarU (M : Mat n) : Mat n :=
  fromBlocks (M.toBlocks₁₁ * (polarP M)⁻¹) (-(M.toBlocks₂₁ * (polarP M)⁻¹))
    (M.toBlocks₂₁ * (polarP M)⁻¹) (M.toBlocks₁₁ * (polarP M)⁻¹)

/-- The shear part `S = P⁻¹ (Uᵀ M)₁₂`. -/
def polarS (M : Mat n) : Sq n := (polarP M)⁻¹ * ((polarU M)ᵀ * M).toBlocks₁₂

/-- `aᵀa + cᵀc` is positive definite for `M ∈ Sp(2n)`. -/
theorem gram_posDef {M : Mat n} (hM : M ∈ Sp n) : (gram M).PosDef := by
  set L : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ := M.submatrix id Sum.inl
  have hL : gram M = Lᴴ * L := by
    ext j l
    simp [gram, L, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁,
      Matrix.conjTranspose_apply]
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (SymplecticGroup.symplectic_det hM)
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hMu
  have hLv : ∀ x : Fin n → ℝ, L *ᵥ x = M *ᵥ Sum.elim x 0 := by
    intro x; ext r
    simp [L, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hL]
  refine Matrix.PosDef.conjTranspose_mul_self L fun x y hxy => ?_
  have h : Sum.elim x 0 = Sum.elim y 0 :=
    hinj (show M *ᵥ Sum.elim x 0 = M *ᵥ Sum.elim y 0 by rw [← hLv x, ← hLv y]; exact hxy)
  funext j
  simpa using congrFun h (Sum.inl j)

/-- `P` is symmetric and positive definite. -/
theorem polarP_posDef {M : Mat n} (hM : M ∈ Sp n) : (polarP M).PosDef := by
  have hg := gram_posDef hM
  have hg0 : 0 ≤ gram M := Matrix.nonneg_iff_posSemidef.mpr hg.posSemidef
  obtain ⟨hP0, hPP⟩ := posSqrt_spec hg0
  have hPsd : (polarP M).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP0
  refine hPsd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr ?_)
  have hgd : (gram M).det ≠ 0 := hg.det_pos.ne'
  rw [← hPP, Matrix.det_mul] at hgd
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hgd)

theorem polarP_transpose {M : Mat n} (hM : M ∈ Sp n) : (polarP M)ᵀ = polarP M :=
  (polarP_posDef hM).isHermitian.eq

/-- The algebraic facts used below. -/
lemma polar_facts {M : Mat n} (hM : M ∈ Sp n) :
    (polarP M)ᵀ = polarP M ∧ ((polarP M)⁻¹)ᵀ = (polarP M)⁻¹ ∧
      polarP M * polarP M = gram M ∧ (polarP M).det ≠ 0 ∧
      M.toBlocks₂₁ᵀ * M.toBlocks₁₁ = M.toBlocks₁₁ᵀ * M.toBlocks₂₁ := by
  have hP := polarP_posDef hM
  have hPT := polarP_transpose hM
  have hg0 : 0 ≤ gram M := Matrix.nonneg_iff_posSemidef.mpr (gram_posDef hM).posSemidef
  have hM' : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ ∈ Sp n := by
    rw [fromBlocks_toBlocks]; exact hM
  refine ⟨hPT, by rw [Matrix.transpose_nonsing_inv, hPT], (posSqrt_spec hg0).2, hP.det_pos.ne',
    (mem_Sp_fromBlocks.mp hM').1⟩

/-- `xᵀx + yᵀy = 1` and `xᵀy = yᵀx` for `x = a P⁻¹`, `y = c P⁻¹`. -/
lemma polar_xy {M : Mat n} (hM : M ∈ Sp n) :
    (M.toBlocks₁₁ * (polarP M)⁻¹)ᵀ * (M.toBlocks₁₁ * (polarP M)⁻¹) +
        (M.toBlocks₂₁ * (polarP M)⁻¹)ᵀ * (M.toBlocks₂₁ * (polarP M)⁻¹) = 1 ∧
      (M.toBlocks₁₁ * (polarP M)⁻¹)ᵀ * (M.toBlocks₂₁ * (polarP M)⁻¹) =
        (M.toBlocks₂₁ * (polarP M)⁻¹)ᵀ * (M.toBlocks₁₁ * (polarP M)⁻¹) := by
  obtain ⟨hPT, hPiT, hPP, hdet, hLag⟩ := polar_facts hM
  have hu : IsUnit (polarP M).det := isUnit_iff_ne_zero.mpr hdet
  simp only [transpose_mul, hPiT]
  refine ⟨?_, ?_⟩
  · calc (polarP M)⁻¹ * M.toBlocks₁₁ᵀ * (M.toBlocks₁₁ * (polarP M)⁻¹) +
          (polarP M)⁻¹ * M.toBlocks₂₁ᵀ * (M.toBlocks₂₁ * (polarP M)⁻¹)
        = (polarP M)⁻¹ * (polarP M * polarP M) * (polarP M)⁻¹ := by
          rw [hPP, gram]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hu]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M.toBlocks₁₁ᵀ, ← hLag, Matrix.mul_assoc]

theorem polarU_isUnitaryType {M : Mat n} (hM : M ∈ Sp n) : IsUnitaryType (polarU M) := by
  obtain ⟨hxx, hxy⟩ := polar_xy hM
  refine ⟨?_, ?_⟩
  · rw [polarU, fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
    simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    congr 1
    all_goals first
      | exact hxx
      | (rw [add_comm]; exact hxx)
      | (rw [hxy]; abel)
  · simp only [polarU, Jm, J, fromBlocks_multiply]
    simp

/-- `Uᵀ M = [[P, N₁₂], [0, P⁻¹]]` with `P⁻¹ N₁₂` symmetric. -/
lemma polar_N {M : Mat n} (hM : M ∈ Sp n) :
    (polarU M)ᵀ * M = fromBlocks (polarP M) ((polarU M)ᵀ * M).toBlocks₁₂ 0 (polarP M)⁻¹ ∧
      ((polarP M)⁻¹ * ((polarU M)ᵀ * M).toBlocks₁₂)ᵀ =
        (polarP M)⁻¹ * ((polarU M)ᵀ * M).toBlocks₁₂ := by
  obtain ⟨hPT, hPiT, hPP, hdet, hLag⟩ := polar_facts hM
  have hu : IsUnit (polarP M).det := isUnit_iff_ne_zero.mpr hdet
  set P := polarP M
  set a := M.toBlocks₁₁
  set c := M.toBlocks₂₁
  have hNb : (polarU M)ᵀ * M = fromBlocks ((a * P⁻¹)ᵀ * a + (c * P⁻¹)ᵀ * c)
      ((a * P⁻¹)ᵀ * M.toBlocks₁₂ + (c * P⁻¹)ᵀ * M.toBlocks₂₂)
      ((-(c * P⁻¹))ᵀ * a + (a * P⁻¹)ᵀ * c)
      ((-(c * P⁻¹))ᵀ * M.toBlocks₁₂ + (a * P⁻¹)ᵀ * M.toBlocks₂₂) := by
    calc (polarU M)ᵀ * M = (polarU M)ᵀ * fromBlocks a M.toBlocks₁₂ c M.toBlocks₂₂ := by
          rw [fromBlocks_toBlocks]
      _ = _ := by rw [polarU, fromBlocks_transpose, fromBlocks_multiply]
  have h11 : (a * P⁻¹)ᵀ * a + (c * P⁻¹)ᵀ * c = P := by
    rw [transpose_mul, transpose_mul, hPiT, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add]
    rw [show aᵀ * a + cᵀ * c = gram M from rfl, ← hPP, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h21 : (-(c * P⁻¹))ᵀ * a + (a * P⁻¹)ᵀ * c = 0 := by
    rw [transpose_neg, transpose_mul, transpose_mul, hPiT, Matrix.neg_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, hLag]
    abel
  rw [h11, h21] at hNb
  have hNmem : (polarU M)ᵀ * M ∈ Sp n :=
    Submonoid.mul_mem _ (SymplecticGroup.transpose_mem (polarU_isUnitaryType hM).mem_Sp) hM
  rw [hNb] at hNmem
  obtain ⟨-, h2, -, h4⟩ := mem_Sp_fromBlocks.mp hNmem
  rw [hPT, transpose_zero, Matrix.zero_mul, sub_zero] at h2
  have h22 : ((-(c * P⁻¹))ᵀ * M.toBlocks₁₂ + (a * P⁻¹)ᵀ * M.toBlocks₂₂) = P⁻¹ :=
    (Matrix.inv_eq_right_inv h2).symm
  rw [h22] at hNb h4
  have h12 : ((polarU M)ᵀ * M).toBlocks₁₂ =
      (a * P⁻¹)ᵀ * M.toBlocks₁₂ + (c * P⁻¹)ᵀ * M.toBlocks₂₂ := by
    rw [hNb, toBlocks_fromBlocks₁₂]
  refine ⟨by rw [hNb, toBlocks_fromBlocks₁₂], ?_⟩
  rw [h12, transpose_mul, hPiT, ← h4, hPiT]

theorem polarS_transpose {M : Mat n} (hM : M ∈ Sp n) : (polarS M)ᵀ = polarS M :=
  (polar_N hM).2

/-- **Decomposition** `M = U · Dg(P, P⁻¹) · Up(S)`. -/
theorem polar_decomp {M : Mat n} (hM : M ∈ Sp n) :
    M = polarU M * Dg (polarP M) (polarP M)⁻¹ * Up (polarS M) := by
  obtain ⟨-, -, -, hdet, -⟩ := polar_facts hM
  have hu : IsUnit (polarP M).det := isUnit_iff_ne_zero.mpr hdet
  have hUT := (polarU_isUnitaryType hM).mul_transpose
  rw [Matrix.mul_assoc, Dg_mul_Up, polarS, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul, ← (polar_N hM).1, ← Matrix.mul_assoc, hUT, Matrix.one_mul]

/-! ### The positive-definite path -/

/-- `posPath P σ = 1 + sin²(πσ/2) (P - 1)`: `1` at `σ = 0`, `P` at `σ = 1`. -/
def posPath (P : Sq n) (σ : ℝ) : Sq n := 1 + (Real.sin (Real.pi * σ / 2) ^ 2) • (P - 1)

lemma posPath_zero (P : Sq n) : posPath P 0 = 1 := by simp [posPath]

lemma posPath_one (P : Sq n) : posPath P 1 = P := by
  simp [posPath]

/-- `posPath P σ` is a convex combination of `1` and `P`, hence positive definite. -/
theorem posPath_posDef {P : Sq n} (hP : P.PosDef) (σ : ℝ) : (posPath P σ).PosDef := by
  set t := Real.sin (Real.pi * σ / 2) ^ 2
  have ht0 : 0 ≤ t := sq_nonneg _
  have ht1 : t ≤ 1 := by
    simp only [t]; nlinarith [Real.sin_sq_add_cos_sq (Real.pi * σ / 2),
      sq_nonneg (Real.cos (Real.pi * σ / 2))]
  have heq : posPath P σ = (1 - t) • (1 : Sq n) + t • P := by
    simp only [posPath, t, smul_sub, sub_smul, one_smul]; abel
  rw [heq]
  rcases ht1.lt_or_eq with h1 | h1
  · exact (Matrix.PosDef.one.smul (by linarith)).add_posSemidef (hP.posSemidef.smul ht0)
  · rw [h1, sub_self, zero_smul, zero_add, one_smul]; exact hP

lemma posPath_transpose {P : Sq n} (hP : Pᵀ = P) (σ : ℝ) : (posPath P σ)ᵀ = posPath P σ := by
  simp [posPath, transpose_add, transpose_smul, transpose_sub, hP]

lemma smoothEntries_posPath (P : Sq n) : SmoothEntries (posPath P) := by
  have hs : ContDiff ℝ ∞ (fun σ : ℝ => Real.sin (Real.pi * σ / 2) ^ 2) :=
    (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const _)).pow 2
  exact (SmoothEntries.const 1).add (SmoothEntries.smul hs (SmoothEntries.const _))

end SymplecticPacking.General.Ham.Linear
