import SymplecticPacking.General.Ham.Linear.Blocks
import SymplecticPacking.General.Ham.Symp

/-!
# Block matrices as linear maps of `ℝ^{2n}`

`toCLM : Mat n → (E n →L E n)` (block index `inl j` ↔ coordinate `q_j`, `inr j` ↔ `p_j`);
`N ∈ Sp(2n) → toCLM N` is symplectic; `ofCLM A ∈ Sp(2n)` for symplectic `A` and
`toCLM (ofCLM A) = A`; joint smoothness of `(σ, u) ↦ toCLM (N σ) u` for smooth entries.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix WithLp Problem
open scoped ContDiff

variable {n : ℕ}

/-- Block indices ↔ coordinates: `inl j ↦ q_j = j`, `inr j ↦ p_j = n + j`. -/
def ei (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) := finSumFinEquiv.trans (finCongr (two_mul n).symm)

@[simp] lemma ei_inl (j : Fin n) : ei n (Sum.inl j) = qIdx j := Fin.ext (by simp [ei, qIdx])
@[simp] lemma ei_inr (j : Fin n) : ei n (Sum.inr j) = pIdx j :=
  Fin.ext (by simp [ei, pIdx]; omega)

/-- The linear map of a block matrix. -/
def toCLM (N : Mat n) : E n →L[ℝ] E n :=
  Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ) (N.submatrix (ei n).symm (ei n).symm)

/-- The block matrix of a linear map. -/
def ofCLM (A : E n →L[ℝ] E n) : Mat n :=
  ((Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ)).symm A).submatrix (ei n) (ei n)

lemma toCLM_ofCLM (A : E n →L[ℝ] E n) : toCLM (ofCLM A) = A := by
  simp [toCLM, ofCLM, submatrix_submatrix]

lemma toCLM_one : toCLM (1 : Mat n) = ContinuousLinearMap.id ℝ (E n) := by
  rw [toCLM, submatrix_one_equiv, map_one]; rfl

/-- Reindexed coordinate vector. -/
def blk (x : E n) : Fin n ⊕ Fin n → ℝ := fun k => x (ei n k)

lemma blk_toCLM (N : Mat n) (x : E n) : blk (toCLM N x) = N *ᵥ blk x := by
  funext k
  simp only [blk, toCLM, ofLp_toEuclideanCLM, mulVec, dotProduct, submatrix_apply,
    Equiv.symm_apply_apply]
  exact (Fintype.sum_equiv (ei n).symm _ _ (fun j => by simp)).trans rfl

/-- `ω₀(x, y) = - X · (J Y)` in block coordinates. -/
lemma omega0_eq (x y : E n) :
    Problem.omega0 x y = -(blk x ⬝ᵥ (Jm n *ᵥ blk y)) := by
  simp only [Problem.omega0, blk, Jm, J, dotProduct, mulVec, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, ei_inl, ei_inr]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, add_zero, neg_mul, ite_mul, one_mul,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_neg]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The block matrix of the form preserved by `toCLM N` is `Nᵀ J N`. -/
lemma omega0_toCLM (N : Mat n) (x y : E n) :
    Problem.omega0 (toCLM N x) (toCLM N y) = -(blk x ⬝ᵥ ((Nᵀ * Jm n * N) *ᵥ blk y)) := by
  rw [omega0_eq, blk_toCLM, blk_toCLM, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec (blk x) Nᵀ, vecMul_transpose]

/-- Symplectic block matrices give symplectic linear maps. -/
theorem toCLM_isSymplectic {N : Mat n} (hN : N ∈ Sp n) : IsSymplecticLinear (toCLM N) := by
  intro x y
  rw [omega0_toCLM, (SymplecticGroup.mem_iff'.mp hN), ← omega0_eq]

lemma blk_single (k : Fin n ⊕ Fin n) :
    blk (EuclideanSpace.single (ei n k) (1 : ℝ)) = Pi.single k 1 := by
  funext l; simp [blk, PiLp.single_apply, Pi.single_apply, (ei n).injective.eq_iff, eq_comm]

/-- The matrix of a symplectic linear map is symplectic. -/
theorem ofCLM_mem {A : E n →L[ℝ] E n} (hA : IsSymplecticLinear A) : ofCLM A ∈ Sp n := by
  rw [SymplecticGroup.mem_iff']
  ext k l
  have h := omega0_toCLM (ofCLM A) (EuclideanSpace.single (ei n k) 1)
    (EuclideanSpace.single (ei n l) 1)
  rw [toCLM_ofCLM, hA, omega0_eq, blk_single, blk_single] at h
  simp only [single_one_dotProduct, mulVec_single, MulOpposite.op_one, one_smul, neg_inj] at h
  simpa using h.symm

/-- Joint smoothness of `(σ, u) ↦ toCLM (N σ) u`. -/
theorem contDiff_toCLM_apply {N : ℝ → Mat n} (hN : SmoothEntries N) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => toCLM (N p.1) p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × E n =>
      (N p.1 |>.submatrix (ei n).symm (ei n).symm) *ᵥ ofLp p.2) := by
    rw [contDiff_pi]
    intro i
    simp only [mulVec, dotProduct, submatrix_apply]
    refine ContDiff.sum fun j _ => ((hN _ _).comp contDiff_fst).mul ?_
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * n) => ℝ) j).contDiff).comp contDiff_snd
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2 * n) => ℝ)).symm.contDiff.comp hc
  convert h using 1
  funext p
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2 * n) => ℝ)).injective
  simp only [toCLM, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  ext i
  simp [ofLp_toEuclideanCLM]

end SymplecticPacking.General.Ham.Linear
