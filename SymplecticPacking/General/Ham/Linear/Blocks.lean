import Mathlib

/-!
# Block matrices in `Sp(2n, ℝ)`

`Mat n = Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ` with Mathlib's `J = [[0,-1],[1,0]]` and
`Sp n = symplecticGroup (Fin n) ℝ`; the block criterion, the shears `Up S = [[1,S],[0,1]]`, the
diagonal blocks `Dg a e = [[a,0],[0,e]]`, and smoothness of matrix-valued paths
(`SmoothEntries`, closed under products, sums, block assembly and inversion); `sec:iso-linear`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix
open scoped ContDiff

variable {n : ℕ}

/-- `n × n` real matrices. -/
abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
/-- `2n × 2n` real matrices in `(q, p)` block form. -/
abbrev Mat (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ
/-- The symplectic group `Sp(2n, ℝ)` (Mathlib convention `Aᵀ J A = J`). -/
abbrev Sp (n : ℕ) := symplecticGroup (Fin n) ℝ
/-- Mathlib's `J = [[0,-1],[1,0]]`, i.e. multiplication by `i` under `z = q + i p`. -/
abbrev Jm (n : ℕ) : Mat n := J (Fin n) ℝ

/-- **Block criterion** for `Sp(2n)`, with the transposed relation added. -/
theorem mem_Sp_fromBlocks {a b c d : Sq n} :
    fromBlocks a b c d ∈ Sp n ↔
      cᵀ * a = aᵀ * c ∧ aᵀ * d - cᵀ * b = 1 ∧ dᵀ * a - bᵀ * c = 1 ∧ dᵀ * b = bᵀ * d := by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1.symm, h3, ?_, h2.symm⟩
    have := congrArg Matrix.transpose h3
    simpa [Matrix.transpose_sub, Matrix.transpose_mul] using this
  · rintro ⟨h1, h2, -, h4⟩
    exact ⟨h1.symm, h4.symm, h2⟩

/-- `Up S = [[1, S], [0, 1]]`. -/
def Up (S : Sq n) : Mat n := fromBlocks 1 S 0 1
/-- `Dg a e = [[a, 0], [0, e]]`; symplectic iff `aᵀ e = 1`. -/
def Dg (a e : Sq n) : Mat n := fromBlocks a 0 0 e

theorem Up_mem {S : Sq n} (hS : Sᵀ = S) : Up S ∈ Sp n := by
  rw [Up, mem_Sp_fromBlocks]
  simp [hS]

theorem Dg_mem {a e : Sq n} (h : aᵀ * e = 1) : Dg a e ∈ Sp n := by
  rw [Dg, mem_Sp_fromBlocks]
  have h' : eᵀ * a = 1 := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this
  simp [h, h']

lemma Up_zero : Up (0 : Sq n) = 1 := by simp [Up, fromBlocks_one]
lemma Dg_one : Dg (1 : Sq n) 1 = 1 := by simp [Dg, fromBlocks_one]

lemma Dg_mul_Up (a e S : Sq n) : Dg a e * Up S = fromBlocks a (a * S) 0 e := by
  simp [Dg, Up, fromBlocks_multiply]

/-! ### Smooth matrix paths -/

/-- All entries are smooth functions of the parameter. -/
def SmoothEntries {ι κ : Type*} (N : ℝ → Matrix ι κ ℝ) : Prop :=
  ∀ i j, ContDiff ℝ ∞ (fun σ => N σ i j)

namespace SmoothEntries

variable {ι κ μ : Type*}

lemma const (N : Matrix ι κ ℝ) : SmoothEntries fun _ : ℝ => N := fun _ _ => contDiff_const

lemma mul [Fintype κ] {N : ℝ → Matrix ι κ ℝ} {N' : ℝ → Matrix κ μ ℝ} (h : SmoothEntries N)
    (h' : SmoothEntries N') : SmoothEntries fun σ => N σ * N' σ := by
  intro i j
  simp only [mul_apply]
  exact ContDiff.sum fun k _ => (h i k).mul (h' k j)

lemma smul {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {N : ℝ → Matrix ι κ ℝ} (h : SmoothEntries N) :
    SmoothEntries fun σ => f σ • N σ := fun i j => by simpa using hf.mul (h i j)

lemma add {N N' : ℝ → Matrix ι κ ℝ} (h : SmoothEntries N) (h' : SmoothEntries N') :
    SmoothEntries fun σ => N σ + N' σ := fun i j => by simpa using (h i j).add (h' i j)

lemma sub {N N' : ℝ → Matrix ι κ ℝ} (h : SmoothEntries N) (h' : SmoothEntries N') :
    SmoothEntries fun σ => N σ - N' σ := fun i j => by simpa using (h i j).sub (h' i j)

lemma fromBlocks' {a b c d : ℝ → Sq n} (ha : SmoothEntries a) (hb : SmoothEntries b)
    (hc : SmoothEntries c) (hd : SmoothEntries d) :
    SmoothEntries fun σ => fromBlocks (a σ) (b σ) (c σ) (d σ) := by
  rintro (i | i) (j | j)
  · exact ha i j
  · exact hb i j
  · exact hc i j
  · exact hd i j

/-- The determinant of a smooth path is smooth. -/
lemma det [Fintype ι] [DecidableEq ι] {N : ℝ → Matrix ι ι ℝ} (h : SmoothEntries N) :
    ContDiff ℝ ∞ (fun σ => (N σ).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun p _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => h _ _

/-- The inverse of a smooth path of invertible matrices is smooth. -/
lemma inv [Fintype ι] [DecidableEq ι] {N : ℝ → Matrix ι ι ℝ} (h : SmoothEntries N)
    (hdet : ∀ σ, (N σ).det ≠ 0) : SmoothEntries fun σ => (N σ)⁻¹ := by
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  have hd : ContDiff ℝ ∞ (fun σ => Ring.inverse (N σ).det) := by
    have : (fun σ => Ring.inverse (N σ).det) = fun σ => ((N σ).det)⁻¹ := by
      funext σ; rw [Ring.inverse_eq_inv']
    rw [this]; exact (SmoothEntries.det h).inv hdet
  refine hd.mul ?_
  simp only [Matrix.adjugate_apply]
  refine SmoothEntries.det (N := fun σ => (N σ).updateRow j (Pi.single i 1)) (fun k l => ?_)
  simp only [Matrix.updateRow_apply]
  by_cases hk : k = j
  · simp only [hk, ite_true]; exact contDiff_const
  · simp only [hk, ite_false]; exact h k l

end SmoothEntries

end SymplecticPacking.General.Ham.Linear
