import verification.Problem

/-!
# Interface between the geometric stage and the Hamiltonian end

The geometric stage of every branch produces explicit *enlarged-source* symplectic embeddings
`f_i` of the balls `B(c_i)` (centred at the origin) into the open target `B°(C)`:
`f_i` is smooth and symplectic on an open ball `B°(a_i)` and injective with pairwise disjoint
images on a closed ball `B(c'_i)`, where `c_i < c'_i < a_i`. The Hamiltonian end
(`SymplecticPacking/HamEnd/End.lean`) turns such embeddings, together with pairwise disjoint
source balls `s_i + B(c_i)`, into an explicit Hamiltonian with `PackingSpec`.

Coordinates: see `verification/Problem.lean`. Under `z_j = q_j + i p_j`
(`toPhase`), `ω₀` is the OpenAI library's `standardForm` and `π ‖y‖²` its `capacity`.
-/

noncomputable section

namespace SymplecticPacking.General

open Metric Set Problem
open scoped ContDiff

/-- A linear map `A : ℝ^{2n} → ℝ^{2n}` is symplectic if `ω₀(Ax, Ay) = ω₀(x, y)`. -/
def IsSymplecticLinear {n : ℕ} (A : E n →L[ℝ] E n) : Prop :=
  ∀ x y, Problem.omega0 (A x) (A y) = Problem.omega0 x y

/-- The complex coordinates `z_j = q_j + i p_j` of a point of `ℝ^{2n}` (the phase space
`Fin n → ℂ` of the OpenAI library). -/
def toPhase {n : ℕ} (y : E n) : Fin n → ℂ := fun j => ⟨y (qIdx j), y (pIdx j)⟩

/-- Data of the geometric stage: maps `f i : ℝ^{2n} → ℝ^{2n}` (sources centred at the origin),
enlarged closed-source capacities `c'_i` and open-domain capacities `a_i`. -/
structure EmbeddingData (n k : ℕ) where
  f : Fin k → E n → E n
  enlarged : Fin k → ℝ
  domain : Fin k → ℝ

/-- Specification of the geometric stage for the input `(n, k, C, c)`:
`c_i < c'_i < a_i`; `f_i` smooth and symplectic on `B°(a_i)`; injective on `B(c'_i)`; the images
`f_i(B(c'_i))` pairwise disjoint and contained in the open target `B°(C)`. -/
structure EmbeddingSpec (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (D : EmbeddingData n k) : Prop where
  lt_enlarged : ∀ i, c i < D.enlarged i
  enlarged_lt_domain : ∀ i, D.enlarged i < D.domain i
  smooth : ∀ i, ContDiffOn ℝ ∞ (D.f i) (capBallOpen 0 (D.domain i))
  sympl : ∀ i, ∀ u ∈ capBallOpen (0 : E n) (D.domain i), IsSymplecticLinear (fderiv ℝ (D.f i) u)
  inj : ∀ i, InjOn (D.f i) (capBall 0 (D.enlarged i))
  disj : ∀ i j, i ≠ j →
    Disjoint (D.f i '' capBall 0 (D.enlarged i)) (D.f j '' capBall 0 (D.enlarged j))
  into : ∀ i, D.f i '' capBall 0 (D.enlarged i) ⊆ capBallOpen 0 C

end SymplecticPacking.General
