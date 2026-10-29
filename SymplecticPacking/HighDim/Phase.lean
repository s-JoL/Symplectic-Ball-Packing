import verification.Problem
import OAI.Geometry.BallPacking.Models.BallVolume

/-!
# Phase-space bridge: `ℝ^{2n}` (`Problem.E n`) and the OpenAI library's `ℂⁿ` (`Ambient n`)

`phaseEquiv n : E n ≃L[ℝ] Ambient n` is `y ↦ (q_j + i p_j)_j`. It carries `π‖y‖²` to the
library's `capacity`, `ω₀` to `standardForm`, and capacity balls to capacity balls.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Problem
open OAI.PackingSufficiencySupport (Ambient capacity standardForm)

/-- The linear equivalence `y ↦ (q_j + i p_j)_j`. -/
def phaseLinearEquiv (n : ℕ) : E n ≃ₗ[ℝ] Ambient n where
  toFun y := fun j => ⟨y (qIdx j), y (pIdx j)⟩
  invFun z := WithLp.toLp 2 fun i : Fin (2 * n) =>
    if h : (i : ℕ) < n then (z ⟨i, h⟩).re
    else (z ⟨i - n, by have := i.isLt; omega⟩).im
  left_inv y := by
    ext i
    by_cases h : (i : ℕ) < n
    · simp only [h, dite_true]
      rfl
    · simp only [h, dite_false]
      show y (pIdx _) = y i
      exact congrArg y (Fin.ext (by simp only [pIdx]; omega))
  right_inv z := by
    funext j
    apply Complex.ext
    · show (if h : ((qIdx j : Fin (2 * n)) : ℕ) < n then (z ⟨_, h⟩).re else _) = (z j).re
      simp [qIdx]
    · show (if h : ((pIdx j : Fin (2 * n)) : ℕ) < n then _ else (z ⟨(pIdx j : ℕ) - n, _⟩).im)
        = (z j).im
      have h1 : ¬ ((pIdx j : Fin (2 * n)) : ℕ) < n := by simp [pIdx]
      rw [dif_neg h1]
      exact congrArg (fun j => (z j).im) (Fin.ext (by simp [pIdx]))
  map_add' x y := by
    funext j
    apply Complex.ext <;> simp
  map_smul' r x := by
    funext j
    apply Complex.ext <;> simp

/-- The continuous linear equivalence `ℝ^{2n} ≃ ℂⁿ`, `y ↦ (q_j + i p_j)_j`. -/
def phaseEquiv (n : ℕ) : E n ≃L[ℝ] Ambient n :=
  (phaseLinearEquiv n).toContinuousLinearEquiv

@[simp] theorem phaseEquiv_apply_re {n : ℕ} (y : E n) (j : Fin n) :
    (phaseEquiv n y j).re = y (qIdx j) := rfl

@[simp] theorem phaseEquiv_apply_im {n : ℕ} (y : E n) (j : Fin n) :
    (phaseEquiv n y j).im = y (pIdx j) := rfl

/-- `ω₀` corresponds to the library's `standardForm`. -/
theorem standardForm_phaseEquiv {n : ℕ} (x y : E n) :
    standardForm (phaseEquiv n x) (phaseEquiv n y) = omega0 x y := by
  simp [standardForm, omega0]

/-- `Σ_i y_i² = Σ_j (q_j² + p_j²)`. -/
theorem sum_sq_split {n : ℕ} (y : E n) :
    ∑ i : Fin (2 * n), y i ^ 2 = ∑ j : Fin n, (y (qIdx j) ^ 2 + y (pIdx j) ^ 2) := by
  rw [Finset.sum_add_distrib]
  rw [← ((finCongr (two_mul n)).trans finSumFinEquiv.symm).symm.sum_comp,
    Fintype.sum_sum_type]
  congr 1

/-- The library's capacity of `(q_j + i p_j)_j` is `π ‖y‖²`. -/
theorem capacity_phaseEquiv {n : ℕ} (y : E n) :
    capacity (phaseEquiv n y) = Real.pi * ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), capacity]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs, sum_sq_split, Complex.normSq_apply,
    phaseEquiv_apply_re, phaseEquiv_apply_im]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phaseEquiv_mem_closedBall {n : ℕ} {y : E n} {c : ℝ} :
    phaseEquiv n y ∈ OAI.PackingSufficiencySupport.closedBall n c ↔ y ∈ capBall 0 c := by
  simp [OAI.PackingSufficiencySupport.closedBall, capBall, capacity_phaseEquiv]

theorem phaseEquiv_mem_openBall {n : ℕ} {y : E n} {c : ℝ} :
    phaseEquiv n y ∈ OAI.PackingSufficiencySupport.openBall n c ↔ y ∈ capBallOpen 0 c := by
  simp [OAI.PackingSufficiencySupport.openBall, capBallOpen, capacity_phaseEquiv]

theorem phaseEquiv_symm_mem_openBall {n : ℕ} {z : Ambient n} {c : ℝ} :
    (phaseEquiv n).symm z ∈ capBallOpen 0 c ↔ z ∈ OAI.PackingSufficiencySupport.openBall n c := by
  rw [← phaseEquiv_mem_openBall, ContinuousLinearEquiv.apply_symm_apply]

end SymplecticPacking.HighDim
