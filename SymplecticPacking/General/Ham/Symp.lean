import SymplecticPacking.General.Interface

/-!
# Linear symplectic algebra of `(ℝ^{2n}, ω₀)` used by the Hamiltonian end

`ω₀` as a continuous bilinear map, its value on coordinate vectors, nondegeneracy (so symplectic
linear maps are injective, hence isomorphisms), and the identification of the Hamiltonian vector
field from `ι_X ω₀ = dH` (`hamVF_eq_of_hasFDerivAt`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter ContinuousLinearMap Problem
open scoped ContDiff Topology

variable {n : ℕ}

/-! ### `ω₀` as a continuous bilinear map -/

lemma omega0_add_left (x x' y : E n) :
    Problem.omega0 (x + x') y = Problem.omega0 x y + Problem.omega0 x' y := by
  simp only [Problem.omega0, PiLp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma omega0_smul_left (c : ℝ) (x y : E n) :
    Problem.omega0 (c • x) y = c * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma omega0_add_right (x y y' : E n) :
    Problem.omega0 x (y + y') = Problem.omega0 x y + Problem.omega0 x y' := by
  simp only [Problem.omega0, PiLp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma omega0_smul_right (c : ℝ) (x y : E n) :
    Problem.omega0 x (c • y) = c * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma omega0_skew (x y : E n) : Problem.omega0 x y = -Problem.omega0 y x := by
  simp only [Problem.omega0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

@[simp] lemma omega0_zero_left (y : E n) : Problem.omega0 0 y = 0 := by
  simp [Problem.omega0]

@[simp] lemma omega0_zero_right (x : E n) : Problem.omega0 x 0 = 0 := by
  simp [Problem.omega0]

/-- `ω₀` as a linear map into linear forms. -/
def omega0ₗ : E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ Problem.omega0 omega0_add_left omega0_smul_left omega0_add_right
    omega0_smul_right

/-- `ω₀` as a continuous bilinear map. -/
def omega0L : E n →L[ℝ] E n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E n →L[ℝ] ℝ)).toLinearMap.comp
      omega0ₗ)

@[simp] lemma omega0L_apply (x y : E n) : omega0L x y = Problem.omega0 x y := rfl

/-! ### Coordinate vectors -/

/-- `ω₀(X, e_m) = -X_{m+n}` for a `q`-index `m < n` and `X_{m-n}` for a `p`-index. -/
lemma omega0_single (X : E n) (m : Fin (2 * n)) :
    Problem.omega0 X (EuclideanSpace.single m 1) =
      if h : (m : ℕ) < n then -X ⟨m + n, by omega⟩
      else X ⟨m - n, by have := m.isLt; omega⟩ := by
  simp only [Problem.omega0, EuclideanSpace.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · have h1 : pIdx (⟨m, h⟩ : Fin n) ≠ m := by
        intro e; have := congrArg Fin.val e; simp [pIdx] at this; omega
      have h2 : qIdx (⟨m, h⟩ : Fin n) = m := Fin.ext rfl
      have h3 : pIdx (⟨m, h⟩ : Fin n) = ⟨m + n, by omega⟩ := Fin.ext (by simp [pIdx]; omega)
      simp only [h1, h2, h3, if_true, if_false, mul_zero, zero_sub, mul_one]
      have h4 : (⟨m + n, by omega⟩ : Fin (2 * n)) ≠ m := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      simp [h4]
    · intro b _ hb
      have h1 : pIdx b ≠ m := by
        intro e; have := congrArg Fin.val e; simp [pIdx] at this; omega
      have h2 : qIdx b ≠ m := by
        intro e; apply hb; ext; have := congrArg Fin.val e; simp [qIdx] at this; simp; omega
      simp [h1, h2]
    · simp
  · have hm := m.isLt
    rw [Finset.sum_eq_single (⟨m - n, by omega⟩ : Fin n)]
    · have h1 : pIdx (⟨m - n, by omega⟩ : Fin n) = m := Fin.ext (by simp [pIdx]; omega)
      have h2 : qIdx (⟨m - n, by omega⟩ : Fin n) ≠ m := by
        intro e; have := congrArg Fin.val e; simp [qIdx] at this; omega
      have h3 : qIdx (⟨m - n, by omega⟩ : Fin n) = ⟨m - n, by omega⟩ := Fin.ext rfl
      simp only [h1, h2, h3, if_true, if_false, mul_zero, sub_zero, mul_one]
      have h4 : (⟨m - n, by omega⟩ : Fin (2 * n)) ≠ m := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      simp [h4]
    · intro b _ hb
      have h1 : pIdx b ≠ m := by
        intro e; apply hb; ext; have := congrArg Fin.val e; simp [pIdx] at this; simp; omega
      have h2 : qIdx b ≠ m := by
        intro e; have := congrArg Fin.val e; simp [qIdx] at this; omega
      simp [h1, h2]
    · simp

/-- Nondegeneracy of `ω₀`. -/
theorem omega0_nondegenerate {X : E n} (h : ∀ w, Problem.omega0 X w = 0) : X = 0 := by
  ext m
  by_cases hm : (m : ℕ) < n
  · -- `m` is a `q`-index: pair with `e_{m+n}`, a `p`-index
    have := h (EuclideanSpace.single ⟨m + n, by omega⟩ 1)
    rw [omega0_single] at this
    simp only [show ¬ ((m : ℕ) + n < n) by omega, dite_false] at this
    have e : (⟨(m : ℕ) + n - n, by omega⟩ : Fin (2 * n)) = m := Fin.ext (by simp)
    rw [e] at this; simpa using this
  · have := h (EuclideanSpace.single ⟨m - n, by omega⟩ 1)
    rw [omega0_single] at this
    simp only [show ((m : ℕ) - n < n) by have := m.isLt; omega, dite_true] at this
    have e : (⟨(m : ℕ) - n + n, by have := m.isLt; omega⟩ : Fin (2 * n)) = m :=
      Fin.ext (by simp; omega)
    rw [e] at this; simpa using this

/-! ### Symplectic linear maps -/

lemma isSymplecticLinear_id : IsSymplecticLinear (ContinuousLinearMap.id ℝ (E n)) :=
  fun _ _ => rfl

/-- A symplectic linear map is injective. -/
lemma IsSymplecticLinear.injective {A : E n →L[ℝ] E n} (hA : IsSymplecticLinear A) :
    Function.Injective A := by
  intro v w hvw
  have hz : A (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  rw [← sub_eq_zero]
  apply omega0_nondegenerate
  intro x
  rw [← hA (v - w) x, hz, omega0_zero_left]

/-- The equivalence defined by a symplectic linear map. -/
def symplEquiv {A : E n →L[ℝ] E n} (hA : IsSymplecticLinear A) : E n ≃L[ℝ] E n :=
  (LinearEquiv.ofInjectiveEndo (A : E n →ₗ[ℝ] E n)
    (IsSymplecticLinear.injective hA)).toContinuousLinearEquiv

@[simp] lemma symplEquiv_coe {A : E n →L[ℝ] E n} (hA : IsSymplecticLinear A) :
    ((symplEquiv hA : E n →L[ℝ] E n)) = A := by ext v; rfl

/-! ### The Hamiltonian vector field -/

/-- `ι_X ω₀ = dH` determines `X`: if `D(H t)(y) w = ω₀(X, w)` for all `w`, then
`X_H(t,y) = X`. -/
theorem hamVF_eq_of_hasFDerivAt {H : ℝ → E n → ℝ} {t : ℝ} {y X : E n} {L : E n →L[ℝ] ℝ}
    (hL : HasFDerivAt (H t) L y) (hX : ∀ w, L w = Problem.omega0 X w) :
    Problem.hamVF H t y = X := by
  have hp : ∀ m, Problem.partialDeriv (H t) m y =
      Problem.omega0 X (EuclideanSpace.single m 1) := by
    intro m; rw [Problem.partialDeriv, hL.fderiv, hX]
  refine PiLp.ext fun m => ?_
  simp only [Problem.hamVF, hp, omega0_single, PiLp.toLp_apply]
  split_ifs with h1 h2 h3
  · omega
  · first
      | exact congrArg (fun j => X j) (Fin.ext (by simp <;> omega))
      | exact (congrArg (fun j => X j) (Fin.ext (by simp <;> omega))).symm
  · simp only [neg_neg]
    first
      | exact congrArg (fun j => X j) (Fin.ext (by simp <;> omega))
      | exact (congrArg (fun j => X j) (Fin.ext (by simp <;> omega))).symm
  · omega

/-- If `D(H t)(y) = 0` then `X_H(t,y) = 0`. -/
theorem hamVF_eq_zero_of_fderiv {H : ℝ → E n → ℝ} {t : ℝ} {y : E n}
    (hd : fderiv ℝ (H t) y = 0) : Problem.hamVF H t y = 0 := by
  refine PiLp.ext fun m => ?_
  simp [Problem.hamVF, Problem.partialDeriv, hd]

end SymplecticPacking.General.Ham
