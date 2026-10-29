import Mathlib

/-!
# The common tail

The common tail `F_v(u) = f(v u) / v`.

For every common `v > 0` the tails of a family of maps with disjoint images are disjoint,
because their images are the images of the *same* dilation `1/v` applied to the disjoint
sets `f_i(v S)`. No star-shapedness is needed. The spatial derivative is `Df(v u)`, so the
tail of a symplectic map is symplectic, and the `v`-derivative is formula (21).
-/

noncomputable section

namespace SymplecticPacking

open Set Metric
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tail `F_v(u) = v⁻¹ • f (v • u)` (formula (20)). -/
def tail (f : E → E) (v : ℝ) (u : E) : E := v⁻¹ • f (v • u)

@[simp] lemma tail_one (f : E → E) : tail f 1 = f := by
  funext u; simp [tail]

/-- Image of a set under the tail: `F_v(S) = v⁻¹ • f(v • S)`. -/
lemma tail_image (f : E → E) (v : ℝ) (S : Set E) :
    tail f v '' S = v⁻¹ • (f '' (v • S)) := by
  ext y
  simp only [mem_image, mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f (v • u), ⟨v • u, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

/-- `v • B̄(0,r) ⊆ B̄(0,r)` for `0 ≤ v ≤ 1`. -/
lemma smul_closedBall_subset {r v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    v • closedBall (0 : E) r ⊆ closedBall (0 : E) r := by
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_closedBall_zero_iff] at hu ⊢
  rw [norm_smul, Real.norm_of_nonneg hv0]
  calc v * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
    _ ≤ r := by rw [one_mul]; exact hu

/-- The tail of a map injective on `T` is injective on any `S` with `v • S ⊆ T`. -/
theorem tail_injOn (f : E → E) {S T : Set E} {v : ℝ} (hv : v ≠ 0) (hST : v • S ⊆ T)
    (hf : InjOn f T) : InjOn (tail f v) S := by
  intro x hx y hy hxy
  have hx' : v • x ∈ T := hST (smul_mem_smul_set hx)
  have hy' : v • y ∈ T := hST (smul_mem_smul_set hy)
  have : f (v • x) = f (v • y) := by
    have := congrArg (fun z => v • z) hxy
    simpa [tail, smul_smul, mul_inv_cancel₀ hv] using this
  have := hf hx' hy' this
  exact smul_right_injective E hv this

/-- **Spatial derivative of the tail**: `D_u F_v(u) = Df(v u)` (so tails of symplectic maps are
symplectic). -/
theorem hasFDerivAt_tail {f : E → E} {f' : E →L[ℝ] E} {v : ℝ} (hv : v ≠ 0) {u : E}
    (hf : HasFDerivAt f f' (v • u)) : HasFDerivAt (tail f v) f' u := by
  have h1 : HasFDerivAt (fun x : E => v • x) (v • ContinuousLinearMap.id ℝ E) u :=
    (hasFDerivAt_id u).const_smul v
  have h2 := (hf.comp u h1).const_smul v⁻¹
  have heq : v⁻¹ • (f'.comp (v • ContinuousLinearMap.id ℝ E)) = f' := by
    ext x; simp [smul_smul, inv_mul_cancel₀ hv]
  rw [heq] at h2
  exact h2

/-- **Formula (21)**: `∂_v F_v(u) = [v Df(vu) u - f(vu)] / v²`. -/
theorem hasDerivAt_tail_param {f : E → E} {f' : E →L[ℝ] E} {v : ℝ} (hv : v ≠ 0) {u : E}
    (hf : HasFDerivAt f f' (v • u)) :
    HasDerivAt (fun w => tail f w u) ((v ^ 2)⁻¹ • (v • f' u - f (v • u))) v := by
  -- `w ↦ w • u` has derivative `u`
  have h1 : HasDerivAt (fun w : ℝ => w • u) u v := by
    simpa using (hasDerivAt_id v).smul_const u
  have h2 : HasDerivAt (fun w : ℝ => f (w • u)) (f' u) v := hf.comp_hasDerivAt v h1
  have h3 : HasDerivAt (fun w : ℝ => w⁻¹) (-(v ^ 2)⁻¹) v := hasDerivAt_inv hv
  have h4 := h3.smul h2
  refine h4.congr_deriv ?_
  have hv' : (v ^ 2)⁻¹ * v = v⁻¹ := by field_simp
  rw [smul_sub, smul_smul, hv', neg_smul]
  abel

end SymplecticPacking
