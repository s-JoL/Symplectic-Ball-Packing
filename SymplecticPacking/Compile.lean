import Mathlib

/-!
# Error bounds of the finite compilation

* `bernstein_tensor_value_error` — (29): the tensor Bernstein operator in `d` variables
  approximates an `L¹`-Lipschitz function (constant `M`) within `d · M / (2 √n)`.
* `flow_error_le` — (32): Grönwall for two Hamiltonian-type fields that are uniformly
  `η`-close, one of them `L`-Lipschitz.
* `eta_choice` — with `η = b · e^{-L} / 2` the final displacement is `< b`.
* `cutoff_gradient_error` — the identity `∇(βP) - ∇H = β∇(P-H) + (P-H)∇β` (using `βH = H`)
  and its norm bound `< 2δ(1 + C_β)`.

The derivative bound (30) is in `General/CompileBernstein.lean`.
-/

noncomputable section

namespace SymplecticPacking

open Finset Real Set
open scoped unitInterval

/-! ### One-variable mean absolute deviation -/

/-- `∑ₖ b_{n,k}(x) |x - k/n| ≤ √(x(1-x)/n)` (Cauchy–Schwarz against the variance identity). -/
lemma bernstein_mean_abs_dev {n : ℕ} (hn : n ≠ 0) (x : I) :
    ∑ k : Fin (n + 1), bernstein n k x * |(x : ℝ) - (k : ℝ) / n| ≤
      Real.sqrt ((x : ℝ) * (1 - x) / n) := by
  have hvar := bernstein.variance hn x
  have hprob := bernstein.probability n x
  set S := ∑ k : Fin (n + 1), bernstein n k x * |(x : ℝ) - (k : ℝ) / n|
  have hS0 : 0 ≤ S := sum_nonneg fun k _ => mul_nonneg bernstein_nonneg (abs_nonneg _)
  apply Real.le_sqrt_of_sq_le
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin (n + 1)))
    (fun k => Real.sqrt (bernstein n k x))
    (fun k => Real.sqrt (bernstein n k x) * |(x : ℝ) - (k : ℝ) / n|)
  have e1 : ∀ k : Fin (n + 1), Real.sqrt (bernstein n k x) *
      (Real.sqrt (bernstein n k x) * |(x : ℝ) - (k : ℝ) / n|) =
        bernstein n k x * |(x : ℝ) - (k : ℝ) / n| := by
    intro k
    rw [← mul_assoc, Real.mul_self_sqrt bernstein_nonneg]
  have e2 : ∀ k : Fin (n + 1), Real.sqrt (bernstein n k x) ^ 2 = bernstein n k x :=
    fun k => Real.sq_sqrt bernstein_nonneg
  have e3 : ∀ k : Fin (n + 1),
      (Real.sqrt (bernstein n k x) * |(x : ℝ) - (k : ℝ) / n|) ^ 2 =
        ((x : ℝ) - (k : ℝ) / n) ^ 2 * bernstein n k x := by
    intro k; rw [mul_pow, e2, sq_abs, mul_comm]
  simp only [e1, e2, e3] at hcs
  have hz : ∀ k : Fin (n + 1), ((bernstein.z k : I) : ℝ) = (k : ℝ) / n := fun k => rfl
  simp only [hz] at hvar
  rw [hprob, hvar, one_mul] at hcs
  exact hcs

lemma sqrt_var_le {n : ℕ} (hn : n ≠ 0) (x : I) :
    Real.sqrt ((x : ℝ) * (1 - x) / n) ≤ 1 / (2 * Real.sqrt n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hx : (x : ℝ) * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]
  have h1 : (x : ℝ) * (1 - x) / n ≤ 1 / (4 * n) := by
    rw [div_le_div_iff₀ hn' (by positivity)]; nlinarith
  calc Real.sqrt ((x : ℝ) * (1 - x) / n) ≤ Real.sqrt (1 / (4 * n)) := Real.sqrt_le_sqrt h1
    _ = 1 / (2 * Real.sqrt n) := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by norm_num),
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-! ### Tensor Bernstein operator -/

variable {d : ℕ}

/-- Tensor Bernstein weight `∏ₗ b_{n, jₗ}(xₗ)`. -/
def tensorWeight (n : ℕ) (x : Fin d → I) (j : Fin d → Fin (n + 1)) : ℝ :=
  ∏ l, bernstein n (j l) (x l)

/-- Grid point `j / n` in the cube. -/
def gridPt (n : ℕ) (j : Fin d → Fin (n + 1)) : Fin d → ℝ := fun l => (j l : ℝ) / n

/-- Tensor Bernstein operator `B_n f(x) = ∑ⱼ f(j/n) ∏ₗ b_{n,jₗ}(xₗ)`. -/
def tensorBernstein (n : ℕ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → I) : ℝ :=
  ∑ j : Fin d → Fin (n + 1), f (gridPt n j) * tensorWeight n x j

lemma tensorWeight_nonneg (n : ℕ) (x : Fin d → I) (j : Fin d → Fin (n + 1)) :
    0 ≤ tensorWeight n x j := prod_nonneg fun _ _ => bernstein_nonneg

/-- Product sums factor: `∑ⱼ ∏ₗ c l (j l) = ∏ₗ ∑ₐ c l a`. -/
lemma sum_prod_eq {n : ℕ} (c : Fin d → Fin (n + 1) → ℝ) :
    ∑ j : Fin d → Fin (n + 1), ∏ l, c l (j l) = ∏ l, ∑ a, c l a := by
  rw [Finset.prod_univ_sum]; simp

lemma sum_tensorWeight (n : ℕ) (x : Fin d → I) :
    ∑ j : Fin d → Fin (n + 1), tensorWeight n x j = 1 := by
  unfold tensorWeight
  rw [sum_prod_eq (fun l a => bernstein n a (x l))]
  exact prod_eq_one fun l _ => bernstein.probability n (x l)

/-- Marginal: `∑ⱼ (∏ₗ b_{jₗ}(xₗ)) g(j m) = ∑ₐ b_a(x_m) g(a)`. -/
lemma sum_tensorWeight_mul_marginal (n : ℕ) (x : Fin d → I) (m : Fin d)
    (g : Fin (n + 1) → ℝ) :
    ∑ j : Fin d → Fin (n + 1), tensorWeight n x j * g (j m) =
      ∑ a : Fin (n + 1), bernstein n a (x m) * g a := by
  let c : Fin d → Fin (n + 1) → ℝ := fun l a =>
    bernstein n a (x l) * (if l = m then g a else 1)
  have hc : ∀ j : Fin d → Fin (n + 1), tensorWeight n x j * g (j m) = ∏ l, c l (j l) := by
    intro j
    unfold tensorWeight
    simp only [c, prod_mul_distrib, prod_ite_eq', Finset.mem_univ, ite_true]
  simp only [hc]
  rw [sum_prod_eq c, ← mul_prod_erase univ (fun l => ∑ a, c l a) (Finset.mem_univ m)]
  have h1 : ∏ l ∈ univ.erase m, ∑ a, c l a = 1 := by
    apply prod_eq_one
    intro l hl
    have hlm : l ≠ m := ne_of_mem_erase hl
    simp only [c, hlm, ite_false, mul_one]
    exact bernstein.probability n (x l)
  rw [h1, mul_one]
  simp [c]

/-- **(29), general `d`.** If `f` is `M`-Lipschitz for the `ℓ¹` distance on the cube, then
`|B_n f(x) - f(x)| ≤ d · M / (2√n)`. (The paper uses `d = 5`, giving `5M/(2√n)`.) -/
theorem bernstein_tensor_value_error {n : ℕ} (hn : n ≠ 0) {M : ℝ} (hM : 0 ≤ M)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ y z : Fin d → ℝ, (∀ l, y l ∈ Icc (0 : ℝ) 1) → (∀ l, z l ∈ Icc (0 : ℝ) 1) →
      |f y - f z| ≤ M * ∑ l, |y l - z l|)
    (x : Fin d → I) :
    |tensorBernstein n f x - f (fun l => (x l : ℝ))| ≤ d * M / (2 * Real.sqrt n) := by
  set x' : Fin d → ℝ := fun l => (x l : ℝ)
  have hx' : ∀ l, x' l ∈ Icc (0 : ℝ) 1 := fun l => (x l).2
  have hgrid : ∀ j : Fin d → Fin (n + 1), ∀ l, gridPt n j l ∈ Icc (0 : ℝ) 1 := by
    intro j l
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    refine ⟨div_nonneg (Nat.cast_nonneg _) hn'.le, ?_⟩
    rw [gridPt, div_le_one hn']
    exact_mod_cast Nat.lt_succ_iff.mp (j l).2
  have hdiff : tensorBernstein n f x - f x' =
      ∑ j : Fin d → Fin (n + 1), (f (gridPt n j) - f x') * tensorWeight n x j := by
    have e : f x' = ∑ j, f x' * tensorWeight n x j := by
      rw [← mul_sum, sum_tensorWeight, mul_one]
    unfold tensorBernstein
    conv_lhs => rw [e]
    rw [← sum_sub_distrib]
    simp only [sub_mul]
  rw [hdiff]
  calc |∑ j, (f (gridPt n j) - f x') * tensorWeight n x j|
      ≤ ∑ j, |(f (gridPt n j) - f x') * tensorWeight n x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, M * (∑ l, |(j l : ℝ) / n - x' l|) * tensorWeight n x j := by
        apply sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (tensorWeight_nonneg n x j)]
        exact mul_le_mul_of_nonneg_right (hf _ _ (hgrid j) hx') (tensorWeight_nonneg n x j)
    _ = M * ∑ l, ∑ j : Fin d → Fin (n + 1), tensorWeight n x j * |(j l : ℝ) / n - x' l| := by
        simp_rw [mul_sum, sum_mul]
        rw [sum_comm]
        exact sum_congr rfl fun l _ => sum_congr rfl fun j _ => by ring
    _ = M * ∑ l, ∑ a : Fin (n + 1), bernstein n a (x l) * |(a : ℝ) / n - x' l| := by
        congr 1
        apply sum_congr rfl; intro l _
        exact sum_tensorWeight_mul_marginal n x l (fun a => |(a : ℝ) / n - x' l|)
    _ ≤ M * ∑ _l : Fin d, 1 / (2 * Real.sqrt n) := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply sum_le_sum; intro l _
        have h := bernstein_mean_abs_dev hn (x l)
        have e : ∑ a : Fin (n + 1), bernstein n a (x l) * |(a : ℝ) / n - x' l| =
            ∑ a : Fin (n + 1), bernstein n a (x l) * |(x l : ℝ) - (a : ℝ) / n| :=
          sum_congr rfl fun a _ => by rw [abs_sub_comm]
        rw [e]
        exact h.trans (sqrt_var_le hn (x l))
    _ = d * M / (2 * Real.sqrt n) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Grönwall (32) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(32).** Let `v` be `L`-Lipschitz in space and `w` uniformly `η`-close to `v`. Integral
curves `y` of `v` and `z` of `w` on `[0,1]` with the same initial point satisfy
`|z(1) - y(1)| ≤ η (e^L - 1) / L`. -/
theorem flow_error_le {v w : ℝ → E → E} {L : NNReal} (hL : (L : ℝ) ≠ 0) {η : ℝ}
    (hv : ∀ t, LipschitzWith L (v t)) (hη : ∀ t x, dist (w t x) (v t x) ≤ η)
    {y z : ℝ → E} (hy : IsIntegralCurveOn y v (Icc 0 1))
    (hz : IsIntegralCurveOn z w (Icc 0 1)) (h0 : z 0 = y 0) :
    dist (z 1) (y 1) ≤ η * (Real.exp L - 1) / L := by
  have hIci : ∀ t ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) 1 ∈ nhdsWithin t (Ici t) := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have key := dist_le_of_approx_trajectories_ODE (v := v) (K := L) (δ := 0)
    (εf := η) (εg := 0) (f := z) (g := y) (f' := fun t => w t (z t))
    (g' := fun t => v t (y t)) hv
    (fun t ht => (hz t ht).continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun t _ => hη t (z t))
    (fun t ht => (hy t ht).continuousWithinAt)
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun t _ => by rw [dist_self])
    (by rw [h0, dist_self]) 1 ⟨zero_le_one, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hL] at key
  simp only [zero_mul, zero_add, add_zero, sub_zero, mul_one] at key
  calc dist (z 1) (y 1) ≤ η / L * (Real.exp L - 1) := key
    _ = η * (Real.exp L - 1) / L := by ring

/-- **(28)+(32).** With `L ≥ 1` and `η = b e^{-L}/2`, the displacement bound is `< b`. -/
theorem eta_choice {L b : ℝ} (hL : 1 ≤ L) (hb : 0 < b) :
    b * Real.exp (-L) / 2 * (Real.exp L - 1) / L < b := by
  have hL0 : 0 < L := by linarith
  have he : 0 < Real.exp L := Real.exp_pos L
  have hinv : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
  rw [div_lt_iff₀ hL0]
  have h1 : b * Real.exp (-L) / 2 * (Real.exp L - 1) ≤ b / 2 := by
    have : b * Real.exp (-L) / 2 * (Real.exp L - 1) =
        b / 2 - b * Real.exp (-L) / 2 := by
      have e : b * Real.exp (-L) / 2 * (Real.exp L - 1) =
          b / 2 * ((Real.exp L - 1) * Real.exp (-L)) := by ring
      rw [e, sub_mul, mul_comm (Real.exp L), hinv, one_mul]; ring
    have : 0 ≤ b * Real.exp (-L) / 2 := by positivity
    linarith
  nlinarith

/-! ### Cutoff (31) -/

/-- **(31) error identity.** If `βH = H` at a point (so `∇H = β∇H + H∇β` there), then
`∇(βP) - ∇H = β∇(P - H) + (P - H)∇β`, and with `0 ≤ β ≤ 1`, `‖∇β‖ ≤ C`, `|P - H| < 2δ`,
`‖∇P - ∇H‖ < 2δ`, the field error is `< 2δ(1 + C)`. Stated for the gradient vectors at
one point. -/
theorem cutoff_gradient_error {β P H C δ : ℝ} {gβ gP gH : E}
    (hβH : gH = β • gH + H • gβ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hC : ‖gβ‖ ≤ C)
    (hPH : |P - H| < 2 * δ) (hgPH : ‖gP - gH‖ < 2 * δ) :
    ‖(β • gP + P • gβ) - gH‖ < 2 * δ * (1 + C) := by
  have hid : (β • gP + P • gβ) - gH = β • (gP - gH) + (P - H) • gβ := by
    conv_lhs => rw [hβH]
    simp only [smul_sub, sub_smul]; abel
  rw [hid]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hδ : 0 < δ := by
    have := abs_nonneg (P - H); linarith
  calc ‖β • (gP - gH) + (P - H) • gβ‖ ≤ ‖β • (gP - gH)‖ + ‖(P - H) • gβ‖ := norm_add_le _ _
    _ = |β| * ‖gP - gH‖ + |P - H| * ‖gβ‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 1 * ‖gP - gH‖ + |P - H| * C := by
        gcongr
        · rw [abs_of_nonneg hβ0]; exact hβ1
    _ < 2 * δ + 2 * δ * C := by
        have := mul_le_mul_of_nonneg_right hPH.le hC0
        linarith
    _ = 2 * δ * (1 + C) := by ring

end SymplecticPacking
