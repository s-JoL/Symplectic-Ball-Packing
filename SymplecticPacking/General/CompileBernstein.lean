import SymplecticPacking.Compile

/-!
# Tensor Bernstein estimates in `q` variables (supplement, Proposition `prop:cpl-bernstein`)

For `g : ℝ^q → ℝ` smooth whose first and second partial derivatives are bounded by `M₀` on the
cube `[0,1]^q`, and rational (here: real) coefficients `h_m` within `A` of the grid values
`g(m/N)`, the polynomial `P_norm = Σ_m h_m W_m` satisfies on the cube
* `|P_norm - g| ≤ q M₀ / (2√N) + A`, and
* along every coordinate line, `|∂_j P_norm - ∂_j g| ≤ M₀ (q/(2√N) + 2/N) + 2 N A`.

The derivative formula is the summation by parts `∂_j Σ_m h_m W_m = N Σ (h_{m+e_j} - h_m) W^{(j)}_m`
(`hasDerivAt_Pn_update`), and the estimate uses the mean value theorem and the binomial mean
absolute deviation (`bernstein_mean_abs_dev`).
-/

noncomputable section

namespace SymplecticPacking.General.Compile

open Finset Real Set
open scoped unitInterval

/-! ### One variable -/

/-- The Bernstein basis polynomial `b_{N,a}(x) = (N choose a) x^a (1-x)^(N-a)` as a real function. -/
def bW (N a : ℕ) (x : ℝ) : ℝ := (N.choose a : ℝ) * x ^ a * (1 - x) ^ (N - a)

lemma bW_eq_eval (N a : ℕ) (x : ℝ) : bW N a x = (bernsteinPolynomial ℝ N a).eval x := by
  simp [bW, bernsteinPolynomial]

lemma bW_eq_bernstein (N a : ℕ) (x : I) : bW N a x = bernstein N a x := by
  rw [bernstein_apply]; rfl

lemma bW_nonneg (N a : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ bW N a x := by
  have h0 := hx.1
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  unfold bW; positivity

lemma sum_bW (N : ℕ) (x : ℝ) : ∑ a : Fin (N + 1), bW N a x = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ N)
  rw [Polynomial.eval_finset_sum, Polynomial.eval_one] at h
  rw [Fin.sum_univ_eq_sum_range (fun a => bW N a x), ← h]
  exact sum_congr rfl fun a _ => bW_eq_eval N a x

lemma bW_succ_self (M : ℕ) (x : ℝ) : bW M (M + 1) x = 0 := by
  simp [bW, Nat.choose_succ_self]

lemma hasDerivAt_bW (N a : ℕ) (x : ℝ) :
    HasDerivAt (bW N a) ((Polynomial.derivative (bernsteinPolynomial ℝ N a)).eval x) x := by
  have : bW N a = fun x => (bernsteinPolynomial ℝ N a).eval x := funext (bW_eq_eval N a)
  rw [this]; exact Polynomial.hasDerivAt _ x

lemma contDiff_bW (N a : ℕ) : ContDiff ℝ ⊤ (bW N a) := by
  unfold bW; fun_prop

lemma eval_derivative_zero (M : ℕ) (x : ℝ) :
    (Polynomial.derivative (bernsteinPolynomial ℝ (M + 1) 0)).eval x =
      -((M : ℝ) + 1) * bW M 0 x := by
  rw [bernsteinPolynomial.derivative_zero]
  simp [bW_eq_eval]

lemma eval_derivative_succ (M b : ℕ) (x : ℝ) :
    (Polynomial.derivative (bernsteinPolynomial ℝ (M + 1) (b + 1))).eval x =
      ((M : ℝ) + 1) * (bW M b x - bW M (b + 1) x) := by
  rw [bernsteinPolynomial.derivative_succ]
  simp [bW_eq_eval]

/-- **Summation by parts.** `Σ_a h_a b'_{M+1,a}(x) = (M+1) Σ_a (h_{a+1} - h_a) b_{M,a}(x)`. -/
lemma sum_mul_deriv_bW (M : ℕ) (h : Fin (M + 1 + 1) → ℝ) (x : ℝ) :
    ∑ a : Fin (M + 1 + 1), h a * (Polynomial.derivative (bernsteinPolynomial ℝ (M + 1) a)).eval x =
      ((M : ℝ) + 1) * ∑ a : Fin (M + 1), (h a.succ - h a.castSucc) * bW M a x := by
  have key : ∑ b : Fin (M + 1), h b.castSucc * bW M b x =
      h 0 * bW M 0 x + ∑ b : Fin (M + 1), h b.succ * bW M (b + 1) x := by
    have e1 := Fin.sum_univ_castSucc (fun a : Fin (M + 1 + 1) => h a * bW M a x)
    have e2 := Fin.sum_univ_succ (fun a : Fin (M + 1 + 1) => h a * bW M a x)
    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero, bW_succ_self,
      mul_zero, add_zero] at e1 e2
    rw [← e1, e2]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, eval_derivative_zero, eval_derivative_succ]
  have e3 : ∑ b : Fin (M + 1), h b.succ * (((M : ℝ) + 1) * (bW M b x - bW M (b + 1) x)) =
      ((M : ℝ) + 1) * (∑ b : Fin (M + 1), h b.succ * bW M b x -
        ∑ b : Fin (M + 1), h b.succ * bW M (b + 1) x) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]; exact sum_congr rfl fun b _ => by ring
  have e4 : ∑ a : Fin (M + 1), (h a.succ - h a.castSucc) * bW M a x =
      ∑ b : Fin (M + 1), h b.succ * bW M b x - ∑ b : Fin (M + 1), h b.castSucc * bW M b x := by
    rw [← Finset.sum_sub_distrib]; exact sum_congr rfl fun b _ => by ring
  rw [e3, e4, key]; ring

/-- Mean absolute deviation, real form: `Σ_a b_{N,a}(x) |a/N - x| ≤ 1/(2√N)`. -/
lemma sum_bW_abs_le {N : ℕ} (hN : N ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∑ a : Fin (N + 1), bW N a x * |(a : ℝ) / N - x| ≤ 1 / (2 * Real.sqrt N) := by
  have h := (bernstein_mean_abs_dev hN ⟨x, hx⟩).trans (sqrt_var_le hN ⟨x, hx⟩)
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun a _ => ?_
  rw [bW_eq_bernstein N a ⟨x, hx⟩, abs_sub_comm]

/-- `Σ_a b_{M,a}(x) |a - M x| ≤ √(M+1)/2`. -/
lemma sum_bW_abs_sub_le (M : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∑ a : Fin (M + 1), bW M a x * |(a : ℝ) - M * x| ≤ Real.sqrt ((M : ℝ) + 1) / 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h := sum_bW_abs_le (N := M) hM.ne' hx
  have e : ∑ a : Fin (M + 1), bW M a x * |(a : ℝ) - M * x| =
      M * ∑ a : Fin (M + 1), bW M a x * |(a : ℝ) / M - x| := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have : (a : ℝ) - M * x = M * ((a : ℝ) / M - x) := by field_simp
    rw [this, abs_mul, abs_of_pos hM']; ring
  rw [e]
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM'
  calc (M : ℝ) * ∑ a : Fin (M + 1), bW M a x * |(a : ℝ) / M - x|
      ≤ M * (1 / (2 * Real.sqrt M)) := mul_le_mul_of_nonneg_left h hM'.le
    _ = Real.sqrt M / 2 := by
        field_simp
        rw [Real.sq_sqrt hM'.le]
    _ ≤ Real.sqrt ((M : ℝ) + 1) / 2 := by
        gcongr; linarith

/-! ### Tensor weights -/

variable {d : ℕ}

/-- The cube `[0,1]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := {ξ | ∀ i, ξ i ∈ Icc (0 : ℝ) 1}

/-- Tensor weight `W_m(ξ) = ∏_i b_{N,m_i}(ξ_i)`. -/
def W (N : ℕ) (m : Fin d → Fin (N + 1)) (ξ : Fin d → ℝ) : ℝ := ∏ i, bW N (m i) (ξ i)

/-- `Σ_m h_m W_m(ξ)`. -/
def Pn (N : ℕ) (h : (Fin d → Fin (N + 1)) → ℝ) (ξ : Fin d → ℝ) : ℝ := ∑ m, h m * W N m ξ

/-- Partial derivative `∂_j f(ξ)` on `ℝ^d`. -/
def cpd (f : (Fin d → ℝ) → ℝ) (j : Fin d) (ξ : Fin d → ℝ) : ℝ := fderiv ℝ f ξ (Pi.single j 1)

lemma W_nonneg (N : ℕ) (m : Fin d → Fin (N + 1)) {ξ : Fin d → ℝ} (hξ : ξ ∈ cube d) :
    0 ≤ W N m ξ := prod_nonneg fun i _ => bW_nonneg _ _ (hξ i)

lemma sum_W (N : ℕ) (ξ : Fin d → ℝ) : ∑ m : Fin d → Fin (N + 1), W N m ξ = 1 := by
  have := SymplecticPacking.sum_prod_eq (d := d) (n := N) (fun l a => bW N a (ξ l))
  unfold W
  rw [this]
  exact prod_eq_one fun l _ => sum_bW N (ξ l)

/-- Marginal: `Σ_m W_m(ξ) f(m_l) = Σ_a b_{N,a}(ξ_l) f(a)`. -/
lemma sum_W_mul_marginal (N : ℕ) (ξ : Fin d → ℝ) (l : Fin d) (f : Fin (N + 1) → ℝ) :
    ∑ m : Fin d → Fin (N + 1), W N m ξ * f (m l) = ∑ a : Fin (N + 1), bW N a (ξ l) * f a := by
  let c : Fin d → Fin (N + 1) → ℝ := fun i a => bW N a (ξ i) * (if i = l then f a else 1)
  have hc : ∀ m : Fin d → Fin (N + 1), W N m ξ * f (m l) = ∏ i, c i (m i) := by
    intro m
    unfold W
    simp only [c, prod_mul_distrib, prod_ite_eq', Finset.mem_univ, ite_true]
  simp only [hc]
  rw [SymplecticPacking.sum_prod_eq c, ← mul_prod_erase univ (fun i => ∑ a, c i a) (mem_univ l)]
  have h1 : ∏ i ∈ univ.erase l, ∑ a, c i a = 1 := by
    apply prod_eq_one
    intro i hi
    have hil : i ≠ l := ne_of_mem_erase hi
    simp only [c, hil, ite_false, mul_one]
    exact sum_bW N (ξ i)
  rw [h1, mul_one]
  simp [c]

/-- `Σ_m W_m(ξ) Σ_l |m_l/N - ξ_l| ≤ d/(2√N)` on the cube. -/
lemma sum_W_l1_le {N : ℕ} (hN : N ≠ 0) {ξ : Fin d → ℝ} (hξ : ξ ∈ cube d) :
    ∑ m : Fin d → Fin (N + 1), W N m ξ * ∑ l, |((m l : ℕ) : ℝ) / N - ξ l| ≤
      d / (2 * Real.sqrt N) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ l, ∑ m : Fin d → Fin (N + 1), W N m ξ * |((m l : ℕ) : ℝ) / N - ξ l|
      = ∑ l, ∑ a : Fin (N + 1), bW N a (ξ l) * |(a : ℝ) / N - ξ l| :=
        sum_congr rfl fun l _ =>
          sum_W_mul_marginal N ξ l (fun a => |((a : ℕ) : ℝ) / N - ξ l|)
    _ ≤ ∑ _l : Fin d, 1 / (2 * Real.sqrt N) := sum_le_sum fun l _ => sum_bW_abs_le hN (hξ l)
    _ = d / (2 * Real.sqrt N) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Derivative along a coordinate line -/

/-- The coefficient of `b_{N,a}(ξ_j)` when only coordinate `j` varies. -/
def G (N : ℕ) {Q : ℕ} (h : (Fin (Q + 1) → Fin (N + 1)) → ℝ) (ξ : Fin (Q + 1) → ℝ)
    (j : Fin (Q + 1)) (a : Fin (N + 1)) : ℝ :=
  ∑ m' : Fin Q → Fin (N + 1), h (j.insertNth a m') * W N m' (fun i => ξ (j.succAbove i))

lemma Pn_update (N : ℕ) {Q : ℕ} (h : (Fin (Q + 1) → Fin (N + 1)) → ℝ) (ξ : Fin (Q + 1) → ℝ)
    (j : Fin (Q + 1)) (s : ℝ) :
    Pn N h (Function.update ξ j s) = ∑ a : Fin (N + 1), bW N a s * G N h ξ j a := by
  unfold Pn G
  rw [← (Fin.insertNthEquiv (fun _ => Fin (N + 1)) j).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun m' _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, W]
  rw [Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Function.update_self,
    Function.update_of_ne (Fin.succAbove_ne j _)]
  ring

/-- The derivative of `Σ_m h_m W_m` along coordinate `j`, in summation-by-parts form. -/
def Dform (M : ℕ) {Q : ℕ} (h : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ) (ξ : Fin (Q + 1) → ℝ)
    (j : Fin (Q + 1)) : ℝ :=
  ((M : ℝ) + 1) * ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1),
    bW M a (ξ j) * W (M + 1) m' (fun i => ξ (j.succAbove i)) *
      (h (j.insertNth a.succ m') - h (j.insertNth a.castSucc m'))

lemma hasDerivAt_Pn_update (M : ℕ) {Q : ℕ} (h : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ)
    (ξ : Fin (Q + 1) → ℝ) (j : Fin (Q + 1)) :
    HasDerivAt (fun u => Pn (M + 1) h (Function.update ξ j u)) (Dform M h ξ j) (ξ j) := by
  have e : (fun u => Pn (M + 1) h (Function.update ξ j u)) =
      fun u => ∑ a : Fin (M + 1 + 1), bW (M + 1) a u * G (M + 1) h ξ j a :=
    funext fun u => Pn_update (M + 1) h ξ j u
  have hD : Dform M h ξ j = ∑ a : Fin (M + 1 + 1), G (M + 1) h ξ j a *
      (Polynomial.derivative (bernsteinPolynomial ℝ (M + 1) a)).eval (ξ j) := by
    rw [sum_mul_deriv_bW, Dform]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    unfold G
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact sum_congr rfl fun m' _ => by ring
  rw [e, hD]
  apply HasDerivAt.fun_sum
  intro a _
  have := (hasDerivAt_bW (M + 1) a (ξ j)).mul_const (G (M + 1) h ξ j a)
  convert this using 1; ring

lemma Dform_add (M : ℕ) {Q : ℕ} (h₁ h₂ : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ)
    (ξ : Fin (Q + 1) → ℝ) (j : Fin (Q + 1)) :
    Dform M (fun m => h₁ m + h₂ m) ξ j = Dform M h₁ ξ j + Dform M h₂ ξ j := by
  unfold Dform
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact sum_congr rfl fun m' _ => by ring

/-- Weighted averages: the double weights `b_{M,a}(ξ_j) W_{m'}` are nonnegative with sum `1`. -/
lemma abs_double_avg_le (M : ℕ) {Q : ℕ} {ξ : Fin (Q + 1) → ℝ} (hξ : ξ ∈ cube (Q + 1))
    (j : Fin (Q + 1)) (F : Fin (M + 1) → (Fin Q → Fin (M + 1 + 1)) → ℝ)
    (u : Fin (M + 1) → ℝ) (v : (Fin Q → Fin (M + 1 + 1)) → ℝ)
    (hF : ∀ a m', |F a m'| ≤ u a + v m') :
    |∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1),
        bW M a (ξ j) * W (M + 1) m' (fun i => ξ (j.succAbove i)) * F a m'| ≤
      ∑ a : Fin (M + 1), bW M a (ξ j) * u a +
        ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' (fun i => ξ (j.succAbove i)) * v m' := by
  set ξ' : Fin Q → ℝ := fun i => ξ (j.succAbove i)
  have hξ' : ξ' ∈ cube Q := fun i => hξ _
  calc _ ≤ ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1),
        |bW M a (ξ j) * W (M + 1) m' ξ' * F a m'| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1),
        bW M a (ξ j) * W (M + 1) m' ξ' * (u a + v m') := by
        refine sum_le_sum fun a _ => sum_le_sum fun m' _ => ?_
        rw [abs_mul, abs_of_nonneg (mul_nonneg (bW_nonneg _ _ (hξ j)) (W_nonneg _ _ hξ'))]
        exact mul_le_mul_of_nonneg_left (hF a m')
          (mul_nonneg (bW_nonneg _ _ (hξ j)) (W_nonneg _ _ hξ'))
    _ = (∑ a : Fin (M + 1), bW M a (ξ j) * u a) * ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' ξ' +
        (∑ a : Fin (M + 1), bW M a (ξ j)) *
          ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' ξ' * v m' := by
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun m' _ => by ring
    _ = _ := by rw [sum_W, sum_bW]; ring

/-! ### Mean value and `ℓ¹`-Lipschitz bounds on the cube -/

lemma hasDerivAt_update_comp {f : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (ξ : Fin d → ℝ) (j : Fin d) (u : ℝ) :
    HasDerivAt (fun s => f (Function.update ξ j s)) (cpd f j (Function.update ξ j u)) u :=
  (hf _).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_update ξ j u)

lemma mem_cube_update {ξ : Fin d → ℝ} (hξ : ξ ∈ cube d) (j : Fin d) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : Function.update ξ j u ∈ cube d := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simpa using hu
  · simpa [Function.update_of_ne h] using hξ i

/-- If all partial derivatives of `f` are bounded by `M` on the cube, then `f` is
`M`-Lipschitz there for the `ℓ¹` distance. -/
lemma l1_lipschitz {f : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ p ∈ cube d, ∀ j, |cpd f j p| ≤ M) {y z : Fin d → ℝ} (hy : y ∈ cube d)
    (hz : z ∈ cube d) : |f y - f z| ≤ M * ∑ l, |y l - z l| := by
  set φ : ℝ → ℝ := fun t => f (z + t • (y - z))
  have hline : ∀ t, HasDerivAt (fun t : ℝ => z + t • (y - z)) (y - z) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (y - z)).const_add z
  have hφ : ∀ t, HasDerivAt φ (fderiv ℝ f (z + t • (y - z)) (y - z)) t := fun t =>
    (hf _).hasFDerivAt.comp_hasDerivAt t (hline t)
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope φ (fun t => fderiv ℝ f (z + t • (y - z)) (y - z))
    zero_lt_one (fun t _ => (hφ t).continuousAt.continuousWithinAt) (fun t _ => hφ t)
  have h1 : φ 1 = f y := by simp [φ]
  have h0 : φ 0 = f z := by simp [φ]
  rw [h1, h0, sub_zero, div_one] at hcd
  rw [← hcd]
  set p := z + c • (y - z)
  have hp : p ∈ cube d := by
    intro i
    have hyi := hy i; have hzi := hz i
    simp only [p, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Set.mem_Icc] at hyi hzi ⊢
    have k1 := mul_nonneg hc.1.le hyi.1
    have k2 := mul_nonneg (sub_nonneg.2 hc.2.le) hzi.1
    have k3 := mul_nonneg hc.1.le (sub_nonneg.2 hyi.2)
    have k4 := mul_nonneg (sub_nonneg.2 hc.2.le) (sub_nonneg.2 hzi.2)
    constructor <;> nlinarith
  have hdec : y - z = ∑ l, (y l - z l) • (Pi.single l (1 : ℝ) : Fin d → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec, map_sum]
  calc |∑ l, fderiv ℝ f p ((y l - z l) • Pi.single l 1)|
      ≤ ∑ l, |fderiv ℝ f p ((y l - z l) • Pi.single l 1)| := abs_sum_le_sum_abs _ _
    _ = ∑ l, |y l - z l| * |cpd f l p| := by
        refine sum_congr rfl fun l _ => ?_
        rw [map_smul, smul_eq_mul, abs_mul]; rfl
    _ ≤ ∑ l, |y l - z l| * M := sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (hM p hp l) (abs_nonneg _)
    _ = M * ∑ l, |y l - z l| := by rw [Finset.mul_sum]; exact sum_congr rfl fun l _ => by ring

/-! ### The two estimates -/

lemma gridPt_insertNth {Q N : ℕ} (j : Fin (Q + 1)) (b : Fin (N + 1)) (m' : Fin Q → Fin (N + 1)) :
    SymplecticPacking.gridPt N (j.insertNth b m') =
      Function.update (SymplecticPacking.gridPt N (j.insertNth 0 m')) j ((b : ℝ) / N) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i', rfl⟩
  · simp [SymplecticPacking.gridPt]
  · simp [SymplecticPacking.gridPt, Function.update_of_ne (Fin.succAbove_ne j i')]

/-- Derivative error of the grid part (Proposition `prop:cpl-bernstein`(b)). -/
lemma Dform_grid_error (M : ℕ) {Q : ℕ} {g : (Fin (Q + 1) → ℝ) → ℝ} (hg : Differentiable ℝ g)
    (hg' : ∀ j, Differentiable ℝ (cpd g j)) {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (h2 : ∀ ξ ∈ cube (Q + 1), ∀ j l, |cpd (cpd g j) l ξ| ≤ M₀)
    {ξ : Fin (Q + 1) → ℝ} (hξ : ξ ∈ cube (Q + 1)) (j : Fin (Q + 1)) :
    |Dform M (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ j - cpd g j ξ| ≤
      M₀ * (((Q : ℝ) + 1) / (2 * Real.sqrt ((M : ℝ) + 1)) + 2 / ((M : ℝ) + 1)) := by
  set N : ℝ := (M : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hNcast : ((M + 1 : ℕ) : ℝ) = N := by push_cast; rfl
  set ξ' : Fin Q → ℝ := fun i => ξ (j.succAbove i)
  have hξ' : ξ' ∈ cube Q := fun i => hξ _
  -- mean value points
  have hmvt : ∀ (a : Fin (M + 1)) (m' : Fin Q → Fin (M + 1 + 1)), ∃ c ∈ Ioo ((a : ℝ) / N)
      (((a : ℝ) + 1) / N), N * (g (SymplecticPacking.gridPt (M + 1) (j.insertNth a.succ m')) -
        g (SymplecticPacking.gridPt (M + 1) (j.insertNth a.castSucc m'))) =
        cpd g j (Function.update (SymplecticPacking.gridPt (M + 1) (j.insertNth 0 m')) j c) := by
    intro a m'
    set base := SymplecticPacking.gridPt (M + 1) (j.insertNth 0 m')
    have hlt : (a : ℝ) / N < ((a : ℝ) + 1) / N := by gcongr; linarith
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun u => g (Function.update base j u))
      (fun u => cpd g j (Function.update base j u)) hlt
      (fun u _ => (hasDerivAt_update_comp hg base j u).continuousAt.continuousWithinAt)
      (fun u _ => hasDerivAt_update_comp hg base j u)
    refine ⟨c, hc, ?_⟩
    have hs : SymplecticPacking.gridPt (M + 1) (j.insertNth a.succ m') =
        Function.update base j (((a : ℝ) + 1) / N) := by
      rw [gridPt_insertNth j a.succ m', hNcast]; simp [base]
    have hs' : SymplecticPacking.gridPt (M + 1) (j.insertNth a.castSucc m') =
        Function.update base j ((a : ℝ) / N) := by
      rw [gridPt_insertNth j a.castSucc m', hNcast]; simp [base]
    have hw : ((a : ℝ) + 1) / N - (a : ℝ) / N = 1 / N := by ring
    rw [hcd, hs, hs', hw]
    field_simp
  choose c hc hcd using hmvt
  -- rewrite the derivative form as an average of `∂_j g` at the mean value points
  have hrepr : Dform M (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ j - cpd g j ξ =
      ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1), bW M a (ξ j) * W (M + 1) m' ξ' *
        (cpd g j (Function.update (SymplecticPacking.gridPt (M + 1) (j.insertNth 0 m')) j
          (c a m')) - cpd g j ξ) := by
    have hone : ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1),
        bW M a (ξ j) * W (M + 1) m' ξ' = 1 := by
      simp_rw [← Finset.mul_sum, sum_W, mul_one, sum_bW]
    have hD : Dform M (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ j =
        ∑ a : Fin (M + 1), ∑ m' : Fin Q → Fin (M + 1 + 1), bW M a (ξ j) * W (M + 1) m' ξ' *
          cpd g j (Function.update (SymplecticPacking.gridPt (M + 1) (j.insertNth 0 m')) j
            (c a m')) := by
      unfold Dform
      rw [Finset.mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m' _ => ?_
      rw [← hcd a m']
      simp only [ξ', hNdef]
      ring
    rw [hD]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hone, one_mul]
  rw [hrepr]
  -- pointwise bound
  set u : Fin (M + 1) → ℝ := fun a => M₀ * (|(a : ℝ) - M * ξ j| / N + 2 / N)
  set v : (Fin Q → Fin (M + 1 + 1)) → ℝ := fun m' => M₀ * ∑ l, |((m' l : ℕ) : ℝ) / N - ξ' l|
  have hpt : ∀ a m', |cpd g j (Function.update (SymplecticPacking.gridPt (M + 1)
      (j.insertNth 0 m')) j (c a m')) - cpd g j ξ| ≤ u a + v m' := by
    intro a m'
    set base := SymplecticPacking.gridPt (M + 1) (j.insertNth 0 m')
    have ha : (a : ℝ) + 1 ≤ N := by
      have := a.isLt; simp only [hNdef]; exact_mod_cast this
    have hc0 : 0 ≤ c a m' := le_trans (by positivity) (hc a m').1.le
    have hc1 : c a m' ≤ 1 := le_trans (hc a m').2.le (by rw [div_le_one hN]; exact ha)
    have hbase : base ∈ cube (Q + 1) := by
      intro i
      simp only [base, SymplecticPacking.gridPt, Set.mem_Icc]
      rw [hNcast]
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hN]
      have h0 : ((j.insertNth (α := fun _ => Fin (M + 1 + 1)) 0 m' i : Fin (M + 1 + 1)) : ℕ)
          ≤ M + 1 := Nat.lt_succ_iff.mp (Fin.is_lt _)
      have h' : (((j.insertNth (α := fun _ => Fin (M + 1 + 1)) 0 m' i : Fin (M + 1 + 1)) : ℕ)
          : ℝ) ≤ M + 1 := by exact_mod_cast h0
      linarith
    have hp := mem_cube_update hbase j ⟨hc0, hc1⟩
    have hlip := l1_lipschitz (hg' j) (fun p hp l => h2 p hp j l) hp hξ
    refine hlip.trans ?_
    rw [Fin.sum_univ_succAbove _ j, mul_add]
    simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne j _)]
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ hM₀
      -- `|c - ξ_j| ≤ |a - Mξ_j|/N + 2/N`
      have hcI := hc a m'
      have hξj := hξ j
      have l1 : (a : ℝ) < c a m' * N := by have := hcI.1; rwa [div_lt_iff₀ hN] at this
      have l2 : c a m' * N < (a : ℝ) + 1 := by have := hcI.2; rwa [lt_div_iff₀ hN] at this
      have eN : ξ j * N = M * ξ j + ξ j := by rw [hNdef]; ring
      have hab := abs_le.mp (le_refl |(a : ℝ) - M * ξ j|)
      rw [show |(a : ℝ) - M * ξ j| / N + 2 / N = (|(a : ℝ) - M * ξ j| + 2) / N by ring,
        le_div_iff₀ hN]
      have e3 : |c a m' - ξ j| * N = |c a m' * N - ξ j * N| := by
        rw [← sub_mul, abs_mul, abs_of_pos hN]
      rw [e3, abs_le]
      constructor <;> linarith [hξj.1, hξj.2, hab.1, hab.2]
    · refine le_of_eq ?_
      simp only [v, base, SymplecticPacking.gridPt, Fin.insertNth_apply_succAbove, hNcast, ξ']
  refine (abs_double_avg_le M hξ j _ u v hpt).trans ?_
  -- the two weighted sums
  have hU : ∑ a : Fin (M + 1), bW M a (ξ j) * u a ≤
      M₀ * (1 / (2 * Real.sqrt N) + 2 / N) := by
    have hs := sum_bW_abs_sub_le M (hξ j)
    have e : ∑ a : Fin (M + 1), bW M a (ξ j) * u a =
        M₀ * ((∑ a : Fin (M + 1), bW M a (ξ j) * |(a : ℝ) - M * ξ j|) / N + 2 / N) := by
      simp only [u]
      have : ∑ a : Fin (M + 1), bW M a (ξ j) * (M₀ * (|(a : ℝ) - M * ξ j| / N + 2 / N)) =
          M₀ * ((∑ a : Fin (M + 1), bW M a (ξ j) * |(a : ℝ) - M * ξ j|) / N +
            (∑ a : Fin (M + 1), bW M a (ξ j)) * (2 / N)) := by
        rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact sum_congr rfl fun a _ => by ring
      rw [this, sum_bW, one_mul]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hM₀
    have hsN : Real.sqrt N / 2 / N = 1 / (2 * Real.sqrt N) := by
      have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
      field_simp
      rw [Real.sq_sqrt hN.le]
    have : (∑ a : Fin (M + 1), bW M a (ξ j) * |(a : ℝ) - M * ξ j|) / N ≤ Real.sqrt N / 2 / N := by
      gcongr
    linarith
  have hV : ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' ξ' * v m' ≤
      M₀ * (Q / (2 * Real.sqrt N)) := by
    have := sum_W_l1_le (N := M + 1) (Nat.succ_ne_zero M) hξ'
    rw [hNcast] at this
    simp only [v]
    calc ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' ξ' *
          (M₀ * ∑ l, |((m' l : ℕ) : ℝ) / N - ξ' l|)
        = M₀ * ∑ m' : Fin Q → Fin (M + 1 + 1), W (M + 1) m' ξ' *
          ∑ l, |((m' l : ℕ) : ℝ) / N - ξ' l| := by
          rw [Finset.mul_sum]; exact sum_congr rfl fun m' _ => by ring
      _ ≤ M₀ * (Q / (2 * Real.sqrt N)) := mul_le_mul_of_nonneg_left this hM₀
  calc _ ≤ M₀ * (1 / (2 * Real.sqrt N) + 2 / N) + M₀ * (Q / (2 * Real.sqrt N)) := add_le_add hU hV
    _ = M₀ * (((Q : ℝ) + 1) / (2 * Real.sqrt N) + 2 / N) := by ring

/-- Derivative error of the rounding part (Proposition `prop:cpl-bernstein`(c)). -/
lemma Dform_round_error (M : ℕ) {Q : ℕ} (e : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ) {A : ℝ}
    (he : ∀ m, |e m| ≤ A) {ξ : Fin (Q + 1) → ℝ} (hξ : ξ ∈ cube (Q + 1)) (j : Fin (Q + 1)) :
    |Dform M e ξ j| ≤ ((M : ℝ) + 1) * (2 * A) := by
  unfold Dform
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < M + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := abs_double_avg_le M hξ j (fun a m' => e (j.insertNth a.succ m') -
    e (j.insertNth a.castSucc m')) (fun _ => 2 * A) (fun _ => 0) (fun a m' => by
      have h1 := he (j.insertNth a.succ m'); have h2 := he (j.insertNth a.castSucc m')
      rw [add_zero]
      calc _ ≤ |e (j.insertNth a.succ m')| + |e (j.insertNth a.castSucc m')| := abs_sub _ _
        _ ≤ 2 * A := by linarith)
  simp only [mul_zero, sum_const_zero, add_zero] at this
  rwa [← Finset.sum_mul, sum_bW, one_mul] at this

/-- Value error (Proposition `prop:cpl-bernstein`(a) together with the rounding (c)). -/
lemma Pn_value_error (M : ℕ) {Q : ℕ} {g : (Fin (Q + 1) → ℝ) → ℝ} (hg : Differentiable ℝ g)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (h1 : ∀ ξ ∈ cube (Q + 1), ∀ j, |cpd g j ξ| ≤ M₀)
    (Hm : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ) {A : ℝ}
    (hA : ∀ m, |Hm m - g (SymplecticPacking.gridPt (M + 1) m)| ≤ A)
    {ξ : Fin (Q + 1) → ℝ} (hξ : ξ ∈ cube (Q + 1)) :
    |Pn (M + 1) Hm ξ - g ξ| ≤ ((Q : ℝ) + 1) * M₀ / (2 * Real.sqrt ((M : ℝ) + 1)) + A := by
  set x : Fin (Q + 1) → I := fun i => ⟨ξ i, hξ i⟩
  have hB := SymplecticPacking.bernstein_tensor_value_error (d := Q + 1) (n := M + 1)
    (Nat.succ_ne_zero M) hM₀ g (fun y z hy hz => l1_lipschitz hg h1 hy hz) x
  have hT : SymplecticPacking.tensorBernstein (M + 1) g x =
      Pn (M + 1) (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ := by
    unfold SymplecticPacking.tensorBernstein Pn
    refine sum_congr rfl fun m _ => ?_
    congr 1
    unfold SymplecticPacking.tensorWeight W
    exact prod_congr rfl fun i _ => (bW_eq_bernstein _ _ (x i)).symm
  rw [hT] at hB
  have hfx : (fun l => ((x l : I) : ℝ)) = ξ := rfl
  rw [hfx] at hB
  push_cast at hB
  have hR : |Pn (M + 1) Hm ξ - Pn (M + 1) (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ|
      ≤ A := by
    unfold Pn
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ m, |Hm m * W (M + 1) m ξ - g (SymplecticPacking.gridPt (M + 1) m) * W (M + 1) m ξ| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, A * W (M + 1) m ξ := by
          refine sum_le_sum fun m _ => ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg (W_nonneg _ _ hξ)]
          exact mul_le_mul_of_nonneg_right (hA m) (W_nonneg _ _ hξ)
      _ = A := by rw [← Finset.mul_sum, sum_W, mul_one]
  calc _ ≤ |Pn (M + 1) Hm ξ - Pn (M + 1) (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ| +
        |Pn (M + 1) (fun m => g (SymplecticPacking.gridPt (M + 1) m)) ξ - g ξ| := abs_sub_le _ _ _
    _ ≤ A + ((Q : ℝ) + 1) * M₀ / (2 * Real.sqrt ((M : ℝ) + 1)) := add_le_add hR hB
    _ = _ := by ring

/-- **Proposition `prop:cpl-bernstein` with rounding**, in the form used by the compilation:
on the cube, the value error and the derivative error along every coordinate line. -/
theorem cube_error (M : ℕ) {Q : ℕ} {g : (Fin (Q + 1) → ℝ) → ℝ} (hg : Differentiable ℝ g)
    (hg' : ∀ j, Differentiable ℝ (cpd g j)) {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (h1 : ∀ ξ ∈ cube (Q + 1), ∀ j, |cpd g j ξ| ≤ M₀)
    (h2 : ∀ ξ ∈ cube (Q + 1), ∀ j l, |cpd (cpd g j) l ξ| ≤ M₀)
    (Hm : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ) {A : ℝ}
    (hA : ∀ m, |Hm m - g (SymplecticPacking.gridPt (M + 1) m)| ≤ A)
    {ξ : Fin (Q + 1) → ℝ} (hξ : ξ ∈ cube (Q + 1)) :
    |Pn (M + 1) Hm ξ - g ξ| ≤ ((Q : ℝ) + 1) * M₀ / (2 * Real.sqrt ((M : ℝ) + 1)) + A ∧
    ∀ j, ∃ D, HasDerivAt (fun u => Pn (M + 1) Hm (Function.update ξ j u) -
        g (Function.update ξ j u)) D (ξ j) ∧
      |D| ≤ M₀ * (((Q : ℝ) + 1) / (2 * Real.sqrt ((M : ℝ) + 1)) + 2 / ((M : ℝ) + 1)) +
        2 * ((M : ℝ) + 1) * A := by
  refine ⟨Pn_value_error M hg hM₀ h1 Hm hA hξ, fun j => ?_⟩
  refine ⟨Dform M Hm ξ j - cpd g j ξ, ?_, ?_⟩
  · have hg0 := hasDerivAt_update_comp hg ξ j (ξ j)
    rw [Function.update_eq_self] at hg0
    exact (hasDerivAt_Pn_update M Hm ξ j).sub hg0
  · set gg : (Fin (Q + 1) → Fin (M + 1 + 1)) → ℝ :=
      fun m => g (SymplecticPacking.gridPt (M + 1) m)
    have hsplit : Hm = fun m => gg m + (Hm m - gg m) := funext fun m => by ring
    have hD : Dform M Hm ξ j = Dform M gg ξ j + Dform M (fun m => Hm m - gg m) ξ j := by
      conv_lhs => rw [hsplit]
      exact Dform_add M _ _ ξ j
    rw [hD]
    have e1 := Dform_grid_error M hg hg' hM₀ h2 hξ j
    have e2 := Dform_round_error M (fun m => Hm m - gg m) hA hξ j
    calc |Dform M gg ξ j + Dform M (fun m => Hm m - gg m) ξ j - cpd g j ξ|
        ≤ |Dform M gg ξ j - cpd g j ξ| + |Dform M (fun m => Hm m - gg m) ξ j| := by
          rw [show Dform M gg ξ j + Dform M (fun m => Hm m - gg m) ξ j - cpd g j ξ =
            (Dform M gg ξ j - cpd g j ξ) + Dform M (fun m => Hm m - gg m) ξ j by ring]
          exact abs_add_le _ _
      _ ≤ _ := by linarith

end SymplecticPacking.General.Compile
