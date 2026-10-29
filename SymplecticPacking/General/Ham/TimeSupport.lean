import SymplecticPacking.General.Ham.Spec

/-!
# Time support of the Hamiltonian of a common isotopy

`sec:ham-hamiltonian`: the Hamiltonian of a common isotopy vanishes for `t ∉ (0,1)` (flat clocks), hence so does
its Hamiltonian vector field.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Problem
open scoped ContDiff

variable {n : ℕ}

/-- A function differentiable at `t₀` and constant on `(-∞, t₀]` has derivative `0` at `t₀`. -/
lemma deriv_eq_zero_of_const_Iic {f : ℝ → E n} {t₀ : ℝ} (hf : DifferentiableAt ℝ f t₀)
    (hc : ∀ s ≤ t₀, f s = f t₀) : deriv f t₀ = 0 := by
  have h1 : HasDerivWithinAt f (deriv f t₀) (Iic t₀) t₀ := hf.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt f 0 (Iic t₀) t₀ :=
    (hasDerivWithinAt_const t₀ (Iic t₀) (f t₀)).congr (fun s hs => hc s hs) rfl
  exact (uniqueDiffWithinAt_Iic t₀).eq_deriv _ h1 h2

/-- Same with `[t₀, ∞)`. -/
lemma deriv_eq_zero_of_const_Ici {f : ℝ → E n} {t₀ : ℝ} (hf : DifferentiableAt ℝ f t₀)
    (hc : ∀ s ≥ t₀, f s = f t₀) : deriv f t₀ = 0 := by
  have h1 : HasDerivWithinAt f (deriv f t₀) (Ici t₀) t₀ := hf.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt f 0 (Ici t₀) t₀ :=
    (hasDerivWithinAt_const t₀ (Ici t₀) (f t₀)).congr (fun s hs => hc s hs) rfl
  exact (uniqueDiffWithinAt_Ici t₀).eq_deriv _ h1 h2

variable {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n} {r1 r2 r3 ρ : Fin k → ℝ}

/-- The time derivative of the isotopy vanishes for `t ≤ 0` and `t ≥ 1` on `B(ρ)`. -/
lemma deriv_time_eq_zero (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) {v : E n} (hv : v ∈ ball (0 : E n) (ρ i)) :
    deriv (fun s => F i s v) t = 0 := by
  have hdiff : DifferentiableAt ℝ (fun s => F i s v) t := by
    have h := (hF.smooth i).contDiffAt (x := (t, v))
      (prod_mem_nhds Filter.univ_mem (isOpen_ball.mem_nhds hv))
    have := (h.differentiableAt (by simp)).comp t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t v)).differentiableAt
    exact this
  rcases ht with ht | ht
  · apply deriv_eq_zero_of_const_Iic hdiff
    intro s hs
    simp only [hF.const_left i s (hs.trans ht), hF.const_left i t ht]
  · apply deriv_eq_zero_of_const_Ici hdiff
    intro s hs
    simp only [hF.const_right i s (le_trans ht hs), hF.const_right i t ht]

/-- `H(t, ·) ≡ 0` for `t ≤ 0` and `t ≥ 1`. -/
theorem ofIsotopy_eq_zero_of_time (hF : CommonIsotopy F s r1 r2 r3 ρ) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) (y : E n) : ofIsotopy F r1 r2 r3 t y = 0 := by
  unfold ofIsotopy
  refine Finset.sum_eq_zero fun i _ => pushforward_eq_zero fun u hu _ => ?_
  have hu' : ∀ r ∈ uIcc (0 : ℝ) 1, r • u ∈ ball (0 : E n) (ρ i) := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.1]
    calc r * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact hr.2
      _ ≤ r3 i := by rw [one_mul]; exact mem_closedBall_zero_iff.mp hu
      _ < ρ i := (hF.radii i).2.2.2
  have : sourcePrimitive (F i) t u = 0 := by
    unfold sourcePrimitive
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro r hr
      simp only [sourceOneForm, deriv_time_eq_zero hF i ht (hu' r hr), omega0]
      simp
  rw [this, mul_zero]

/-- Hence the Hamiltonian vector field vanishes for `t ≤ 0` and `t ≥ 1`. -/
theorem hamVF_ofIsotopy_eq_zero_of_time (hF : CommonIsotopy F s r1 r2 r3 ρ) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) (y : E n) : Problem.hamVF (ofIsotopy F r1 r2 r3) t y = 0 := by
  have h0 : ofIsotopy F r1 r2 r3 t = fun _ => 0 := funext (ofIsotopy_eq_zero_of_time hF ht)
  exact hamVF_eq_zero_of_fderiv (by rw [h0]; simp)

end SymplecticPacking.General.Ham
