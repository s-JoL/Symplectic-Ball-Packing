import SymplecticPacking.Effective.PackingCertificate
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Source-cell and target-ball tests

Finite rational source-cell and target-ball tests, with geometric soundness.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate

open Set Finset
set_option maxHeartbeats 1000000

def l2Vector {d : ℕ} (x : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x

@[simp] theorem l2Vector_apply {d : ℕ} (x : Fin d → ℝ) (j : Fin d) :
    l2Vector x j = x j := rfl

@[simp] theorem l2Vector_sub {d : ℕ} (x y : Fin d → ℝ) :
    l2Vector (x-y) = l2Vector x-l2Vector y := rfl

/-- A deliberately coarse, dimension-uniform comparison. The constant is rational. -/
theorem l2_norm_le_sum_abs {d : ℕ} (x : Fin d → ℝ) :
    ‖l2Vector x‖ ≤ ∑ j, |x j| := by
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ j, ‖l2Vector x j‖^2) ≤ Real.sqrt ((∑ j, |x j|)^2) := by
      apply Real.sqrt_le_sqrt
      simp only [l2Vector_apply, Real.norm_eq_abs]
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg _)
    _ = _ := Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)

theorem l2_norm_le_dim_mul {d : ℕ} {x : Fin d → ℝ} {e : ℝ}
    (he : 0 ≤ e) (hx : ‖x‖ ≤ e) : ‖l2Vector x‖ ≤ (d:ℝ)*e := by
  refine (l2_norm_le_sum_abs x).trans ?_
  calc
    ∑ j, |x j| ≤ ∑ _j : Fin d, e := Finset.sum_le_sum fun j _ => by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans hx
    _ = (d:ℝ)*e := by simp

/-- Squared Euclidean norm of a rational point. -/
def sqNorm {d : ℕ} (x : Fin d → ℚ) : ℚ := ∑ j, x j^2

theorem sqNorm_cast {d : ℕ} (x : Fin d → ℚ) :
    (sqNorm x:ℝ) = ‖l2Vector (ODE.castVector x)‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [sqNorm, l2Vector, ODE.castVector]

/-- The terminal test pays the sup-to-Euclidean error before squaring. -/
def targetCheck {d : ℕ} (x : Fin d → ℚ) (e R : ℚ) : Bool :=
  decide (0 < R-(d:ℚ)*e ∧ sqNorm x < (R-(d:ℚ)*e)^2)

theorem targetCheck_sound {d : ℕ} {x : Fin d → ℚ} {y : Fin d → ℝ} {e R : ℚ}
    (he : 0 ≤ e) (hdist : ‖y-ODE.castVector x‖ ≤ (e:ℝ))
    (hc : targetCheck x e R = true) : ‖l2Vector y‖ < (R:ℝ) := by
  have hc' : 0 < R-(d:ℚ)*e ∧ sqNorm x < (R-(d:ℚ)*e)^2 :=
    of_decide_eq_true hc
  have hmargin : (0:ℝ) < (R:ℝ)-(d:ℝ)*e := by exact_mod_cast hc'.1
  have hs : ‖l2Vector (ODE.castVector x)‖^2 < ((R:ℝ)-(d:ℝ)*e)^2 := by
    rw [← sqNorm_cast]
    exact_mod_cast hc'.2
  have hx : ‖l2Vector (ODE.castVector x)‖ < (R:ℝ)-(d:ℝ)*e := by
    nlinarith [norm_nonneg (l2Vector (ODE.castVector x))]
  have herr := l2_norm_le_dim_mul (by exact_mod_cast he) hdist
  rw [l2Vector_sub] at herr
  calc
    ‖l2Vector y‖ ≤ ‖l2Vector y-l2Vector (ODE.castVector x)‖+
        ‖l2Vector (ODE.castVector x)‖ := by
      simpa only [add_comm] using norm_le_insert' (l2Vector y) (l2Vector (ODE.castVector x))
    _ < (R:ℝ) := by linarith

/-- A cell centred at `a` is discarded only when it lies outside the rational
outer source ball even after paying its whole covering radius. -/
def outsideCheck {d : ℕ} (a s : Fin d → ℚ) (ρ r : ℚ) : Bool :=
  decide ((r+(d:ℚ)*ρ)^2 < sqNorm (a-s))

theorem outsideCheck_false_of_covered {d : ℕ} {a s : Fin d → ℚ}
    {x : Fin d → ℝ} {ρ r : ℚ} (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hcover : ‖ODE.castVector a-x‖ ≤ (ρ:ℝ))
    (hball : ‖l2Vector (x-ODE.castVector s)‖ ≤ (r:ℝ)) :
    outsideCheck a s ρ r = false := by
  have hnear := l2_norm_le_dim_mul (by exact_mod_cast hρ) hcover
  rw [l2Vector_sub] at hnear hball
  have htri : ‖l2Vector (ODE.castVector a)-l2Vector (ODE.castVector s)‖ ≤
      (r:ℝ)+(d:ℝ)*ρ := by
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)
  have hp : (0:ℝ) ≤ (r:ℝ)+(d:ℝ)*ρ := by
    have hr' : (0:ℝ) ≤ r := by exact_mod_cast hr
    have hρ' : (0:ℝ) ≤ ρ := by exact_mod_cast hρ
    positivity
  have hsq : (sqNorm (a-s):ℝ) ≤ ((r:ℝ)+(d:ℝ)*ρ)^2 := by
    rw [sqNorm_cast]
    have heq : l2Vector (ODE.castVector (a-s)) =
        l2Vector (ODE.castVector a)-l2Vector (ODE.castVector s) := by
      ext j; simp [ODE.castVector, l2Vector]
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hq : sqNorm (a-s) ≤ (r+(d:ℚ)*ρ)^2 := by exact_mod_cast hsq
  exact decide_eq_false (not_lt_of_ge hq)

/-- One source-cell check. The trajectory branch is a finite Euler tube and
terminal test; the other branch has the geometric exclusion proof above. -/
def cellCheck {d : ℕ} (N : ℕ) (x : ℕ → Fin d → ℚ) (s : Fin d → ℚ)
    (ρ r e plateau target : ℚ) : Bool :=
  outsideCheck (x 0) s ρ r ||
    (plateauCheck N x e plateau && targetCheck (x N) e target)

theorem cellCheck_of_covered {d : ℕ} {N : ℕ} {x : ℕ → Fin d → ℚ}
    {s : Fin d → ℚ} {y : Fin d → ℝ} {ρ r e plateau target : ℚ}
    (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hcover : ‖ODE.castVector (x 0)-y‖ ≤ (ρ:ℝ))
    (hball : ‖l2Vector (y-ODE.castVector s)‖ ≤ (r:ℝ))
    (hc : cellCheck N x s ρ r e plateau target = true) :
    plateauCheck N x e plateau = true ∧ targetCheck (x N) e target = true := by
  have ho := outsideCheck_false_of_covered hρ hr hcover hball
  simpa only [cellCheck, ho, Bool.false_or, Bool.and_eq_true] using hc

end SymplecticPacking.Effective.PackingCertificate
