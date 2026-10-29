import SymplecticPacking.Effective.Names
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Error estimates for the Euler method

Local defect and perturbed-step estimates for an initial-value problem on `[0,1]`, and the
finite recurrence that sums them; the perturbation of a step is the error of one field-value query.
-/

noncomputable section
namespace SymplecticPacking.Effective.ODE
open Set
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Velocity control follows directly from the differential equation. -/
theorem solution_increment {F : ℝ → E → E} {γ : ℝ → E} {M : ℝ}
    (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (F t (γ t)) t)
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖F t (γ t)‖ ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖γ t - γ s‖ ≤ M * |t - s| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hγ r hr).hasDerivWithinAt) hM (convex_Icc 0 1) hs ht

/-- The first-order local defect is proved from the ODE, rather than assumed
as a property of a proposed numerical trajectory. The coarser constant avoids any
extra differentiability of the field. -/
theorem local_defect {F : ℝ → E → E} {γ : ℝ → E} {A L M : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (F t (γ t)) t)
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖F t (γ t)‖ ≤ M)
    (htime : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖F t x - F s x‖ ≤ A * |t-s|)
    (hspace : ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖F t x - F t y‖ ≤ L * ‖x-y‖)
    {s h : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hh : 0 ≤ h) (hsh : s+h ≤ 1) :
    ‖γ (s+h) - γ s - h • F s (γ s)‖ ≤ (A+L*M)*h^2 := by
  let g : ℝ → E := fun t => γ t - γ s - (t-s) • F s (γ s)
  have hsub : Icc s (s+h) ⊆ Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
  have hg : ∀ t ∈ Icc s (s+h), HasDerivWithinAt g
      (F t (γ t)-F s (γ s)) (Icc s (s+h)) t := by
    intro t ht
    convert (((hγ t (hsub ht)).sub_const (γ s)).sub
      (((hasDerivAt_id t).sub_const s).smul_const (F s (γ s)))).hasDerivWithinAt using 1 <;>
      simp only [g, Pi.sub_apply, id_eq, one_smul] <;> rfl
  have hbound : ∀ t ∈ Icc s (s+h), ‖F t (γ t)-F s (γ s)‖ ≤ (A+L*M)*h := by
    intro t ht
    have hts : |t-s| = t-s := abs_of_nonneg (sub_nonneg.mpr ht.1)
    have hv := solution_increment hγ hM hs (hsub ht)
    have hsp := hspace t (hsub ht) (γ t) (γ s)
    have hti := htime s hs t (hsub ht) (γ s)
    have htri : ‖F t (γ t)-F s (γ s)‖ ≤
        ‖F t (γ t)-F t (γ s)‖ + ‖F t (γ s)-F s (γ s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hts] at hv hti
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s hs)
    calc
      _ ≤ L * (M * (t-s)) + A * (t-s) :=
        htri.trans (add_le_add (hsp.trans (mul_le_mul_of_nonneg_left hv hL)) hti)
      _ = (A+L*M)*(t-s) := by ring
      _ ≤ (A+L*M)*h := mul_le_mul_of_nonneg_left (by linarith [ht.2])
        (add_nonneg hA (mul_nonneg hL hM0))
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound
    (convex_Icc s (s+h)) (show s ∈ Icc s (s+h) by exact ⟨le_rfl, by linarith⟩)
    (show s+h ∈ Icc s (s+h) by exact ⟨by linarith, le_rfl⟩)
  have hgs : g s = 0 := by simp [g]
  have hge : g (s+h) = γ (s+h)-γ s-h • F s (γ s) := by
    simp only [g, add_sub_cancel_left]
  rw [hgs, sub_zero, hge, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] at hb
  nlinarith

/-- A finite recurrence estimate. Only the steps used are required. -/
theorem finite_error_bound {e : ℕ → ℝ} {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (he0 : 0 ≤ e 0) {N : ℕ}
    (hstep : ∀ i < N, e (i+1) ≤ a * e i+b) :
    ∀ i ≤ N, e i ≤ (e 0+(i:ℝ)*b)*a^i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have hiN : i < N := by omega
    have hie := ih (by omega)
    have ha0 : 0 ≤ a := by linarith
    calc
      _ ≤ a * e i + b := hstep i hiN
      _ ≤ a * ((e 0+(i:ℝ)*b)*a^i)+b := by gcongr
      _ ≤ a * ((e 0+(i:ℝ)*b)*a^i)+b*a^(i+1) := by
        exact add_le_add le_rfl (by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (one_le_pow₀ ha : 1 ≤ a^(i+1)) hb))
      _ = (e 0+((i+1:ℕ):ℝ)*b)*a^(i+1) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- Ordinary quantitative hypotheses on the original field and a solution.
They contain no numerical trajectory and no solution-evaluation oracle. -/
structure Bounds (F : ℝ → E → E) (γ : ℝ → E) (A L M : ℝ) : Prop where
  time_nonneg : 0 ≤ A
  space_nonneg : 0 ≤ L
  speed_nonneg : 0 ≤ M
  derivative : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (F t (γ t)) t
  speed : ∀ t ∈ Icc (0:ℝ) 1, ‖F t (γ t)‖ ≤ M
  time : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
    ‖F t x-F s x‖ ≤ A*|t-s|
  space : ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖F t x-F t y‖ ≤ L*‖x-y‖

def gridTime (N i : ℕ) : ℝ := (i:ℝ)/N

theorem gridTime_mem {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    gridTime N i ∈ Icc (0:ℝ) 1 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  exact ⟨div_nonneg (Nat.cast_nonneg i) hN'.le,
    (div_le_one hN').mpr (by exact_mod_cast hi)⟩

theorem gridTime_succ (N i : ℕ) : gridTime N (i+1) = gridTime N i+1/(N:ℝ) := by
  simp only [gridTime, Nat.cast_add, Nat.cast_one]
  ring

/-- Perturbed Euler step: the perturbation is just the error of one field-value query. -/
theorem step_error {F : ℝ → E → E} {γ : ℝ → E} {A L M : ℝ}
    (B : Bounds F γ A L M) {N i : ℕ} (hN : 0 < N) (hi : i < N)
    {x y v : E} {η : ℝ}
    (hstep : y=x+(1/(N:ℝ)) • v)
    (hv : ‖v-F (gridTime N i) x‖ ≤ η) :
    ‖y-γ (gridTime N (i+1))‖ ≤
      (1+L/(N:ℝ))*‖x-γ (gridTime N i)‖ +
        (η/(N:ℝ)+(A+L*M)/(N:ℝ)^2) := by
  let t := gridTime N i
  let h : ℝ := 1/N
  let R := γ (t+h)-γ t-h • F t (γ t)
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have ht : t ∈ Icc (0:ℝ) 1 := gridTime_mem hN (by omega)
  have hth : t+h ≤ 1 := by
    rw [show t+h=gridTime N (i+1) from (gridTime_succ N i).symm]
    exact (gridTime_mem hN (by omega : i+1 ≤ N)).2
  have hR : ‖R‖ ≤ (A+L*M)*h^2 :=
    local_defect B.time_nonneg B.space_nonneg B.derivative B.speed B.time B.space ht hh hth
  have hspace := B.space t ht x (γ t)
  have he : y-γ (t+h) = (x-γ t)+h • (v-F t x)+h • (F t x-F t (γ t))-R := by
    rw [hstep]
    dsimp only [R, h]
    module
  rw [gridTime_succ]
  change ‖y-γ (t+h)‖ ≤ _
  rw [he]
  calc
    _ ≤ (‖x-γ t‖+‖h • (v-F t x)‖)+‖h • (F t x-F t (γ t))‖+‖R‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ = (‖x-γ t‖+h*‖v-F t x‖)+h*‖F t x-F t (γ t)‖+‖R‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ (‖x-γ t‖+h*η)+h*(L*‖x-γ t‖)+(A+L*M)*h^2 := by
      gcongr
    _ = _ := by dsimp only [h, t]; ring

/-- The finite rational Euler iteration. The evaluator receives the step
index and the current rational vector, and returns a rational vector. -/
def rationalEuler (d N : ℕ) (eval : ℕ → (Fin d → ℚ) → (Fin d → ℚ))
    (initial : Fin d → ℚ) : ℕ → Fin d → ℚ
  | 0 => initial
  | i+1 => fun j => rationalEuler d N eval initial i j +
      eval i (rationalEuler d N eval initial i) j / N

def castVector {d : ℕ} (x : Fin d → ℚ) : Fin d → ℝ := fun j => x j

@[simp] theorem rationalEuler_zero (d N : ℕ) (eval) (initial) :
    rationalEuler d N eval initial 0 = initial := rfl

@[simp] theorem rationalEuler_succ_cast (d N : ℕ) (eval) (initial) (i : ℕ) :
    castVector (rationalEuler d N eval initial (i+1)) =
      castVector (rationalEuler d N eval initial i) +
        (1/(N:ℝ)) • castVector (eval i (rationalEuler d N eval initial i)) := by
  funext j
  change ((rationalEuler d N eval initial i j + eval i (rationalEuler d N eval initial i) j / (N:ℚ) : ℚ) : ℝ) =
    (rationalEuler d N eval initial i j : ℝ) + (1/(N:ℝ)) * (eval i (rationalEuler d N eval initial i) j : ℝ)
  push_cast
  ring

/-- A fixed, explicit query precision and mesh. Their cost is conservative;
no search for a successful trajectory is used. -/
def precision (L n : ℕ) : ℕ := n+3+2*L
def mesh (L C n : ℕ) : ℕ := 2^(precision L n)*(C+1)

end SymplecticPacking.Effective.ODE
