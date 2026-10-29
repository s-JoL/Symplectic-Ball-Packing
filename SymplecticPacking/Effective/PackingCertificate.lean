import SymplecticPacking.Effective.ODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic

/-!
# Finite Euler certificates for open-target containment

The checks in this file are finite rational inequalities.  In particular, none of
them asks whether a Hamiltonian satisfies `PackingSpec`.  The analytic statements
below relate the checked rational Euler table to a differential equation.

The all-time bound is useful with a clipped polynomial field: if every Euler box
lies strictly inside the plateau of the output cutoff, the clipped trajectory is
an integral curve of the output Hamiltonian throughout the whole time interval.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate

open Set
open scoped Topology NNReal
set_option maxHeartbeats 1000000

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euler error at *each* grid point, including uncertain initial data. -/
theorem grid_error {F : ℝ → E → E} {γ : ℝ → E} {A L M : ℝ}
    (B : ODE.Bounds F γ A L M) {N : ℕ} (hN : 0 < N)
    (x v : ℕ → E) {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ i < N, x (i+1) = x i + (1/(N:ℝ)) • v i)
    (hvalue : ∀ i < N, ‖v i - F (ODE.gridTime N i) (x i)‖ ≤ η)
    {i : ℕ} (hi : i ≤ N) :
    ‖x i - γ (ODE.gridTime N i)‖ ≤
      (‖x 0 - γ 0‖ + η + (A+L*M)/(N:ℝ))*Real.exp L := by
  let e : ℕ → ℝ := fun j => ‖x j - γ (ODE.gridTime N j)‖
  let a : ℝ := 1+L/(N:ℝ)
  let b : ℝ := η/(N:ℝ)+(A+L*M)/(N:ℝ)^2
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ A+L*M := add_nonneg B.time_nonneg
    (mul_nonneg B.space_nonneg B.speed_nonneg)
  have ha : 1 ≤ a := by
    have hp := div_nonneg B.space_nonneg hN'.le
    dsimp only [a]
    linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hrec : ∀ j < N, e (j+1) ≤ a*e j+b := fun j hj =>
    ODE.step_error B hN hj (hstep j hj) (hvalue j hj)
  have hfin := ODE.finite_error_bound (e := e) ha hb (norm_nonneg _) hrec i hi
  have hpow : a^i ≤ Real.exp L := by
    have hbase : a ≤ Real.exp (L/(N:ℝ)) := by
      simpa only [a, add_comm] using Real.add_one_le_exp (L/(N:ℝ))
    calc
      a^i ≤ a^N := pow_le_pow_right₀ ha hi
      _ ≤ (Real.exp (L/(N:ℝ)))^N :=
        pow_le_pow_left₀ (by dsimp [a]; positivity) hbase N
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hbi : (i:ℝ)*b ≤ (N:ℝ)*b := mul_le_mul_of_nonneg_right
    (by exact_mod_cast hi) hb
  have hcoef : 0 ≤ e 0+(i:ℝ)*b := by dsimp [e]; positivity
  have he0 : e 0 = ‖x 0-γ 0‖ := by simp [e, ODE.gridTime]
  have hNb : (N:ℝ)*b = η+(A+L*M)/(N:ℝ) := by
    dsimp only [b]; field_simp <;> ring
  calc
    _ ≤ (e 0+(i:ℝ)*b)*Real.exp L :=
      hfin.trans (mul_le_mul_of_nonneg_left hpow hcoef)
    _ ≤ (e 0+(N:ℝ)*b)*Real.exp L := by gcongr
    _ = _ := by rw [he0, hNb]; ring

/-- A grid cell covering any time in `[0,1]`; the last grid point is allowed. -/
theorem exists_time_cell {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ i ≤ N, ODE.gridTime N i ≤ t ∧
      t - ODE.gridTime N i ≤ 1/(N:ℝ) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨⌊t*(N:ℝ)⌋₊, ?_, ?_, ?_⟩
  · apply Nat.floor_le_of_le
    nlinarith [ht.2]
  · apply (div_le_iff₀ hN').mpr
    exact Nat.floor_le (mul_nonneg ht.1 hN'.le)
  · have hh := Nat.lt_floor_add_one (t*(N:ℝ))
    apply (le_div_iff₀ hN').mpr
    dsimp only [ODE.gridTime]
    have hcancel : ((⌊t*(N:ℝ)⌋₊:ℝ)/(N:ℝ))*(N:ℝ) = (⌊t*(N:ℝ)⌋₊:ℝ) :=
      div_mul_cancel₀ _ hN'.ne'
    nlinarith

/-- Between grid points the trajectory moves by at most `M/N`. -/
theorem time_error {F : ℝ → E → E} {γ : ℝ → E} {A L M : ℝ}
    (B : ODE.Bounds F γ A L M) {N : ℕ} (hN : 0 < N)
    (x v : ℕ → E) {η ρ : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ i < N, x (i+1) = x i+(1/(N:ℝ)) • v i)
    (hvalue : ∀ i < N, ‖v i-F (ODE.gridTime N i) (x i)‖ ≤ η)
    (hstart : ‖x 0-γ 0‖ ≤ ρ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ i ≤ N, ‖γ t-x i‖ ≤
      (ρ+η+(A+L*M)/(N:ℝ))*Real.exp L+M/(N:ℝ) := by
  obtain ⟨i, hi, hit, hti⟩ := exists_time_cell hN ht
  have hg := grid_error B hN x v hη hstep hvalue hi
  have hv := ODE.solution_increment B.derivative B.speed (ODE.gridTime_mem hN hi) ht
  have habs : |t-ODE.gridTime N i| = t-ODE.gridTime N i :=
    abs_of_nonneg (sub_nonneg.mpr hit)
  rw [habs] at hv
  refine ⟨i, hi, ?_⟩
  calc
    ‖γ t-x i‖ ≤ ‖γ t-γ (ODE.gridTime N i)‖+‖γ (ODE.gridTime N i)-x i‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M*(t-ODE.gridTime N i)+
        (‖x 0-γ 0‖+η+(A+L*M)/(N:ℝ))*Real.exp L := by
      rw [norm_sub_rev (γ (ODE.gridTime N i)) (x i)]
      exact add_le_add hv hg
    _ ≤ M*(1/(N:ℝ))+(ρ+η+(A+L*M)/(N:ℝ))*Real.exp L := by
      exact add_le_add (mul_le_mul_of_nonneg_left hti B.speed_nonneg)
        (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
    _ = _ := by ring

/-- Rational tube radius; `exp L ≤ 4^L` leaves only rational arithmetic in checks. -/
def error (A L M N : ℕ) (ρ η : ℚ) : ℚ :=
  (ρ+η+((A:ℚ)+L*M)/N)*4^L+(M:ℚ)/N

theorem error_nonneg (A L M N : ℕ) {ρ η : ℚ} (hρ : 0 ≤ ρ) (hη : 0 ≤ η) :
    0 ≤ error A L M N ρ η := by unfold error; positivity

theorem exp_le_four_pow (L : ℕ) : Real.exp (L:ℝ) ≤ (4:ℝ)^L := by
  have h3 : Real.exp 1 ≤ (4:ℝ) := by linarith [Real.exp_one_lt_three]
  calc
    _ = (Real.exp 1)^L := by rw [← Real.exp_nat_mul]; simp
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg 1) h3 L

theorem error_bound {A L M N : ℕ} {ρ η : ℚ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) :
    ((ρ:ℝ)+η+((A:ℝ)+L*M)/N)*Real.exp (L:ℝ)+(M:ℝ)/N ≤
      (error A L M N ρ η:ℝ) := by
  have hρ' : (0:ℝ) ≤ ρ := by exact_mod_cast hρ
  have hη' : (0:ℝ) ≤ η := by exact_mod_cast hη
  have he := mul_le_mul_of_nonneg_left (exp_le_four_pow L)
    (show 0 ≤ (ρ:ℝ)+η+((A:ℝ)+L*M)/N by positivity)
  simp only [error, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat]
  linarith

/-- Initial source-cell uncertainty and field perturbation are both paid. This
all-time estimate is also the transfer used in the certificate nonemptiness proof. -/
theorem flow_error_with_initial {F G : ℝ → E → E} {L : ℝ≥0} {ρ η : ℝ}
    (hF : ∀ t, LipschitzWith L (F t))
    (hη : ∀ t x, dist (G t x) (F t x) ≤ η)
    {y z : ℝ → E} (hy : IsIntegralCurveOn y F (Icc 0 1))
    (hz : IsIntegralCurveOn z G (Icc 0 1)) (h0 : dist (z 0) (y 0) ≤ ρ) :
    ∀ t ∈ Icc (0:ℝ) 1, dist (z t) (y t) ≤ gronwallBound ρ L η t := by
  have hIci : ∀ t ∈ Ico (0:ℝ) 1, Icc (0:ℝ) 1 ∈ nhdsWithin t (Ici t) := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have h := dist_le_of_approx_trajectories_ODE (v := F) (K := L) (δ := ρ)
    (εf := η) (εg := 0) (f := z) (g := y)
    (f' := fun t => G t (z t)) (g' := fun t => F t (y t)) hF
    (fun t ht => (hz t ht).continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun t _ => hη t (z t))
    (fun t ht => (hy t ht).continuousWithinAt)
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun t _ => by rw [dist_self]) h0
  simpa only [add_zero, sub_zero] using h

/-- The finite plateau test inspects only the rational Euler table. -/
def plateauCheck {d : ℕ} (N : ℕ) (x : ℕ → Fin d → ℚ) (e R : ℚ) : Bool :=
  decide (∀ i : Fin (N+1), ∀ j, |x i j|+e < R)

/-- A successful rational plateau test implies a strict spatial bound at every
real time for every initial value covered by the paid initial error. -/
theorem plateauCheck_sound {d A L M N : ℕ} {F : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    {γ : ℝ → Fin d → ℝ} (B : ODE.Bounds F γ (A:ℝ) (L:ℝ) (M:ℝ))
    (hN : 0 < N) (x v : ℕ → Fin d → ℚ) {ρ η R : ℚ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hstep : ∀ i < N, ODE.castVector (x (i+1)) = ODE.castVector (x i)+
      (1/(N:ℝ)) • ODE.castVector (v i))
    (hvalue : ∀ i < N, ‖ODE.castVector (v i)-F (ODE.gridTime N i)
      (ODE.castVector (x i))‖ ≤ (η:ℝ))
    (hstart : ‖ODE.castVector (x 0)-γ 0‖ ≤ (ρ:ℝ))
    (hc : plateauCheck N x (error A L M N ρ η) R = true)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (j : Fin d) : |γ t j| < (R:ℝ) := by
  obtain ⟨i, hi, hdist⟩ := time_error B hN
    (fun i => ODE.castVector (x i)) (fun i => ODE.castVector (v i))
    (by exact_mod_cast hη) hstep hvalue hstart ht
  have hcoord := norm_le_pi_norm (γ t-ODE.castVector (x i)) j
  have hdist' := hdist.trans (error_bound hρ hη)
  have hc' : ∀ i : Fin (N+1), ∀ j, |x i j|+error A L M N ρ η < R :=
    of_decide_eq_true hc
  have hr : |(x i j:ℝ)|+(error A L M N ρ η:ℝ) < (R:ℝ) := by
    exact_mod_cast hc' ⟨i, by omega⟩ j
  have hcoord' : |γ t j-(x i j:ℝ)| ≤ (error A L M N ρ η:ℝ) := by
    simpa only [Pi.sub_apply, ODE.castVector, Real.norm_eq_abs] using hcoord.trans hdist'
  calc
    |γ t j| ≤ |γ t j-(x i j:ℝ)|+|(x i j:ℝ)| := by
      simpa only [sub_add_cancel, Real.norm_eq_abs] using
        norm_add_le (γ t j-(x i j:ℝ)) (x i j:ℝ)
    _ < (R:ℝ) := by linarith

end SymplecticPacking.Effective.PackingCertificate
