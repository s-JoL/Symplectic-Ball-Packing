import SymplecticPacking.BranchLargeHigh.Coupled
import SymplecticPacking.Strip.Map

/-!
# The slit-shell map

Paper `lem:lrg-slit`, supplement `lem:two-slit` (
formula (6)). For `δ > 0` let `x + iT = Ψ_strip(z)` be the strip map of `Strip/Map.lean`
(`0 < x < u + δ/2`, `0 < T < 1`, `dx ∧ dT = ω_fib`). The slit-shell map is

  `y₀ = e^{-2πiT} √([1 - x - (1-u) μ]/π)`,   `y_i = e^{-2πiT} √(1-u) ξ_i`  (`i ≥ 1`).

It is smooth on `{u < 1, 1 - x - (1-u)μ > 0}` (including `z = 0`), injective there, has exact
capacity `π|y|² = 1 - x`, and pulls `ω₀` back to the coupled form `Ω` (`shell_pullback`,
`ShellDeriv.lean`).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Set
open scoped ContDiff

variable {m : ℕ}

/-- The strip point `x + iT = Ψ_strip(z₀)`. -/
def stripPt (δ : ℝ) (y : E (m + 1)) : ℂ := Strip.psiStrip δ (zc y 0)

/-- The new fibre moment `x`. -/
def xs (δ : ℝ) (y : E (m + 1)) : ℝ := (stripPt δ y).re

/-- The angle `T ∈ (0, 1)`. -/
def Ts (δ : ℝ) (y : E (m + 1)) : ℝ := (stripPt δ y).im

/-- The phase `e^{-2πiT}`. -/
def phase (δ : ℝ) (y : E (m + 1)) : ℂ := Complex.exp (((-(2 * Real.pi * Ts δ y) : ℝ) : ℂ) * Complex.I)

/-- The radicand `[1 - x - (1-u) μ]/π` of the first shell coordinate. -/
def radicand (δ : ℝ) (y : E (m + 1)) : ℝ :=
  (1 - xs δ y - (1 - fibMoment y) * baseMoment y) / Real.pi

/-- The complex coordinates of the slit-shell map. -/
def shellPhase (δ : ℝ) (y : E (m + 1)) : Fin (m + 1) → ℂ :=
  Fin.cons (phase δ y * (Real.sqrt (radicand δ y) : ℂ))
    (fun i => phase δ y * (Real.sqrt (1 - fibMoment y) : ℂ) * zc y i.succ)

/-- **The slit-shell map** (`lem:lrg-slit`, formula (6)). -/
def shell (δ : ℝ) (y : E (m + 1)) : E (m + 1) := ofPhase (shellPhase δ y)

/-- Its natural domain `{u < 1, radicand > 0}`. -/
def shellDomain (δ : ℝ) : Set (E (m + 1)) := {y | fibMoment y < 1 ∧ 0 < radicand δ y}

section
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

lemma stripPt_contDiff : ContDiff ℝ ∞ (stripPt (m := m) δ) :=
  (Strip.psiStrip_smooth hδ).comp (zc_contDiff 0)

lemma xs_pos (y : E (m + 1)) : 0 < xs δ y := Strip.psiStrip_x_pos hδ _

lemma xs_lt (y : E (m + 1)) : xs δ y < fibMoment y + δ / 2 := by
  have := Strip.psiStrip_x_lt hδ (zc y 0)
  rw [fibMoment, Complex.normSq_eq_norm_sq]; exact this

lemma Ts_mem (y : E (m + 1)) : 0 < Ts δ y ∧ Ts δ y < 1 :=
  ⟨(Strip.psiStrip_mem hδ _).2.1, (Strip.psiStrip_mem hδ _).2.2⟩

/-- Positivity of the radicand from the compact bounds `u ≤ h`, `μ ≤ M` and `δ/2 < (1-h)(1-M)`. -/
lemma radicand_pos_of_bounds {h M : ℝ} (hM : M ≤ 1) (hh : h ≤ 1)
    (hδh : δ / 2 < (1 - h) * (1 - M)) {y : E (m + 1)} (hu : fibMoment y ≤ h)
    (hμ : baseMoment y ≤ M) : 0 < radicand δ y := by
  unfold radicand
  apply div_pos _ Real.pi_pos
  have hx := xs_lt hδ y
  have h1 : (1 - h) * (1 - M) ≤ (1 - fibMoment y) * (1 - baseMoment y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  nlinarith

end

lemma phase_normSq (δ : ℝ) (y : E (m + 1)) : Complex.normSq (phase δ y) = 1 := by
  rw [phase, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num

lemma phase_ne_zero (δ : ℝ) (y : E (m + 1)) : phase δ y ≠ 0 := Complex.exp_ne_zero _

@[simp] lemma zc_shell_zero (δ : ℝ) (y : E (m + 1)) :
    zc (shell δ y) 0 = phase δ y * (Real.sqrt (radicand δ y) : ℂ) := by
  simp [shell, shellPhase]

@[simp] lemma zc_shell_succ (δ : ℝ) (y : E (m + 1)) (i : Fin m) :
    zc (shell δ y) i.succ = phase δ y * (Real.sqrt (1 - fibMoment y) : ℂ) * zc y i.succ := by
  simp [shell, shellPhase]

/-- **Exact capacity** `π|shell(y)|² = 1 - x`. -/
lemma shell_capacity (δ : ℝ) {y : E (m + 1)} (hu : fibMoment y ≤ 1) (hr : 0 ≤ radicand δ y) :
    Real.pi * ‖shell δ y‖ ^ 2 = 1 - xs δ y := by
  rw [norm_sq_eq, Fin.sum_univ_succ]
  simp only [zc_shell_zero, zc_shell_succ, Complex.normSq_mul, phase_normSq, Complex.normSq_ofReal,
    one_mul]
  rw [Real.mul_self_sqrt hr, Real.mul_self_sqrt (by linarith), ← Finset.mul_sum]
  have hπ := Real.pi_pos
  unfold radicand
  have hb : Real.pi * ∑ i : Fin m, Complex.normSq (zc y i.succ) = baseMoment y := rfl
  field_simp
  nlinarith [hb]

/-- **Smoothness** of the slit-shell map on its domain, including the original axis `z₀ = 0`. -/
lemma shell_contDiffAt {δ : ℝ} (hδ : 0 < δ) {y : E (m + 1)} (hy : y ∈ shellDomain δ) :
    ContDiffAt ℝ ∞ (shell δ) y := by
  have hT : ContDiff ℝ ∞ (Ts (m := m) δ) :=
    Complex.imCLM.contDiff.comp (stripPt_contDiff hδ)
  have hx : ContDiff ℝ ∞ (xs (m := m) δ) :=
    Complex.reCLM.contDiff.comp (stripPt_contDiff hδ)
  have hph : ContDiff ℝ ∞ (phase (m := m) δ) := by
    unfold phase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hT).neg).mul
      contDiff_const).cexp
  have hrad : ContDiff ℝ ∞ (radicand (m := m) δ) := by
    unfold radicand
    exact ((contDiff_const.sub hx).sub
      ((contDiff_const.sub fibMoment_contDiff).mul baseMoment_contDiff)).div_const _
  have h0 : ContDiffAt ℝ ∞ (fun y => (Real.sqrt (radicand δ y) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (hrad.contDiffAt.sqrt (ne_of_gt hy.2))
  have h1 : ContDiffAt ℝ ∞ (fun y : E (m + 1) => (Real.sqrt (1 - fibMoment y) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y
      ((contDiff_const.sub fibMoment_contDiff).contDiffAt.sqrt (by linarith [hy.1]))
  have hS : ContDiffAt ℝ ∞ (shellPhase δ) y := by
    rw [contDiffAt_pi]
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [shellPhase, Fin.cons_zero]
      exact hph.contDiffAt.mul h0
    · simp only [shellPhase, Fin.cons_succ]
      exact (hph.contDiffAt.mul h1).mul (zc_contDiff _).contDiffAt
  exact ofPhase_contDiff.contDiffAt.comp y hS

/-- **Injectivity** of the slit-shell map on its domain: `x = 1 - π|y|²`, then `T` from the phase
of the (nonzero) first coordinate, then `z₀ = Ψ_strip⁻¹(x + iT)`, then `ξ`. -/
lemma shell_injOn {δ : ℝ} (hδ : 0 < δ) : InjOn (shell (m := m) δ) (shellDomain δ) := by
  intro y hy y' hy' h
  have hc := shell_capacity δ hy.1.le hy.2.le
  have hc' := shell_capacity δ hy'.1.le hy'.2.le
  rw [h] at hc
  have hxx : xs δ y = xs δ y' := by linarith
  -- first coordinates
  have h0 := congrArg (fun p => zc p 0) h
  simp only [zc_shell_zero] at h0
  have hn := congrArg Complex.normSq h0
  simp only [Complex.normSq_mul, phase_normSq, Complex.normSq_ofReal, one_mul] at hn
  have hs : Real.sqrt (radicand δ y) = Real.sqrt (radicand δ y') := by
    have := Real.sqrt_pos.2 hy.2
    have := Real.sqrt_pos.2 hy'.2
    nlinarith
  have hsne : ((Real.sqrt (radicand δ y) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 hy.2))
  rw [hs] at h0 hsne
  have hph : phase δ y = phase δ y' := mul_right_cancel₀ hsne h0
  have hTT : Ts δ y = Ts δ y' := by
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 hph
    have him := congrArg Complex.im hk
    simp at him
    have hk' : Ts δ y' - Ts δ y = k := by
      have := Real.pi_pos
      field_simp at him
      linarith
    have h1 := Ts_mem hδ y
    have h2 := Ts_mem hδ y'
    have hk0 : k = 0 := by
      have hlt : (k : ℝ) < 1 := by linarith
      have hgt : (-1 : ℝ) < k := by linarith
      have : k < 1 := by exact_mod_cast hlt
      have : -1 < k := by exact_mod_cast hgt
      omega
    rw [hk0] at hk'; simp at hk'; linarith
  have hst : stripPt δ y = stripPt δ y' := Complex.ext hxx hTT
  have hz : zc y 0 = zc y' 0 :=
    (Strip.psiStrip_bijOn hδ).injOn (mem_univ _) (mem_univ _) hst
  have hu : fibMoment y = fibMoment y' := by simp [fibMoment, hz]
  apply eq_of_zc_eq
  intro j
  refine Fin.cases hz (fun i => ?_) j
  have hi := congrArg (fun p => zc p i.succ) h
  simp only [zc_shell_succ, hph, hu] at hi
  have hne : phase δ y' * ((Real.sqrt (1 - fibMoment y') : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (phase_ne_zero _ _)
      (Complex.ofReal_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 (by linarith [hy'.1]))))
  exact mul_left_cancel₀ hne hi

end SymplecticPacking.BranchLargeHigh
