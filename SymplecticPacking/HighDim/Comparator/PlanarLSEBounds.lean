import SymplecticPacking.HighDim.Comparator.PlanarGen

/-!
# Derivative bounds for the planar log-sum-exp potential

The derivatives are computed from exponential moments. These estimates are uniform
in the intercepts and depend only on the common slope bound and temperature.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.LSE

open Set Real
open scoped ContDiff

/-- Exponential moment of order `r` of the slopes. -/
def moment (l : List (ℝ × ℝ)) (c : ℝ) (r : ℕ) (v : ℝ) : ℝ :=
  (l.map fun p => p.2 ^ r * Real.exp (c * (p.1 + p.2 * v))).sum

/-- The scalar log-sum-exp potential. -/
def potential (l : List (ℝ × ℝ)) (c v : ℝ) : ℝ := c⁻¹ * Real.log (moment l c 0 v)

theorem moment_smooth (l : List (ℝ × ℝ)) (c : ℝ) (r : ℕ) :
    ContDiff ℝ ∞ (moment l c r) := by
  change ContDiff ℝ ∞ (fun v => (l.map fun p => p.2 ^ r * Real.exp (c * (p.1 + p.2 * v))).sum)
  induction l with
  | nil => simpa [moment] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  | cons p l ih =>
    simpa only [List.map_cons, List.sum_cons, Function.comp_apply, id_eq] using
      (contDiff_const.mul (Real.contDiff_exp.comp
        (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_id))))).add ih

theorem moment_zero_pos {l : List (ℝ × ℝ)} (hl : l ≠ []) (c v : ℝ) :
    0 < moment l c 0 v := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hl
  have hh := List.single_le_sum (l := l.map fun p => Real.exp (c * (p.1 + p.2 * v)))
    (fun a ha => by obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact (Real.exp_pos _).le)
    (Real.exp (c * (p.1 + p.2 * v))) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simpa [moment] using (Real.exp_pos (c * (p.1 + p.2 * v))).trans_le hh

theorem moment_hasDerivAt (l : List (ℝ × ℝ)) (c : ℝ) (r : ℕ) (v : ℝ) :
    HasDerivAt (moment l c r) (c * moment l c (r + 1) v) v := by
  induction l with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (c * 0) v
    simpa using (hasDerivAt_const v (0 : ℝ))
  | cons p l ih =>
    have he := ((hasDerivAt_const v c).mul
      ((hasDerivAt_const v p.1).add ((hasDerivAt_const v p.2).mul (hasDerivAt_id v)))).exp
    have hh := ((hasDerivAt_const v (p.2 ^ r)).mul he).add ih
    convert hh using 1
    · funext x
      simp [moment]
    · simp only [moment, List.map_cons, List.sum_cons, pow_succ, Pi.add_apply,
        Pi.mul_apply, id_eq, zero_mul, mul_one, zero_add]
      ring

theorem potential_smooth {l : List (ℝ × ℝ)} (hl : l ≠ []) (c : ℝ) :
    ContDiff ℝ ∞ (potential l c) :=
  contDiff_const.mul ((moment_smooth l c 0).log fun v => (moment_zero_pos hl c v).ne')

theorem potential_hasDerivAt {l : List (ℝ × ℝ)} (hl : l ≠ []) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    HasDerivAt (potential l c) (moment l c 1 v / moment l c 0 v) v := by
  have h := (moment_hasDerivAt l c 0 v).log (moment_zero_pos hl c v).ne'
  convert (hasDerivAt_const v c⁻¹).mul h using 1
  · rfl
  · simp only [zero_mul, zero_add]
    field_simp

theorem potential_deriv {l : List (ℝ × ℝ)} (hl : l ≠ []) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    deriv (potential l c) v = moment l c 1 v / moment l c 0 v :=
  (potential_hasDerivAt hl hc v).deriv

/-- Every exponential moment is bounded by the corresponding slope power. -/
theorem moment_abs_le {l : List (ℝ × ℝ)} {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ p ∈ l, |p.2| ≤ L) (c : ℝ) (r : ℕ) (v : ℝ) :
    |moment l c r v| ≤ L ^ r * moment l c 0 v := by
  induction l with
  | nil => simp [moment]
  | cons p l ih =>
    have hp := hb p (by simp)
    have hi := ih (fun q hq => hb q (by simp [hq]))
    have hterm : |p.2 ^ r * Real.exp (c * (p.1 + p.2 * v))| ≤
        L ^ r * Real.exp (c * (p.1 + p.2 * v)) := by
      rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hp _) (Real.exp_pos _).le
    simp only [moment, List.map_cons, List.sum_cons, pow_zero, one_mul] at *
    exact (abs_add_le _ _).trans (by nlinarith)

/-- The logarithmic potential has the same uniform slope bound as its affine pieces. -/
theorem potential_deriv_abs_le {l : List (ℝ × ℝ)} (hl : l ≠ []) {c L : ℝ}
    (hc : c ≠ 0) (hL : 0 ≤ L) (hb : ∀ p ∈ l, |p.2| ≤ L) (v : ℝ) :
    |deriv (potential l c) v| ≤ L := by
  rw [potential_deriv hl hc, abs_div, abs_of_pos (moment_zero_pos hl c v)]
  rw [div_le_iff₀ (moment_zero_pos hl c v)]
  simpa only [pow_one] using moment_abs_le hL hb c 1 v

/-- Normalised exponential moment. -/
def ratio (l : List (ℝ × ℝ)) (c : ℝ) (r : ℕ) (v : ℝ) : ℝ :=
  moment l c r v / moment l c 0 v

theorem ratio_abs_le {l : List (ℝ × ℝ)} (hl : l ≠ []) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ p ∈ l, |p.2| ≤ L) (c : ℝ) (r : ℕ) (v : ℝ) :
    |ratio l c r v| ≤ L ^ r := by
  unfold ratio
  rw [abs_div, abs_of_pos (moment_zero_pos hl c v), div_le_iff₀ (moment_zero_pos hl c v)]
  exact moment_abs_le hL hb c r v

theorem ratio_hasDerivAt {l : List (ℝ × ℝ)} (hl : l ≠ []) (c : ℝ) (r : ℕ) (v : ℝ) :
    HasDerivAt (ratio l c r) (c * (ratio l c (r + 1) v - ratio l c r v * ratio l c 1 v)) v := by
  have hh := (moment_hasDerivAt l c r v).div (moment_hasDerivAt l c 0 v)
    (moment_zero_pos hl c v).ne'
  convert hh using 1
  · rfl
  · dsimp only [ratio]
    field_simp
    <;> ring

theorem centered_square (l : List (ℝ × ℝ)) (c v a : ℝ) :
    (l.map fun p => (p.2 - a) ^ 2 * Real.exp (c * (p.1 + p.2 * v))).sum =
      moment l c 2 v - 2 * a * moment l c 1 v + a ^ 2 * moment l c 0 v := by
  induction l with
  | nil => simp [moment]
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, moment, pow_one, pow_zero, one_mul] at *
    rw [ih]
    ring

theorem variance_nonneg {l : List (ℝ × ℝ)} (hl : l ≠ []) (c v : ℝ) :
    0 ≤ ratio l c 2 v - ratio l c 1 v ^ 2 := by
  have hs : 0 ≤ (l.map fun p => (p.2 - ratio l c 1 v) ^ 2 *
      Real.exp (c * (p.1 + p.2 * v))).sum :=
    List.sum_nonneg (by
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      positivity)
  rw [centered_square] at hs
  have h0 := moment_zero_pos hl c v
  have heq : moment l c 2 v - 2 * ratio l c 1 v * moment l c 1 v +
      ratio l c 1 v ^ 2 * moment l c 0 v =
      moment l c 0 v * (ratio l c 2 v - ratio l c 1 v ^ 2) := by
    unfold ratio
    field_simp
    <;> ring
  rw [heq] at hs
  exact nonneg_of_mul_nonneg_right hs h0

theorem potential_second {l : List (ℝ × ℝ)} (hl : l ≠ []) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    deriv (deriv (potential l c)) v = c * (ratio l c 2 v - ratio l c 1 v ^ 2) := by
  have hf : deriv (potential l c) = ratio l c 1 := funext (potential_deriv hl hc)
  rw [hf]
  simpa [pow_two] using (ratio_hasDerivAt hl c 1 v).deriv

theorem potential_second_bounds {l : List (ℝ × ℝ)} (hl : l ≠ []) {c L : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hb : ∀ p ∈ l, |p.2| ≤ L) (v : ℝ) :
    0 ≤ deriv (deriv (potential l c)) v ∧
      deriv (deriv (potential l c)) v ≤ c * L ^ 2 := by
  rw [potential_second hl hc.ne']
  constructor
  · exact mul_nonneg hc.le (variance_nonneg hl c v)
  · have hb2 := (le_abs_self (ratio l c 2 v)).trans (ratio_abs_le hl hL hb c 2 v)
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (ratio l c 1 v)]) hc.le

theorem potential_third {l : List (ℝ × ℝ)} (hl : l ≠ []) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    deriv (deriv (deriv (potential l c))) v =
      c ^ 2 * (ratio l c 3 v - 3 * ratio l c 2 v * ratio l c 1 v + 2 * ratio l c 1 v ^ 3) := by
  have hf : deriv (deriv (potential l c)) =
      fun x => c * (ratio l c 2 x - ratio l c 1 x ^ 2) := funext (potential_second hl hc)
  rw [hf]
  have hh := (hasDerivAt_const v c).mul
    ((ratio_hasDerivAt hl c 2 v).sub ((ratio_hasDerivAt hl c 1 v).pow 2))
  convert hh.deriv using 1
  ring

theorem potential_third_abs_le {l : List (ℝ × ℝ)} (hl : l ≠ []) {c L : ℝ}
    (hc : c ≠ 0) (hL : 0 ≤ L) (hb : ∀ p ∈ l, |p.2| ≤ L) (v : ℝ) :
    |deriv (deriv (deriv (potential l c))) v| ≤ 8 * c ^ 2 * L ^ 3 := by
  rw [potential_third hl hc, abs_mul, abs_of_nonneg (sq_nonneg c)]
  have h1 := ratio_abs_le hl hL hb c 1 v
  have h2 := ratio_abs_le hl hL hb c 2 v
  have h3 := ratio_abs_le hl hL hb c 3 v
  simp only [pow_one] at h1
  have h21 : |ratio l c 2 v * ratio l c 1 v| ≤ L ^ 3 := by
    rw [abs_mul]
    have := mul_le_mul h2 h1 (abs_nonneg _) (sq_nonneg L)
    nlinarith
  have h13 : |ratio l c 1 v ^ 3| ≤ L ^ 3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 3
  have hab : |ratio l c 3 v - 3 * ratio l c 2 v * ratio l c 1 v| ≤
      |ratio l c 3 v| + |3 * ratio l c 2 v * ratio l c 1 v| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (ratio l c 3 v) (-(3 * ratio l c 2 v * ratio l c 1 v))
  have ht := (abs_add_le (ratio l c 3 v - 3 * ratio l c 2 v * ratio l c 1 v)
    (2 * ratio l c 1 v ^ 3)).trans (add_le_add hab (le_refl |2 * ratio l c 1 v ^ 3|))
  have hmul : |3 * ratio l c 2 v * ratio l c 1 v| = 3 * |ratio l c 2 v * ratio l c 1 v| := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hmul2 : |2 * ratio l c 1 v ^ 3| = 2 * |ratio l c 1 v ^ 3| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hmul, hmul2] at ht
  have hsum : |ratio l c 3 v - 3 * ratio l c 2 v * ratio l c 1 v + 2 * ratio l c 1 v ^ 3| ≤
      8 * L ^ 3 := by nlinarith [pow_nonneg hL 3]
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg c)]

end SymplecticPacking.HighDim.PlanarGen.LSE

namespace SymplecticPacking.HighDim.PlanarGen.Input

open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)

theorem U0_eq_lse_potential : D.U0 y = LSE.potential (D.pieces y) D.clse := by
  funext v
  simp [U0, LSE.potential, LSE.moment]

theorem U0_smooth (hne : D.pieces y ≠ []) : ContDiff ℝ ∞ (D.U0 y) := by
  rw [D.U0_eq_lse_potential y]
  exact LSE.potential_smooth hne _

theorem U0_deriv_abs_le (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) (v : ℝ) : |deriv (D.U0 y) v| ≤ D.L := by
  rw [D.U0_eq_lse_potential y]
  exact LSE.potential_deriv_abs_le hne (clse_pos hξ).ne' hL hb v

theorem U0_second_bounds (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) (v : ℝ) :
    0 ≤ deriv (deriv (D.U0 y)) v ∧ deriv (deriv (D.U0 y)) v ≤ D.clse * D.L ^ 2 := by
  rw [D.U0_eq_lse_potential y]
  exact LSE.potential_second_bounds hne (clse_pos hξ) hL hb v

theorem U0_third_abs_le (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) (v : ℝ) :
    |deriv (deriv (deriv (D.U0 y))) v| ≤ 8 * D.clse ^ 2 * D.L ^ 3 := by
  rw [D.U0_eq_lse_potential y]
  exact LSE.potential_third_abs_le hne (clse_pos hξ).ne' hL hb v

end SymplecticPacking.HighDim.PlanarGen.Input
