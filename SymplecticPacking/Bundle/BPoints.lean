import SymplecticPacking.Bundle.Theta

/-!
# The three points of the curve on `Z₀ = 0`

`sec:fer` (`lem:fer-bpoints`): the three points of the curve on `Z₀ = 0`.

In torus coordinates `(u, v)` (`z = u + τ v`), `Zunit u v 0 = 0` exactly at
`b₁ = (0,0)`, `b₂ = (1/3, 2/3)`, `b₃ = (2/3, 1/3)` modulo `ℤ²`.

Proof: `Z₀ = 2 cF π² P(πz)`; at the lattice `θ₁(πz) = 0` and `P` has the factor `θ₁`; off the
lattice `Z₀ = θ³ · 2 cF ℘(z)`. The zeros of `℘` are the two fixed points `z₂ ≡ τ z₂`,
`z₃ ≡ -z₂` of the rotation (homogeneity `℘(ζ₆ z) = ζ₆⁻² ℘(z)`), and there are no others by
`℘'² = -g₃` at a zero of `℘` plus injectivity of `(℘, ℘')` (`wp_injective`).
-/

noncomputable section

namespace SymplecticPacking.Bundle

open _root_.Complex PeriodPair Set
open scoped Real

/-- The three points `b₁, b₂, b₃` in torus coordinates. -/
def bpoints : Fin 3 → ℝ × ℝ := ![(0, 0), (1/3, 2/3), (2/3, 1/3)]

/-! ### Homogeneity of `℘` under the hexagonal rotation -/

lemma wp_zeta6_mul (z : ℂ) : ℘[hexPair] (zeta6 * z) = (zeta6 ^ 2)⁻¹ * ℘[hexPair] z := by
  unfold PeriodPair.weierstrassP
  rw [← tsum_mul_left, ← rotLattice.tsum_eq]
  congr 1; funext l
  simp only [rotLattice, Equiv.coe_fn_mk]
  have h0 := zeta6_ne_zero
  rw [show zeta6 * z - zeta6 * (l : ℂ) = zeta6 * (z - l) by ring]
  simp only [mul_pow, one_div, mul_inv]
  ring

lemma wp_tau_mul (z : ℂ) : ℘[hexPair] (tau * z) = (tau ^ 2)⁻¹ * ℘[hexPair] z := by
  have ht : tau = zeta6 * zeta6 := by rw [← sq, zeta6_sq]; rfl
  rw [ht, mul_assoc, wp_zeta6_mul, wp_zeta6_mul, ← mul_assoc, ← mul_inv]
  congr 2; ring

lemma tau_sq : tau ^ 2 = -1 - tau := by
  have h := zeta6_sq
  simp only [tau]; linear_combination h

/-! ### Lattice membership in torus coordinates -/

lemma torusZ_sub_mem_iff (u v a b : ℝ) :
    torusZ u v - torusZ a b ∈ hexPair.lattice ↔ ∃ m n : ℤ, u = a + m ∧ v = b + n := by
  rw [mem_lattice_iff]
  have hs : (0 : ℝ) < Real.sqrt 3 := by positivity
  constructor
  · rintro ⟨m, n, h⟩
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [torusZ, tau_re, tau_im] at him hre
    have hvn : v - b = n := by
      have : (v - b - n) * (Real.sqrt 3 / 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · linarith
      · linarith
    refine ⟨m, n, ?_, by linarith⟩
    rw [← hvn] at hre; linarith
  · rintro ⟨m, n, rfl, rfl⟩
    refine ⟨m, n, ?_⟩
    simp only [torusZ]; push_cast; ring

/-- The fixed point `z₂ = 1/3 + 2τ/3`. -/
def z2 : ℂ := torusZ (1/3) (2/3)

lemma z2_notMem : z2 ∉ hexPair.lattice := by
  intro h
  have : torusZ (1/3) (2/3) - torusZ 0 0 ∈ hexPair.lattice := by
    simpa [z2, torusZ] using h
  obtain ⟨m, n, hm, -⟩ := (torusZ_sub_mem_iff _ _ _ _).mp this
  have h1 : (0 : ℝ) < m := by linarith
  have h2 : (m : ℝ) < 1 := by linarith
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

lemma wp_z2 : ℘[hexPair] z2 = 0 := by
  have hfix : tau * z2 = z2 + (-1 + -1 * tau) := by
    simp only [z2, torusZ]; push_cast
    linear_combination (2 / 3 : ℂ) * tau_sq
  have hl : ((-1 : ℂ) + -1 * tau) ∈ hexPair.lattice :=
    (mem_lattice_iff _).mpr ⟨-1, -1, by push_cast; ring⟩
  have h1 : ℘[hexPair] (tau * z2) = ℘[hexPair] z2 := by
    rw [hfix]; exact hexPair.weierstrassP_add_coe z2 ⟨_, hl⟩
  rw [wp_tau_mul] at h1
  have hne : (tau ^ 2)⁻¹ ≠ 1 := by
    intro h
    have h' : tau ^ 2 = 1 := inv_eq_one.mp h
    rw [tau_sq] at h'
    have := congrArg Complex.im h'
    simp [tau_im] at this
  have : ((tau ^ 2)⁻¹ - 1) * ℘[hexPair] z2 = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- **Zeros of `℘`**: off the lattice, `℘ z = 0 ↔ z ≡ z₂` or `z ≡ -z₂`. -/
theorem wp_eq_zero_iff {z : ℂ} (hz : z ∉ hexPair.lattice) :
    ℘[hexPair] z = 0 ↔ z - z2 ∈ hexPair.lattice ∨ z + z2 ∈ hexPair.lattice := by
  constructor
  · intro h0
    have hsq := hex_wp_eq z hz
    have hsq2 := hex_wp_eq z2 z2_notMem
    rw [h0] at hsq; rw [wp_z2] at hsq2
    have : (℘'[hexPair] z - ℘'[hexPair] z2) * (℘'[hexPair] z + ℘'[hexPair] z2) = 0 := by
      linear_combination hsq - hsq2
    rcases mul_eq_zero.mp this with h | h
    · left
      exact wp_injective z z2 hz z2_notMem (by rw [h0, wp_z2]) (sub_eq_zero.mp h)
    · right
      have hn : -z2 ∉ hexPair.lattice := fun hm => z2_notMem (by simpa using neg_mem hm)
      have := wp_injective z (-z2) hz hn (by rw [h0, weierstrassP_neg, wp_z2])
        (by rw [derivWeierstrassP_neg]; linear_combination h)
      simpa using this
  · rintro (h | h)
    · have := hexPair.weierstrassP_add_coe z2 ⟨_, h⟩
      simp only [add_sub_cancel] at this
      rw [this, wp_z2]
    · have := hexPair.weierstrassP_add_coe (-z2) ⟨_, h⟩
      rw [show -z2 + (z + z2) = z by ring] at this
      rw [this, weierstrassP_neg, wp_z2]

/-! ### The zero locus of `Z₀` -/

lemma Zunit_zero_eq_zero_iff_Zraw (u v : ℝ) :
    Zunit u v 0 = 0 ↔ Zraw (torusZ u v) 0 = 0 := by
  have hpos := normSq3_pos (Zraw_ne_zero (torusZ u v))
  have hs : (Real.sqrt (normSq3 (Zraw (torusZ u v))) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  simp only [Zunit, Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, hs, false_or]

lemma Zraw_zero_eq_zero_iff (z : ℂ) :
    Zraw z 0 = 0 ↔ z ∈ hexPair.lattice ∨ z - z2 ∈ hexPair.lattice ∨
      z + z2 ∈ hexPair.lattice := by
  by_cases hθ : jacobiTheta1 (π * z) = 0
  · have hz := (jacobiTheta1_pi_mul_eq_zero_iff z).mp hθ
    simp only [hz, true_or, iff_true]
    simp [Zraw, PTheta, hθ]
  · have hz : z ∉ hexPair.lattice := fun h => hθ ((jacobiTheta1_pi_mul_eq_zero_iff z).mpr h)
    rw [Zraw_eq hθ]
    simp only [Pi.smul_apply, smul_eq_mul, torusLift, Matrix.cons_val_zero, mul_eq_zero,
      pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, hθ, false_or,
      cF_ne_zero, hz, wp_eq_zero_iff hz]

/-- **The three points on `Z₀ = 0`** (`lem:fer-bpoints`). -/
theorem Z0_eq_zero_iff (u v : ℝ) :
    Zunit u v 0 = 0 ↔
      ∃ j : Fin 3, ∃ m n : ℤ, u = (bpoints j).1 + m ∧ v = (bpoints j).2 + n := by
  rw [Zunit_zero_eq_zero_iff_Zraw, Zraw_zero_eq_zero_iff]
  have e0 : torusZ u v = torusZ u v - torusZ 0 0 := by simp [torusZ]
  have e2 : torusZ u v - z2 = torusZ u v - torusZ (1/3) (2/3) := rfl
  have e3 : torusZ u v + z2 - (1 + tau) = torusZ u v - torusZ (2/3) (1/3) := by
    simp only [z2, torusZ]; push_cast; ring
  have hl : (1 + tau) ∈ hexPair.lattice := (mem_lattice_iff _).mpr ⟨1, 1, by push_cast; ring⟩
  have e3' : torusZ u v + z2 ∈ hexPair.lattice ↔
      torusZ u v - torusZ (2/3) (1/3) ∈ hexPair.lattice := by
    rw [← e3]
    exact ⟨fun h => sub_mem h hl, fun h => by simpa using add_mem h hl⟩
  rw [e3', e2]
  nth_rewrite 1 [e0]
  rw [torusZ_sub_mem_iff, torusZ_sub_mem_iff, torusZ_sub_mem_iff]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, by simpa [bpoints] using h⟩
    · exact ⟨1, by simpa [bpoints] using h⟩
    · exact ⟨2, by simpa [bpoints] using h⟩
  · rintro ⟨j, h⟩
    fin_cases j
    · left; simpa [bpoints] using h
    · right; left; simpa [bpoints] using h
    · right; right; simpa [bpoints] using h

lemma bpoints_fst_mem (j : Fin 3) : (bpoints j).1 ∈ Ico (0 : ℝ) 1 := by
  fin_cases j <;> simp [bpoints] <;> norm_num

theorem Zunit_zero_ne_zero_of_fract {u v : ℝ} (h : ∀ j : Fin 3, Int.fract u ≠ (bpoints j).1) :
    Zunit u v 0 ≠ 0 := by
  intro h0
  obtain ⟨j, m, n, hu, -⟩ := (Z0_eq_zero_iff u v).mp h0
  apply h j
  rw [hu, Int.fract_add_intCast, Int.fract_eq_self.mpr (bpoints_fst_mem j)]

theorem Zunit_zero_ne_zero_of_mem {u : ℝ} (hu : u ∈ Ioo (1/12 : ℝ) (1/4)) (v : ℝ) :
    Zunit u v 0 ≠ 0 := by
  apply Zunit_zero_ne_zero_of_fract
  have hf : Int.fract u = u := Int.fract_eq_self.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  intro j
  rw [hf]
  fin_cases j <;> simp [bpoints] <;> intro h <;> rw [h] at hu <;> norm_num at hu

end SymplecticPacking.Bundle
