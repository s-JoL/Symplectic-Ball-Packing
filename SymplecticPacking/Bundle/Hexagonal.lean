import Mathlib

/-!
# The hexagonal lattice and the Fermat cubic

`sec:fer-torus`: the hexagonal period lattice `ℤ + ℤ ζ₆` has `g₂ = 0`, so its Weierstrass
function satisfies `℘'² = 4℘³ - g₃`; after rescaling to `g₃ = 1`, `z ↦ [2℘ : -(1+℘'/√3) : -(1-℘'/√3)]`
lands on the Fermat cubic.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Complex PeriodPair

/-- `ζ₆ = e^{iπ/3} = 1/2 + i√3/2`. -/
def zeta6 : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

lemma zeta6_sq : zeta6 ^ 2 = zeta6 - 1 := by
  apply Complex.ext <;> simp [zeta6, sq] <;> ring_nf <;>
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring

lemma zeta6_ne_zero : zeta6 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [zeta6] at this

/-- The hexagonal period pair `(1, ζ₆)`. -/
def hexPair : PeriodPair where
  ω₁ := 1
  ω₂ := zeta6
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
    have him : t * (Real.sqrt 3 / 2) = 0 := by
      have := congrArg Complex.im h; simpa [zeta6] using this
    have hre : s + t * (1 / 2) = 0 := by
      have := congrArg Complex.re h; simpa [zeta6] using this
    have ht : t = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exfalso; linarith
    exact ⟨by rw [ht] at hre; linarith, ht⟩

lemma mul_zeta6_mem {z : ℂ} (hz : z ∈ hexPair.lattice) : zeta6 * z ∈ hexPair.lattice := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair] at hz ⊢
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨-b, a + b, ?_⟩
  simp only [hexPair, zsmul_eq_mul]
  have := zeta6_sq
  push_cast
  linear_combination (-(↑b : ℂ)) * this

/-- Multiplication by `ζ₆` permutes the lattice. -/
def rotLattice : hexPair.lattice ≃ hexPair.lattice where
  toFun l := ⟨zeta6 * l, mul_zeta6_mem l.2⟩
  invFun l := ⟨(1 - zeta6) * l, by
    have h1 := mul_zeta6_mem l.2
    have : (1 - zeta6) * (l : ℂ) = (l : ℂ) - zeta6 * l := by ring
    rw [this]; exact Submodule.sub_mem _ l.2 h1⟩
  left_inv l := by
    ext; simp only
    have := zeta6_sq
    linear_combination (-(l : ℂ)) * this
  right_inv l := by
    ext; simp only
    have := zeta6_sq
    linear_combination (-(l : ℂ)) * this

lemma zeta6_pow_four_ne_one : zeta6 ^ 4 ≠ 1 := by
  have h2 := zeta6_sq
  have h4 : zeta6 ^ 4 = -zeta6 := by
    calc zeta6 ^ 4 = (zeta6 ^ 2) ^ 2 := by ring
      _ = (zeta6 - 1) ^ 2 := by rw [h2]
      _ = zeta6 ^ 2 - 2 * zeta6 + 1 := by ring
      _ = -zeta6 := by rw [h2]; ring
  rw [h4]; intro h
  have := congrArg Complex.re h; simp [zeta6] at this; norm_num at this

/-- **`g₂ = 0` for the hexagonal lattice.** -/
theorem hex_G4 : hexPair.G 4 = 0 := by
  have h : hexPair.G 4 = (zeta6 ^ 4)⁻¹ * hexPair.G 4 := by
    unfold PeriodPair.G
    rw [← tsum_mul_left, ← rotLattice.tsum_eq]
    congr 1; funext l
    simp only [rotLattice, Equiv.coe_fn_mk, mul_pow, mul_inv]
  have hne : (zeta6 ^ 4)⁻¹ ≠ 1 := by
    intro h1; exact zeta6_pow_four_ne_one (inv_eq_one.mp h1)
  have : (1 - (zeta6 ^ 4)⁻¹) * hexPair.G 4 = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h').symm hne
  · exact h'

theorem hex_g2 : hexPair.g₂ = 0 := by simp [PeriodPair.g₂, hex_G4]

/-- Hence `℘'² = 4 ℘³ - g₃` off the lattice. -/
theorem hex_wp_eq (z : ℂ) (hz : z ∉ hexPair.lattice) :
    ℘'[hexPair] z ^ 2 = 4 * ℘[hexPair] z ^ 3 - hexPair.g₃ := by
  rw [hexPair.derivWeierstrassP_sq z hz, hex_g2]; ring

end SymplecticPacking.Bundle
