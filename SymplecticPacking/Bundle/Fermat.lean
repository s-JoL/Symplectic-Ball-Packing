import SymplecticPacking.Bundle.WeierstrassInj

/-!
# The Fermat cubic as the image of the hexagonal torus

`sec:fer-torus`: the hexagonal torus `ℂ / (ℤ + ℤ ζ₆)` embeds in `ℂP²` as the Fermat
cubic `X³ + Y³ + Z³ = 0`, via `z ↦ [2 c ℘ z : -(1 + d ℘' z) : -(1 - d ℘' z)]` (and lattice
points `↦ [0 : 1 : -1]`).

The paper rescales the lattice so that `g₃ = 1`; here we keep `hexPair` and instead normalise
the map with explicit constants `cF = g₃^{-1/3}`, `dF = (3 g₃)^{-1/2}` (principal branches), so
that `cF³ = 1/g₃` and `dF² = 1/(3 g₃)`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Complex PeriodPair

/-- `cF = g₃^{-1/3}` (principal branch). -/
def cF : ℂ := hexPair.g₃ ^ (-(1 : ℂ) / 3)

/-- `dF = (3 g₃)^{-1/2}` (principal branch). -/
def dF : ℂ := (3 * hexPair.g₃) ^ (-(1 : ℂ) / 2)

theorem cF_cube : cF ^ 3 = 1 / hexPair.g₃ := by
  rw [cF, ← Complex.cpow_nat_mul]
  have : ((3 : ℕ) : ℂ) * (-(1 : ℂ) / 3) = -1 := by push_cast; ring
  rw [this, Complex.cpow_neg_one, one_div]

theorem dF_sq : dF ^ 2 = 1 / (3 * hexPair.g₃) := by
  rw [dF, ← Complex.cpow_nat_mul]
  have : ((2 : ℕ) : ℂ) * (-(1 : ℂ) / 2) = -1 := by push_cast; ring
  rw [this, Complex.cpow_neg_one, one_div]

theorem cF_ne_zero : cF ≠ 0 := by
  intro h
  have := cF_cube
  rw [h] at this
  simp at this
  exact hex_g3_ne_zero this.symm

theorem dF_ne_zero : dF ≠ 0 := by
  intro h
  have := dF_sq
  rw [h] at this
  simp at this
  exact hex_g3_ne_zero this

/-- The Fermat cubic form `X³ + Y³ + Z³`. -/
def fermat (Z : Fin 3 → ℂ) : ℂ := Z 0 ^ 3 + Z 1 ^ 3 + Z 2 ^ 3

/-- Affine lift of the torus parametrisation at `z ∉ L`. -/
def torusLift (z : ℂ) : Fin 3 → ℂ :=
  ![2 * cF * ℘[hexPair] z, -(1 + dF * ℘'[hexPair] z), -(1 - dF * ℘'[hexPair] z)]

/-- Affine lift of the image of the lattice points: `[0 : 1 : -1]`. -/
def latticeLift : Fin 3 → ℂ := ![0, 1, -1]

/-- Affine lift of the torus parametrisation on all of `ℂ`. -/
def torusPoint (z : ℂ) : Fin 3 → ℂ := by
  classical
  exact if z ∈ hexPair.lattice then latticeLift else torusLift z

theorem torusLift_fermat {z : ℂ} (hz : z ∉ hexPair.lattice) : fermat (torusLift z) = 0 := by
  have hg := hex_g3_ne_zero
  have hc := cF_cube
  have hd := dF_sq
  have hQ := hex_wp_eq z hz
  simp only [fermat, torusLift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  set P := ℘[hexPair] z
  set Q := ℘'[hexPair] z
  set g := hexPair.g₃
  have e : (2 * cF * P) ^ 3 + (-(1 + dF * Q)) ^ 3 + (-(1 - dF * Q)) ^ 3
      = 8 * cF ^ 3 * P ^ 3 - 2 - 6 * dF ^ 2 * Q ^ 2 := by ring
  rw [e, hc, hd, hQ]
  field_simp
  ring

theorem latticeLift_fermat : fermat latticeLift = 0 := by
  simp [fermat, latticeLift]; norm_num

lemma latticeLift_one_add_two : latticeLift 1 + latticeLift 2 = 0 := by
  simp [latticeLift]

/-- Components 1 and 2 of `torusLift z` sum to `-2`. -/
lemma torusLift_one_add_two (z : ℂ) : torusLift z 1 + torusLift z 2 = -2 := by
  simp [torusLift]; ring

theorem torusLift_ne_zero (z : ℂ) : torusLift z ≠ 0 := by
  intro h
  have h3 := torusLift_one_add_two z
  rw [h] at h3
  simp at h3

theorem latticeLift_ne_zero : latticeLift ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [latticeLift] at this

theorem torusLift_mem {z : ℂ} (hz : z ∉ hexPair.lattice) :
    torusLift z ≠ 0 ∧ fermat (torusLift z) = 0 :=
  ⟨torusLift_ne_zero z, torusLift_fermat hz⟩

theorem torusPoint_mem (z : ℂ) : torusPoint z ≠ 0 ∧ fermat (torusPoint z) = 0 := by
  unfold torusPoint
  split_ifs with h
  · exact ⟨latticeLift_ne_zero, latticeLift_fermat⟩
  · exact torusLift_mem h

/-- **Projective injectivity** of the torus parametrisation off the lattice. -/
theorem torusLift_proj_injective {z w : ℂ} (hz : z ∉ hexPair.lattice)
    (hw : w ∉ hexPair.lattice) (h : ∃ c : ℂ, c ≠ 0 ∧ torusLift w = c • torusLift z) :
    z - w ∈ hexPair.lattice := by
  obtain ⟨c, -, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  have hs : torusLift w 1 + torusLift w 2 = c * (torusLift z 1 + torusLift z 2) := by
    rw [h1, h2]; simp [mul_add]
  rw [torusLift_one_add_two, torusLift_one_add_two] at hs
  have hc1 : c = 1 := by linear_combination hs / 2
  subst hc1
  simp only [torusLift, Pi.smul_apply, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    ] at h0 h1
  have hP : ℘[hexPair] z = ℘[hexPair] w := by
    have : (2 * cF) * (℘[hexPair] w - ℘[hexPair] z) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero cF_ne_zero)
    · exact (sub_eq_zero.mp h).symm
  have hQ : ℘'[hexPair] z = ℘'[hexPair] w := by
    have : dF * (℘'[hexPair] w - ℘'[hexPair] z) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h dF_ne_zero
    · exact (sub_eq_zero.mp h).symm
  exact wp_injective z w hz hw hP hQ

/-- The image `[0 : 1 : -1]` of the lattice points is not on the image of `ℂ ∖ L`. -/
theorem latticeLift_not_proj_torusLift (z : ℂ) (c : ℂ) :
    latticeLift ≠ c • torusLift z := by
  intro h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have hs : latticeLift 1 + latticeLift 2 = c * (torusLift z 1 + torusLift z 2) := by
    rw [h1, h2]; simp [mul_add]
  rw [torusLift_one_add_two, latticeLift_one_add_two] at hs
  have hc0 : c = 0 := by linear_combination hs / 2
  rw [hc0, zero_smul] at h
  exact latticeLift_ne_zero h

theorem torusLift_not_proj_latticeLift (z : ℂ) (c : ℂ) :
    torusLift z ≠ c • latticeLift := by
  intro h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have hs : torusLift z 1 + torusLift z 2 = c * (latticeLift 1 + latticeLift 2) := by
    rw [h1, h2]; simp [mul_add]
  rw [torusLift_one_add_two, latticeLift_one_add_two] at hs
  norm_num at hs

/-- Projective injectivity of `torusPoint` on `ℂ / L`. -/
theorem torusPoint_proj_injective {z w : ℂ}
    (h : ∃ c : ℂ, c ≠ 0 ∧ torusPoint w = c • torusPoint z) :
    z - w ∈ hexPair.lattice := by
  obtain ⟨c, hc0, hc⟩ := h
  unfold torusPoint at hc
  by_cases hz : z ∈ hexPair.lattice <;> by_cases hw : w ∈ hexPair.lattice <;>
    simp only [hz, hw, ite_true, ite_false] at hc
  · exact Submodule.sub_mem _ hz hw
  · exact absurd hc (torusLift_not_proj_latticeLift w c)
  · exact absurd hc (latticeLift_not_proj_torusLift z c)
  · exact torusLift_proj_injective hz hw ⟨c, hc0, hc⟩

end SymplecticPacking.Bundle
