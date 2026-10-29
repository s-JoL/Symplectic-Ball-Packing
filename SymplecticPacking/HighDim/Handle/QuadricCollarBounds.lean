import SymplecticPacking.BranchLargeHigh.FSTail

/-!
# Collar bounds for the quadric

The inner radius and explicit Fubini--Study budget of the quadric collar.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics

theorem quadric_tail_factor_lower {q : ℕ} (hq : 2 ≤ q) :
    16 ≤ (2 : ℝ)^q * (q+2) := by
  have hp : (4 : ℝ) ≤ (2 : ℝ)^q := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq
    norm_num at hp
    exact hp
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

theorem quadric_collar_level_two {q ℓ : ℕ} {d : ℝ} (hq : 2 ≤ q)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hℓ : 64*((2:ℝ)^q*(q+2))/d ≤ ℓ) : 2 ≤ ℓ := by
  have hA := quadric_tail_factor_lower hq
  have hcross := (div_le_iff₀ hd).mp hℓ
  have hL : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hmul : (ℓ : ℝ)*d ≤ ℓ := mul_le_of_le_one_right hL hd1
  have htwo : (2 : ℝ) ≤ ℓ := by nlinarith
  exact_mod_cast htwo

theorem quadric_exhaustion_inner_radius {q ℓ : ℕ} (a : Fin q → ℂ) (hℓ : 2 ≤ ℓ) :
    exhaustionRadius a (ℓ-2) = exhaustionRadius a ℓ-2 := by
  simp only [exhaustionRadius, Nat.cast_sub hℓ, Nat.cast_ofNat]
  ring

/-- The proof applies to every sufficiently large certified integer level. -/
theorem quadric_collar_numeric_bound {q ℓ : ℕ} (a : Fin q → ℂ) {d : ℝ}
    (hq : 2 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1)
    (hℓ : 64*((2:ℝ)^q*(q+2))/d ≤ ℓ) :
    (2:ℝ)^q*(q+2)/(exhaustionRadius a ℓ-2)^2 ≤ d/65536 := by
  let A : ℝ := (2:ℝ)^q*(q+2)
  let R : ℝ := exhaustionRadius a ℓ-2
  have hA : 16 ≤ A := quadric_tail_factor_lower hq
  have hRℓ : (ℓ : ℝ) ≤ R := by
    dsimp [R, exhaustionRadius]
    have hs : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    linarith
  have hR0 : 0 ≤ R := (Nat.cast_nonneg ℓ).trans hRℓ
  have hc : 64*A ≤ d*R := by
    have hc := (div_le_iff₀ hd).mp hℓ
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hRℓ hd.le]
  have hR : 64*A ≤ R := by nlinarith [mul_le_of_le_one_left hR0 hd1]
  have hRpos : 0 < R := by linarith
  have hmul := mul_le_mul hc hR (by positivity : 0 ≤ 64*A) (mul_nonneg hd.le hR0)
  have hAA : 65536*A ≤ 4096*A^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ A-16)]
  change A/R^2 ≤ d/65536
  apply (div_le_div_iff₀ (sq_pos_of_pos hRpos) (by norm_num : (0:ℝ)<65536)).mpr
  nlinarith

variable {q : ℕ} (a : Fin q → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a

theorem quadric_collar_inner_defect {ℓ : ℕ} {d : ℝ}
    (hq : 2 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1)
    (hℓ : 64*((2:ℝ)^q*(q+2))/d ≤ ℓ) :
    (2:ℝ)^q - compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a (ℓ-2)))
      (curveFSForm a (1/Real.pi)) ≤ d/65536 := by
  have ht := SymplecticPacking.BranchLargeHigh.exhaustion_area_defect_le a (ℓ-2)
  apply ht.trans
  rw [quadric_exhaustion_inner_radius a (quadric_collar_level_two hq hd hd1 hℓ)]
  exact quadric_collar_numeric_bound a hq hd hd1 hℓ

end SymplecticPacking.HighDim.ToricPackingStages
