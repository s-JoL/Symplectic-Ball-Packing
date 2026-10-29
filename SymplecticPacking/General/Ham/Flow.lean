import SymplecticPacking.General.Ham.FieldIdentity
import SymplecticPacking.General.Ham.Curves

/-!
# Integral curves follow the isotopy

Formula (27): every integral curve of `X_H` from `s i + u`, `‖u‖ < r₁ᵢ`, follows the
isotopy, `γ t = F i t u` for `t ∈ [0,1]` (by (26) and uniqueness of ODE solutions).
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter Problem
open scoped ContDiff Topology

variable {n : ℕ}

variable {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n} {r1 r2 r3 ρ : Fin k → ℝ}

/-- **Formula (27).** (Uses `ofIsotopy_smooth` for the Lipschitz bound.) -/
theorem ofIsotopy_flow' (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) (u : E n)
    (hu : ‖u‖ < r1 i) (γ : ℝ → E n) (hγ0 : γ 0 = s i + u)
    (hγ : IsIntegralCurveOn γ (Problem.hamVF (ofIsotopy F r1 r2 r3)) (Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t = F i t u := by
  obtain ⟨S, hS⟩ := hF.bounded
  obtain ⟨K, C, hlip, -⟩ := hamVF_lipschitz_bound (ofIsotopy_smooth hF) (ofIsotopy_support hS)
    (fun t y ht => hamVF_ofIsotopy_eq_zero_of_time hF ht y)
  have hu1 : ‖u‖ < r1 i := hu
  have huρ : u ∈ ball (0 : E n) (ρ i) := mem_ball_zero_iff.mpr (by
    obtain ⟨_, h12, h23, h3ρ⟩ := hF.radii i; linarith)
  set c : ℝ → E n := fun t => F i t u with hcdef
  have hc : ∀ t, HasDerivAt c (Problem.hamVF (ofIsotopy F r1 r2 r3) t (c t)) t := by
    intro t
    have hd := hasDerivAt_time ((hF.sympFamily i).differentiableAt (s := t) huρ)
    rw [show c t = F i t u from rfl, hamVF_ofIsotopy_image hF i t hu1, hd.deriv]
    exact hd
  have hIci : ∀ t ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) 1 ∈ 𝓝[≥] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have heq := ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) (K := K)
    (v := Problem.hamVF (ofIsotopy F r1 r2 r3)) (f := γ) (g := c)
    (fun t _ => (hlip t).lipschitzOnWith) hγ.continuousOn
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun _ _ => mem_univ _)
    (fun t _ => (hc t).continuousAt.continuousWithinAt)
    (fun t _ => (hc t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (by rw [hγ0]; exact (hF.start i u).symm)
  exact fun t ht => heq ht

end SymplecticPacking.General.Ham
