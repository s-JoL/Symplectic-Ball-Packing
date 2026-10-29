import SymplecticPacking.General.Ham.Flow

/-!
# The Hamiltonian of a common isotopy

`ofIsotopy_spec` (dimension `2n`, per-ball radii): the Hamiltonian `ofIsotopy F r₁ r₂ r₃` of a
common isotopy is smooth, compactly supported, has global integral curves, and its integral
curves from the balls `s_i + B(r₁ i)` follow the isotopy.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Problem
open scoped ContDiff

variable {n : ℕ}

/-- **`sec:ham-hamiltonian`.** The explicit Hamiltonian `ofIsotopy F r₁ r₂ r₃` of a common isotopy is
smooth and compactly supported, has global integral curves, and on the balls `‖u‖ < r₁` its
integral curves are exactly the isotopy: `φ_H^t(s_i + u) = F i t u` (formula (27)). -/
theorem ofIsotopy_spec {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n}
    {r1 r2 r3 ρ : Fin k → ℝ}
    (hF : CommonIsotopy F s r1 r2 r3 ρ) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => ofIsotopy F r1 r2 r3 p.1 p.2) ∧
    (∃ K : Set (E n), IsCompact K ∧ ∀ t, ∀ y ∉ K, ofIsotopy F r1 r2 r3 t y = 0) ∧
    (∀ x : E n, ∃ γ : ℝ → E n, γ 0 = x ∧ IsIntegralCurve γ (Problem.hamVF (ofIsotopy F r1 r2 r3))) ∧
    (∀ i : Fin k, ∀ u : E n, ‖u‖ < r1 i → ∀ γ : ℝ → E n, γ 0 = s i + u →
      IsIntegralCurveOn γ (Problem.hamVF (ofIsotopy F r1 r2 r3)) (Icc 0 1) →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t = F i t u) :=
  ⟨ofIsotopy_smooth hF, ofIsotopy_compactSupport hF.bounded, ofIsotopy_exists_curve' hF,
    fun i u hu γ hγ0 hγ => ofIsotopy_flow' hF i u hu γ hγ0 hγ⟩

end SymplecticPacking.General.Ham
