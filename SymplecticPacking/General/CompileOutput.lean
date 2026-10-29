import SymplecticPacking.General.Compile

/-!
# Finite output of the dimension-independent compiler

The output consists of an integer box size and a rational polynomial, rather than an
existentially chosen Hamiltonian. Correctness holds for every `CompilationDatum` satisfying
(C1)–(C7); producing that datum from names of computable inputs is a separate obligation.
-/

noncomputable section

namespace SymplecticPacking.General.Compile

open Problem
open scoped ContDiff

/-- The finite data returned by the compiler: the cutoff box and rational polynomial. -/
structure FiniteOutput (n : ℕ) where
  B : ℕ
  P : MvPolynomial (Fin (2 * n + 1)) ℚ

/-- Interpretation of the finite output as the explicit flat cutoff times its polynomial. -/
def FiniteOutput.hamiltonian {n : ℕ} (out : FiniteOutput n) : ℝ → E n → ℝ :=
  finiteHam n out.B out.P

/-- Extract the finite output directly from the supplied compilation datum. -/
def compileOutput {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (D : CompilationDatum n k C c s H) : FiniteOutput n :=
  ⟨D.B, D.P⟩

/-- **L2 correctness.** Every datum satisfying (C1)–(C7) yields finite rational output whose
Hamiltonian carries the given closed source balls into the original open target. No special
dimension, equal-radius hypothesis, or additional compilation choice is required. -/
theorem main_finite {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (D : CompilationDatum n k C c s H) :
    PackingSpec n k C c s (compileOutput D).hamiltonian :=
  finite_spec hH D

end SymplecticPacking.General.Compile
