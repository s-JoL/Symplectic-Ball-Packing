import SymplecticPacking.General.Ham.Symp
import SymplecticPacking.Explicit

/-!
# The global Hamiltonian of a common isotopy (definitions)

Given a common isotopy `F i t : ℝ^{2n} → ℝ^{2n}` (defined for all `t`, constant outside `[0,1]`),
the Hamiltonian is the sum over `i` of the pushforwards of `χ_i · h_{i,t}`, where `h_{i,t}` is the
radial source primitive and `χ_i = Χ_{r₁ᵢ,r₂ᵢ}` a radial cutoff. The pushforward uses the definite
description of the unique preimage in `B̄(r₃ᵢ)` and is `0` off the image.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Problem

variable {n : ℕ}

/-- The radial cutoff `Χ_{r_on,r_off}(u) = 1 - S((|u|² - r_on²)/(r_off² - r_on²))`, `S` the flat
step `Real.smoothTransition`. -/
def radialCutoff (ron roff : ℝ) (u : E n) : ℝ :=
  1 - Real.smoothTransition ((‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2))

/-- The source one-form `a_t(u)[v] = ω₀(∂_t F(t,u), D_u F(t,u) v)`. -/
def sourceOneForm (F : ℝ → E n → E n) (t : ℝ) (u v : E n) : ℝ :=
  Problem.omega0 (deriv (fun s => F s u) t) (fderiv ℝ (F t) u v)

/-- The radial source primitive `h_t(u) = ∫₀¹ a_t(r u)[u] dr`. -/
def sourcePrimitive (F : ℝ → E n → E n) (t : ℝ) (u : E n) : ℝ :=
  ∫ r in (0 : ℝ)..1, sourceOneForm F t (r • u) u

open scoped Classical in
/-- Pushforward of a source function `g` along the embeddings `F t` restricted to `B̄(r)`: the
value at `y` is `g t u` for the unique `u ∈ B̄(r)` with `F t u = y`, and `0` if there is no such
unique `u`. -/
def pushforward (F : ℝ → E n → E n) (r : ℝ) (g : ℝ → E n → ℝ) (t : ℝ) (y : E n) : ℝ :=
  if h : ∃! u, u ∈ closedBall (0 : E n) r ∧ F t u = y then g t (Explicit.the h) else 0

/-- The global Hamiltonian of a common isotopy `F : Fin k → ℝ → ℝ^{2n} → ℝ^{2n}` with per-ball
radii `r₁ᵢ < r₂ᵢ < r₃ᵢ`. -/
def ofIsotopy {k : ℕ} (F : Fin k → ℝ → E n → E n) (r1 r2 r3 : Fin k → ℝ) (t : ℝ) (y : E n) : ℝ :=
  ∑ i, pushforward (F i) (r3 i)
    (fun t u => radialCutoff (r1 i) (r2 i) u * sourcePrimitive (F i) t u) t y

end SymplecticPacking.General.Ham
