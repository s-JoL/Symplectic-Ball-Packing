import SymplecticPacking.BranchLargeHigh.Phase

/-!
# The first coupled normal line over the base ball chart

Paper `lem:lrg-slit`, supplement `lem:two-slit`.
On `ℂ × B^{2m}(1)` with fibre coordinate `z = zc y 0` and base coordinate `ξ = (zc y i.succ)`,
the coupled form is

  `Ω = d[λ_fib + (1 - u) λ_base] = ω_fib + (1 - u) ω_base - du ∧ λ_base`,

`u = π|z|²`, `λ_base(ξ)(w) = ω_base(ξ, w)/2`. It is the pull-back of the standard first-normal
form `σ + d(u α)` under the unitary frame of `O(1)` over `CP^m ∖ F` with angular connection
`α = dθ - λ_base`. The second stage of the branch produces embeddings that pull `Ω` back to `ω₀`
(`IsCoupledSymplectic`); the slit-shell map pulls `ω₀` back to `Ω` (`Shell.lean`).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General

variable {m : ℕ}

/-- The fibre area form `ω_fib = dx_0 ∧ dy_0` on the first complex coordinate. -/
def omegaFib (v w : E (m + 1)) : ℝ :=
  (zc v 0).re * (zc w 0).im - (zc v 0).im * (zc w 0).re

/-- The base form `ω_base = Σ_{i ≥ 1} dx_i ∧ dy_i`. -/
def omegaBase (v w : E (m + 1)) : ℝ :=
  ∑ i : Fin m, ((zc v i.succ).re * (zc w i.succ).im - (zc v i.succ).im * (zc w i.succ).re)

/-- The differential of the fibre moment, `du_y(v) = 2π ⟨z₀(y), z₀(v)⟩`. -/
def dFib (y v : E (m + 1)) : ℝ :=
  2 * Real.pi * ((zc y 0).re * (zc v 0).re + (zc y 0).im * (zc v 0).im)

/-- The base Liouville form `λ_base(y)(w) = ω_base(y, w)/2`. -/
def lamBase (y w : E (m + 1)) : ℝ := omegaBase y w / 2

/-- **The coupled form** `Ω_y(v, w) = ω_fib(v,w) + (1 - u(y)) ω_base(v,w)
- du_y(v) λ_base(y)(w) + du_y(w) λ_base(y)(v)`. -/
def coupledForm (y v w : E (m + 1)) : ℝ :=
  omegaFib v w + (1 - fibMoment y) * omegaBase v w - dFib y v * lamBase y w +
    dFib y w * lamBase y v

/-- A map `g` into the coupled model is *coupled-symplectic* at `y` if `g^*Ω = ω₀` there. -/
def IsCoupledSymplectic {n : ℕ} (g : E n → E (m + 1)) (y : E n) : Prop :=
  ∀ v w, coupledForm (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) = Problem.omega0 v w

end SymplecticPacking.BranchLargeHigh
