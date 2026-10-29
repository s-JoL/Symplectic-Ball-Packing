import SymplecticPacking.Bundle.Theta

/-!
# The connection form and the area form on the torus cover

`sec:fer` (`def:cub-model`, `lem:fer-alpha`, `lem:fer-sigma`, `def:fer-frame`): the connection form `η_H` and the
area form `σ` pulled back to the universal cover `ℝ²` of the torus by the theta lift `Zunit`.

Conventions: `⟨Z, W⟩ = Σ conj(Z i) W i` (`herm3`); `∂_u Z`, `∂_v Z` are `dZu`, `dZv`.
* `η_H = (2πi)⁻¹ Z† dZ`. On `‖Z‖ = 1` the product `Z† dZ` is purely imaginary, so
  `Zunit^* η_H = (Im⟨Z, ∂_u Z⟩ du + Im⟨Z, ∂_v Z⟩ dv) / 2π` (`etaHu`, `etaHv`).
* `σ = Zunit^* ω_FS = (2πi)⁻¹ dZ† ∧ dZ = (1/π) Im⟨∂_u Z, ∂_v Z⟩ du ∧ dv` (`sigmaC`), the
  Fubini–Study form with line area `1`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open _root_.Complex ComplexConjugate
open scoped Real

/-- Hermitian product `⟨Z, W⟩ = Σ conj(Z i) W i` on `ℂ³`. -/
def herm3 (Z W : Fin 3 → ℂ) : ℂ := ∑ i, conj (Z i) * W i

/-- `∂_u Zunit`. -/
def dZu (u v : ℝ) : Fin 3 → ℂ := deriv (fun s => Zunit s v) u

/-- `∂_v Zunit`. -/
def dZv (u v : ℝ) : Fin 3 → ℂ := deriv (fun t => Zunit u t) v

/-- `du`-coefficient of `Zunit^* η_H`, `η_H = (2πi)⁻¹ Z† dZ`. -/
def etaHu (u v : ℝ) : ℝ := (herm3 (Zunit u v) (dZu u v)).im / (2 * π)

/-- `dv`-coefficient of `Zunit^* η_H`. -/
def etaHv (u v : ℝ) : ℝ := (herm3 (Zunit u v) (dZv u v)).im / (2 * π)

/-- `σ = Zunit^* ω_FS` as a multiple of `ν = du ∧ dv`: `σ = (1/π) Im⟨∂_u Z, ∂_v Z⟩`. -/
def sigmaC (u v : ℝ) : ℝ := (herm3 (dZu u v) (dZv u v)).im / π

end SymplecticPacking.Bundle
