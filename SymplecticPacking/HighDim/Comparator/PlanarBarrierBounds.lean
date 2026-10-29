import Mathlib

/-!
# Barrier margins for the parameterised planar construction

The hypotheses are estimates on the unmodified potential after paying the quadratic
modification error; that error is kept for arbitrarily large tolerances.
-/

namespace SymplecticPacking.HighDim.PlanarGen

open Real

/-- A modified-energy bound gives strict distance from both radial endpoints. The `4κ`
term pays the endpoint barrier at its minimum; `δ` pays the well modification error. -/
theorem radial_barrier_margin {κ M E δ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) (hp1 : p < 1)
    (henergy : κ / p + κ / (1 - p) - 2 * M - 4 * κ ≤ E + δ) :
    κ / (2 * M + 2 + 4 * κ + E + δ) < p ∧
      κ / (2 * M + 2 + 4 * κ + E + δ) < 1 - p := by
  have hother : 0 < κ / (1 - p) := div_pos hκ (by linarith)
  have hfirst : 0 < κ / p := div_pos hκ hp
  have hsum : κ / p + κ / (1 - p) ≤ 2 * M + 4 * κ + E + δ := by linarith
  have hden : 0 < 2 * M + 2 + 4 * κ + E + δ := by linarith
  constructor
  · rw [div_lt_iff₀ hden]
    have hlt : κ / p < 2 * M + 2 + 4 * κ + E + δ := by linarith
    have := (div_lt_iff₀ hp).mp hlt
    nlinarith
  · rw [div_lt_iff₀ hden]
    have hlt : κ / (1 - p) < 2 * M + 2 + 4 * κ + E + δ := by linarith
    have := (div_lt_iff₀ (by linarith : 0 < 1 - p)).mp hlt
    nlinarith

end SymplecticPacking.HighDim.PlanarGen
