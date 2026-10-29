import SymplecticPacking.Strip.Map
import SymplecticPacking.Params

/-!
`sec:str-balls` (paper `def:str-enlarged`, `lem:str-ball`): the enlarged capacities
`ρ < ρ̄ < ρ̂ < a` and the ball estimate: a point of the ball of capacity `ρ̄` (or `ρ̂`) at fibre
level `p` is sent by the strip map to an `x` smaller than the layer width `h_i(p)`.
(`ρ̄ = (ρ + a)/2` is `Params.rhoBar`, `def:str-enlarged`.)
-/

noncomputable section

namespace SymplecticPacking.Strip

open scoped Real

variable (P : Params)

/-- `δ_strip = a - ρ̄`. -/
def deltaStrip : ℝ := P.a - P.rhoBar

/-- `ρ̂ = ρ̄ + (a - ρ̄)/4`. -/
def rhoHat : ℝ := P.rhoBar + (P.a - P.rhoBar) / 4

end SymplecticPacking.Strip
