import SymplecticPacking.E4

/-!
# The embeddings of the four-dimensional construction

The properties (`prop:rtc-embeddings`) of the explicit embeddings `f_i`.
-/

noncomputable section

namespace SymplecticPacking

open Metric Set
open scoped ContDiff

/-- Properties of the four-dimensional embeddings: smooth with symplectic derivative on an
open ball `B(ρ')`, `ρ' > r₄`, injective on `B̄(r₄)`, pairwise disjoint images of `B̄(r₄)`, all
contained in the open ball `B(R₀)`. -/
structure Embed.Spec (P : Params) (f : Fin P.k → E4 → E4) (ρ' : ℝ) : Prop where
  radius : P.r4 < ρ'
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 ρ')
  sympl : ∀ i, ∀ u ∈ ball (0 : E4) ρ', IsSymplecticLinear (fderiv ℝ (f i) u)
  inj : ∀ i, InjOn (f i) (closedBall 0 P.r4)
  disj : ∀ i j, i ≠ j → Disjoint (f i '' closedBall 0 P.r4) (f j '' closedBall 0 P.r4)
  inBall : ∀ i, f i '' closedBall 0 P.r4 ⊆ ball 0 P.R0

end SymplecticPacking
