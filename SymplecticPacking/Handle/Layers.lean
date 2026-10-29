import SymplecticPacking.Handle.Twist

/-!
`sec:shd-four` (`def:shd4-scalars`, `lem:shd4-budget`, `def:shd4-frame`, `lem:shd4-Gf`):
the residual `R*`, the layer intervals and the final coefficient `G_f`.

The scalar data `μ_h`, `h_i`, `J` and their estimates (`def:shd4-scalars`, `lem:shd4-budget`) are
`Params.muh`, `Params.hi`, `Params.J`, `Params.Hstar_ge`, `Params.hi_gt_pos_part`,
`Params.hi_sub_pos_part_le`, `Params.sum_hi_le`, `Params.residual_ge` (`Params.lean`). All `h_i`
are equal to `Params.hi`; sums `∑_{i=1}^k` are over `Finset.Icc 1 k`.

* `Rstar P w = K(p(q⁻¹w)) − J(p(w)) − ∑ h_i(p(w))` with `q = q̂₁`; `Rstar_ge`: `R* ≥ 7g/8` on
  `D̄(h)`, from `Qhat.full_comparison` at the source point `z = q⁻¹(w)`.
* `layerLeft j`, `layerRight j`, `rhoLayer j` for `1 ≤ j ≤ N_ℓ = k + 1`; `Gf P s w`;
  `Gf_mono`, `Gf_low`, `Gf_up`, `Gf_layer`.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology
open SymplecticPacking.Bundle (stepA u0 u1)
open SymplecticPacking.Qhat (qhatP qhatInvP Psupp)
open scoped ContDiff Real

variable (P : Params)

/-! ### Disk preservation -/

/-! ### The residual (`def:shd4-scalars`, `lem:shd4-budget`) -/

/-- **The residual** `R*(w) = K(p(q⁻¹ w)) − J(p(w)) − ∑_{i=1}^k h_i(p(w))`, `q = q̂₁`. -/
def Rstar (w : ℂ) : ℝ :=
  P.K (π * ‖qhatInvP P 1 w‖ ^ 2) - P.J (π * ‖w‖ ^ 2) -
    ∑ _i ∈ Finset.Icc 1 P.k, P.hi (π * ‖w‖ ^ 2)

/-! ### Layer intervals (`def:shd4-frame`) -/

/-- `N_ℓ = k + 1` layers: `k` toric ones and the residual one `* = N_ℓ`. -/
def Nlayers : ℕ := P.k + 1

/-- `ℓ_s = (u₁ − u₀)/N_ℓ`. -/
def ells : ℝ := (u1 - u0) / (Nlayers P)

/-- `left_j = u₀ + (j − 1)ℓ_s + ℓ_s/4`. -/
def layerLeft (j : ℕ) : ℝ := u0 + ((j : ℝ) - 1) * (ells P) + (ells P) / 4

/-- `right_j = u₀ + (j − 1)ℓ_s + 3ℓ_s/4`. -/
def layerRight (j : ℕ) : ℝ := u0 + ((j : ℝ) - 1) * (ells P) + 3 * (ells P) / 4

/-- `ρ_j(s) = S((s − left_j)/(right_j − left_j))`. -/
def rhoLayer (j : ℕ) (s : ℝ) : ℝ :=
  flatStep ((s - (layerLeft P) j) / ((layerRight P) j - (layerLeft P) j))

/-! ### The final coefficient (`lem:shd4-Gf`) -/

/-- **`G_f(s, w) = J(p) + ∑_{i=1}^k ρ_i(s) h_i(p) + ρ_*(s) R*(w)`**, `p = p(w)`. -/
def Gf (s : ℝ) (w : ℂ) : ℝ :=
  P.J (π * ‖w‖ ^ 2) + ∑ i ∈ Finset.Icc 1 P.k, (rhoLayer P) i s * P.hi (π * ‖w‖ ^ 2) +
    (rhoLayer P) (Nlayers P) s * Rstar P w

/-- The toric part below layer `i`: `a_i = J + ∑_{j<i} h_j`. -/
def aLayer (i : ℕ) (p : ℝ) : ℝ := P.J p + ∑ _j ∈ Finset.Ico 1 i, P.hi p

end SymplecticPacking.Handle
