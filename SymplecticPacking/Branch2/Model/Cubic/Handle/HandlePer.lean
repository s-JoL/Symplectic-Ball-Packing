import SymplecticPacking.Handle.HandlePer
import SymplecticPacking.Branch2.Model.Cubic.Handle.HandleDeck

/-!
# Invariance of the strip primitives under the `v`-deck map

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`cons:shd4-moser`): the strip primitives `η_λ` (`Cubic/Handle/FirstStage.lean`),
`ξ` and `J(p)β` (`Cubic/Handle/SecondStage.lean`) are invariant (as covectors) under the deck map
`Tv` (`eta_TvE`, `xi_TvE`, `JbE_TvE`), via the `1`-periodicity in `t` of their local forms
(`etaLoc_shift3`, `xiA_shift3`, `JbE_shift3`) and `chartInv ∘ Tv = (v + 1) ∘ chartInv`
(`chartInv_TvE`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap _root_.Complex ComplexConjugate
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE Zunit phaseV frameA u0 u1 annulus stepA bB bB_add_one)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

/-! ### The iterated `u`-deck map and the periodisation -/

/-! ### `Tv`-invariance of the strip primitives -/

lemma etaLoc_shift3 (P : Branch2.VCubic) (lam : ℝ) (w : ℂ) (s t : ℝ) :
    etaLoc P lam (mk w s (t + 1)) = etaLoc P lam (mk w s t) := by
  simp [etaLoc, PhiS, etaCoef, bB_add_one]

theorem eta_TvE (P : Branch2.VCubic) (lam : ℝ) (Y : E4) : eta P lam (TvE Y) = eta P lam Y := by
  have h2 : TvE Y 2 = Y 2 := by simp [TvE]
  unfold eta
  rw [h2]
  split_ifs
  · rw [chartInv_TvE, etaLoc_shift3]
    congr 1
    conv_rhs => rw [← mk_wL (chartInv Y)]
    simp
  · rfl

theorem JbE_TvE (P : Branch2.VCubic) (Y : E4) : JbE P (TvE Y) = JbE P Y := by
  have hp : pE (TvE Y) = pE Y := deckV.pE_eq Y
  simp only [JbE, hp]
  simp [TvE, bB_add_one]

lemma JbE_shift3 (P : Branch2.VCubic) (w : ℂ) (s t : ℝ) : JbE P (mk w s (t + 1)) = JbE P (mk w s t) := by
  simp [JbE, bB_add_one]

lemma xiA_shift3 (P : Branch2.VCubic) (w : ℂ) (s t : ℝ) : xiA P (mk w s (t + 1)) = xiA P (mk w s t) := by
  simp [xiA, bB_add_one, Dlam]

theorem xi_TvE (P : Branch2.VCubic) (Y : E4) : xi P (TvE Y) = xi P Y := by
  have h2 : TvE Y 2 = Y 2 := by simp [TvE]
  unfold xi
  rw [h2, JbE_TvE]
  split_ifs
  · rw [chartInv_TvE, xiA_shift3, JbE_shift3]
    conv_rhs => rw [← mk_wL (chartInv Y)]
    simp
  · rfl

end SymplecticPacking.Handle.Cubic
