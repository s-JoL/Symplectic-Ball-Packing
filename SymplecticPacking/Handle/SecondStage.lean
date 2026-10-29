import SymplecticPacking.Handle.FirstStage

/-!
# A support lemma for the second stage of the handle

`sec:shd-four` (`cons:shd4-xi`, `lem:shd4-xi`): `bB_eventually_zero`, the bump `b` of
`β = b(v) dv` vanishes near the `v`-coordinates of the three points `b_j`. The second stage and
the final form for cubic data are in `Branch2/Model/Cubic/Handle/SecondStage.lean`.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus OmegaT OmegaT_split pp
  contDiff_stepA contDiff_bB bpoints)
open SymplecticPacking.Qhat (qhatP qhatInvP QhamP Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

attribute [local irreducible] Bundle.frameA Bundle.Zunit Bundle.lambdaCu Bundle.lambdaCv
  Bundle.etaHu Bundle.etaHv Bundle.sigmaC

variable (P : Params)

/-! ### The second-stage primitive (`cons:shd4-xi`) -/

/-- `G_f − G₁`. -/
def Gdiff (s : ℝ) (w : ℂ) : ℝ := Gf P s w - Glam P 1 s w

/-- **`ξ_𝒜 = 𝒟^*[(G_f − G₁)β] = ((G_f − G₁) ∘ 𝒟) β`** on `𝒜 × ℂ`. -/
def xiA : Form1 E4 := fun X => (Gdiff P (X 2) (wL (Dlam P 1 X)) * bB (X 3)) • dc 3

/-- `J(p) π^*β`, a global one-form. -/
def JbE : Form1 E4 := fun X => (P.J (pE X) * bB (X 3)) • dc 3

open Classical in
/-- **The second-stage primitive on `N`**: `ξ = J(p) π^*β + ext₀(ξ_𝒜 − J(p) β)`. -/
def xi : Form1 E4 := fun X =>
  JbE P X + if X 2 ∈ annulus then xiA P (chartInv X) - JbE P (chartInv X) else 0

/-- **The second stage** `Ω^{(2)}_τ = Ω^{(1)}_1 + τ dξ` (`cons:shd4-xi`). -/
def secondStage (τ : ℝ) : Form2 E4 := fun X => firstStage P 1 X + τ • d1 (xi P) X

/-- **The final form** `Ω_final = Ω^{(2)}_1 = Ω₀ + dα₁ + dη₁ + dξ`. -/
def OmegaFinal : Form2 E4 := secondStage P 1

/-- **`Ω_pre = dγ_sm + ω_V + d(G_f β)`** (`prop:shd4-third`), in the `𝒜⁺`-frame. -/
def OmegaPre : Form2 E4 := OmegaPreG P (Gf P)

/-! ### `ξ` is global (`lem:shd4-xi`) -/

/-- `bB` vanishes near the `v`-coordinates of the three points `b_j`. -/
lemma bB_eventually_zero (j : Fin 3) : bB =ᶠ[𝓝 (bpoints j).2] fun _ => 0 := by
  have hc0 : |Bundle.centred (bpoints j).2 (bpoints j).2| < 1 / 2 := by
    rw [Bundle.centred, sub_self, zero_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    norm_num
  have hev := Bundle.centred_eventually hc0
  have hfl : ⌊(bpoints j).2 - (bpoints j).2 + 1 / 2⌋ = 0 := by
    rw [sub_self, zero_add, Int.floor_eq_zero_iff]; constructor <;> norm_num
  rw [hfl] at hev
  filter_upwards [hev, Metric.ball_mem_nhds (bpoints j).2 (by norm_num : (0 : ℝ) < 1 / 100)]
    with v hv hball
  have hc : |Bundle.centred (bpoints j).2 v| < 1 / 100 := by
    rw [hv]; simpa [Real.dist_eq] using hball
  exact Bundle.bB_eq_zero fun hm => Bundle.v_far_strip hc
    ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-! ### The second stage on `𝒜` and off it (`prop:shd4-third`) -/

/-! ### The final form over the annulus (`prop:shd4-third`) -/

/-- The inverse twist `𝒟_λ⁻¹(s, t, w) = (s, t, q_{λ f(s)}⁻¹(w))`. -/
def DlamInv (lam : ℝ) (X : E4) : E4 := mk (qhatInvP P (lam * stepA (X 2)) (wL X)) (X 2) (X 3)

end SymplecticPacking.Handle
