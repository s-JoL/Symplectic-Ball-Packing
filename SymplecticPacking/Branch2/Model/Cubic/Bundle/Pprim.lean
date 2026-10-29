import SymplecticPacking.Bundle.Pprim
import SymplecticPacking.Branch2.Model.Cubic.Base

/-!
# The base area form `κ₁` and the primitive `α₁⁰`

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Bundle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:fer` (`def:fer-kappa`, `lem:fer-kappa`, `def:fer-Pprim`, `lem:fer-Pprim`): the base area
form `κ₁(p) = e_h ν + H*(p) χ` (`kappa1`), positivity of `κ(p) = (1 − 3p)σ` (`kappa_pos`), the
difference `κ₁ − κ` (`kdiff`) with zero torus integral (`integral_kdiff`), and
`α₁⁰ = P_prim(κ₁ − κ)` (`alpha10`) with `d_C α₁⁰ = κ₁ − κ` (`d_alpha10`), periodic and affine
in `p`. The forms `χ`, `κ` and the operator `P_prim` are those of `Bundle/Pprim.lean`.

Two-forms are coefficients of `ν = du ∧ dv`. `AffineP` records affine dependence on `p`.
-/

noncomputable section

namespace SymplecticPacking.Bundle.Cubic

open Set Filter Topology MeasureTheory
open scoped ContDiff Real

/-! ### Affine dependence on `p` -/

/-! ### `χ` and the base area forms -/

/-- `κ₁(p) = e_h ν + H*(p) χ`. -/
def kappa1 (P : Branch2.VCubic) : Coef := fun u v p => P.eh + P.Hstar p * chiA u v

lemma integral_kappa1 (P : Branch2.VCubic) (p : ℝ) :
    torusInt (fun u v => kappa1 P u v p) = 3 * (1 - 3 * p) := by
  unfold torusInt kappa1
  have hc : ∀ v, Continuous (fun u => chiA u v) := fun v =>
    contDiff_chiA.continuous.comp (continuous_id.prodMk continuous_const)
  have e : ∀ v, ∫ u in (0 : ℝ)..1, (P.eh + P.Hstar p * chiA u v) =
      P.eh + P.Hstar p * ∫ u in (0 : ℝ)..1, chiA u v := by
    intro v
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (((hc v).intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const_mul]
    simp
  simp only [e]
  have hc2 : Continuous (fun v => ∫ u in (0 : ℝ)..1, chiA u v) := by
    unfold chiA
    simp only [intervalIntegral.integral_mul_const]
    exact continuous_const.mul contDiff_bB.continuous
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((hc2.intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const_mul]
  have := integral_chi
  unfold torusInt at this
  rw [this]
  simp [Branch2.CubicData.Hstar, Branch2.CubicData.Hb]

/-- **Positivity of `κ`, `κ₁`** (`lem:fer-kappa`): for `p ≤ h` both are positive, and
`κ₁(p) ≥ e_h > 0` whenever `H*(p) ≥ 0`. -/
theorem kappa_pos (P : Branch2.VCubic) :
    (∀ u v p, p ≤ P.h → 0 < kappa u v p ∧ 0 < kappa1 P u v p) ∧
    (∀ u v p, 0 ≤ P.Hstar p → P.eh ≤ kappa1 P u v p) ∧ 0 < P.eh := by
  have heh : 0 < P.eh := by unfold Branch2.CubicData.eh; linarith [P.g_pos]
  have hk1 : ∀ u v p, 0 ≤ P.Hstar p → P.eh ≤ kappa1 P u v p := fun u v p hH => by
    unfold kappa1; nlinarith [chiA_nonneg u v]
  refine ⟨fun u v p hp => ⟨?_, ?_⟩, hk1, heh⟩
  · unfold kappa
    have : 0 < 1 - 3 * p := by
      have := P.h_lt_third; linarith
    exact mul_pos this (sigmaC_pos u v)
  · have := P.Hstar_ge hp
    exact lt_of_lt_of_le heh (hk1 u v p (by linarith [P.g_pos]))

lemma contDiff_kappa1 (P : Branch2.VCubic) (p : ℝ) : ContDiff ℝ ∞ (sl (kappa1 P) p) :=
  contDiff_const.add (contDiff_const.mul contDiff_chiA)

lemma kappa1_affine (P : Branch2.VCubic) : AffineP (kappa1 P) :=
  AffineP.of_eq (fun u v => P.eh + (3 - P.eh) * chiA u v) (fun u v => -9 * chiA u v)
    fun u v p => by simp only [kappa1, Branch2.CubicData.Hstar, Branch2.CubicData.Hb]; ring

/-! ### The torus primitive operator (`def:fer-Pprim`) -/

section Pprim

variable {b : Coef}

end Pprim

/-! ### `α₁⁰` (`def:fer-Delta`) -/

/-- The exact base two-form `κ₁ − κ`. -/
def kdiff (P : Branch2.VCubic) : Coef := kappa1 P - kappa

lemma contDiff_kdiff (P : Branch2.VCubic) (p : ℝ) : ContDiff ℝ ∞ (sl (kdiff P) p) :=
  (contDiff_kappa1 P p).sub (contDiff_kappa p)

lemma kdiff_periodic (P : Branch2.VCubic) : CoefPeriodic (kdiff P) := by
  intro u v p
  constructor <;> simp only [kdiff, Pi.sub_apply, kappa1, kappa, (sigmaC_periodic u v).1,
    (sigmaC_periodic u v).2, (chiA_periodic u v).1, (chiA_periodic u v).2]

attribute [local irreducible] sigmaC chiA in
lemma integral_kdiff (P : Branch2.VCubic) (p : ℝ) : torusInt (fun u v => kdiff P u v p) = 0 := by
  have h1 := integral_kappa1 P p
  have h2 := integral_kappa p
  unfold torusInt at h1 h2 ⊢
  show ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, (kappa1 P u v p - kappa u v p) = 0
  have hc1 : ∀ v, IntervalIntegrable (fun u => kappa1 P u v p) volume 0 1 := fun v =>
    ((contDiff_kappa1 P p).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hc2 : ∀ v, IntervalIntegrable (fun u => kappa u v p) volume 0 1 := fun v =>
    ((contDiff_kappa p).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have e : ∀ v, ∫ u in (0 : ℝ)..1, (kappa1 P u v p - kappa u v p) =
      (∫ u in (0 : ℝ)..1, kappa1 P u v p) - ∫ u in (0 : ℝ)..1, kappa u v p := fun v =>
    intervalIntegral.integral_sub (hc1 v) (hc2 v)
  simp only [e]
  rw [intervalIntegral.integral_sub, h1, h2, sub_self]
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v u => kappa1 P u v p) ((contDiff_kappa1 P p).continuous.comp continuous_swap)
      0 1).intervalIntegrable _ _
  · have hk : Continuous (Function.uncurry fun v u => kappa u v p) :=
      (contDiff_kappa p).continuous.comp continuous_swap
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v u => kappa u v p) hk 0 1).intervalIntegrable _ _

/-- **`α₁⁰(p) = P_prim(κ₁(p) − κ(p))`** (`def:fer-Delta`). -/
def alpha10 (P : Branch2.VCubic) : BForm := Pprim (kdiff P)

/-- `d_C α₁⁰ = κ₁ − κ`. -/
theorem d_alpha10 (P : Branch2.VCubic) (u v p : ℝ) :
    (alpha10 P).dC u v p = kappa1 P u v p - kappa u v p :=
  d_Pprim (contDiff_kdiff P p).continuous u v

theorem alpha10_periodic (P : Branch2.VCubic) : (alpha10 P).Periodic :=
  Pprim_periodic (fun p => (contDiff_kdiff P p).continuous) (kdiff_periodic P) (integral_kdiff P)

theorem alpha10_affine (P : Branch2.VCubic) : AffineP (alpha10 P).cu ∧ AffineP (alpha10 P).cv :=
  Pprim_affine ((kappa1_affine P).sub kappa_affine) (contDiff_kdiff P 0).continuous
    (contDiff_kdiff P 1).continuous

end SymplecticPacking.Bundle.Cubic
