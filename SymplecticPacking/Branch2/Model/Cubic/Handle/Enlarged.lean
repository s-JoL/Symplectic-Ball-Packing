import SymplecticPacking.Handle.Layers
import SymplecticPacking.Bundle.OmegaT
import SymplecticPacking.Branch2.Model.Cubic.Handle.Layers
import SymplecticPacking.Branch2.Model.Cubic.Bundle.OmegaT

/-!
# The enlarged moment bound `δ_m`

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`def:shd4-scalars`, `lem:shd4-budget`): the enlarged moment bound `δ_m` and the
scalar positivity estimates on the open domain `{p < h + 2δ_m}`.

* `deltam P = min((d_n − h)/4, g/100)`;
* `deltam_one_sub`: `p < h + 2δ_m ⟹ p < d_n` and `1 − 3p > 0`;
* `deltam_Hstar`: `H*(p) ≥ 15g/16 − 9(p − h)₊ > 15g/16 − 18δ_m > 0`;
* `deltam_residual`: `R*(w) > 0` for `p(w) < h + 2δ_m`; for `p(w) ≥ h`,
  `R*(w) = H*(p) − ∑ h_i(p) ≥ 29g/32 − 9(p − h)`;
* `deltam_kappaT`: `κ_t > 0` on `{p < h + 2δ_m}`, `t ∈ [0, 1]`.
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set
open SymplecticPacking.Qhat.Cubic (qhatInvP Psupp)
open scoped Real

variable (P : Branch2.VCubic)

/-- **The enlarged moment bound** `δ_m = min((d_n − h)/4, g/100)`. -/
def deltam : ℝ := min ((P.dn - P.h) / 4) (P.g / 100)

lemma deltam_pos : 0 < deltam P :=
  lt_min (by linarith [P.h_lt_dn]) (by linarith [P.g_pos])

lemma deltam_le_dn : deltam P ≤ (P.dn - P.h) / 4 := min_le_left _ _
lemma deltam_le_g : deltam P ≤ P.g / 100 := min_le_right _ _

/-- **`lem:shd4-budget`(a)**. -/
theorem deltam_one_sub {p : ℝ} (hp : p < P.h + 2 * deltam P) : p < P.dn ∧ 0 < 1 - 3 * p := by
  have := deltam_le_dn P
  have := P.h_lt_dn
  have := P.dn_lt_third
  constructor <;> linarith

/-- `H*(h) ≥ 15g/16` (an equality for the equal-ball parameters). -/
lemma Hstar_h : 15 * P.g / 16 ≤ P.Hstar P.h := P.Hstar_h_ge

/-- **`lem:shd4-budget`(b)**. -/
theorem deltam_Hstar {p : ℝ} (hp : p < P.h + 2 * deltam P) :
    15 * P.g / 16 - 9 * max (p - P.h) 0 ≤ P.Hstar p ∧
      15 * P.g / 16 - 18 * deltam P < 15 * P.g / 16 - 9 * max (p - P.h) 0 ∧
      0 < 15 * P.g / 16 - 18 * deltam P := by
  have hd := deltam_pos P
  have hg := deltam_le_g P
  have hg0 := P.g_pos
  have e : P.Hstar p = P.Hstar P.h - 9 * (p - P.h) := P.Hstar_sub _ _
  have hh := Hstar_h P
  refine ⟨?_, ?_, by linarith⟩
  · rw [e]
    rcases le_total p P.h with h | h
    · rw [max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (by linarith)]; linarith
  · rcases le_total p P.h with h | h
    · rw [max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (by linarith)]; linarith

lemma Hstar_pos_of {p : ℝ} (hp : p < P.h + 2 * deltam P) : 0 < P.Hstar p := by
  obtain ⟨h1, h2, h3⟩ := deltam_Hstar P hp; linarith

/-- **`lem:shd4-budget`(c)**. -/
theorem deltam_residual {w : ℂ} (hw : π * ‖w‖ ^ 2 < P.h + 2 * deltam P) :
    0 < Rstar P w ∧
      (P.h ≤ π * ‖w‖ ^ 2 →
        Rstar P w = P.Hstar (π * ‖w‖ ^ 2) - ∑ i ∈ Finset.Icc 1 P.k, P.hi i (π * ‖w‖ ^ 2) ∧
        29 * P.g / 32 - 9 * (π * ‖w‖ ^ 2 - P.h) ≤ Rstar P w) := by
  have hg0 := P.g_pos
  have hd := deltam_le_g P
  have hupper : P.h ≤ π * ‖w‖ ^ 2 →
      Rstar P w = P.Hstar (π * ‖w‖ ^ 2) - ∑ i ∈ Finset.Icc 1 P.k, P.hi i (π * ‖w‖ ^ 2) ∧
      29 * P.g / 32 - 9 * (π * ‖w‖ ^ 2 - P.h) ≤ Rstar P w := by
    intro hh
    have hq : qhatInvP P 1 w = w := qhatInvP_collar P (lt_of_lt_of_le (Psupp_lt_h P) hh)
    have hR : Rstar P w = P.Hstar (π * ‖w‖ ^ 2) - ∑ i ∈ Finset.Icc 1 P.k,
        P.hi i (π * ‖w‖ ^ 2) := by
      rw [Rstar, hq]; unfold Branch2.CubicData.J; ring
    refine ⟨hR, ?_⟩
    rw [hR]
    have h1 := P.sum_hi_le (π * ‖w‖ ^ 2)
    have h0 : ∑ i ∈ Finset.Icc 1 P.k, max (P.a i - π * ‖w‖ ^ 2) 0 = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have := P.a_lt_h (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
        exact max_eq_right (by linarith)
    rw [h0, zero_add] at h1
    have e : P.Hstar (π * ‖w‖ ^ 2) = P.Hstar P.h - 9 * (π * ‖w‖ ^ 2 - P.h) := P.Hstar_sub _ _
    have := Hstar_h P
    rw [e]; linarith
  refine ⟨?_, hupper⟩
  rcases le_or_gt (π * ‖w‖ ^ 2) P.h with h | h
  · have := Rstar_ge P h; linarith
  · have := (hupper h.le).2; linarith

/-- `κ_t = (1 − t)κ + tκ₁ > 0` on `{p < h + 2δ_m}` for `t ∈ [0, 1]`. -/
theorem deltam_kappaT {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u v : ℝ) {p : ℝ}
    (hp : p < P.h + 2 * deltam P) : 0 < Bundle.Cubic.kappaT P t u v p :=
  Bundle.Cubic.kappaT_pos P ht (deltam_one_sub P hp).2 (Hstar_pos_of P hp).le

end SymplecticPacking.Handle.Cubic
