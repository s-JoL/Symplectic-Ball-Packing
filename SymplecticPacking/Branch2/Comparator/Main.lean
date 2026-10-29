import SymplecticPacking.Branch2.Comparator.FixedPoint
import SymplecticPacking.Branch2.Comparator.Smooth

/-!
# The comparison function for `m = 1` (`thm:cmp-main`, scalar half)

`Kcmp D = smoothK h M w K_N` with `M = L_P/(1-λ)` (the Lipschitz constant of all iterates) and
`w = d/(32(M+1))`. Then `K` is `C^∞` and convex on `ℝ`, `|K - K_N| ≤ d/32` on `[0,h]`, and
`R(K - P) ≤ K - 13d/16` on `[0, h]` (`Kcmp_gap`).
-/

noncomputable section

namespace SymplecticPacking.Branch2.Cmp

open Set
open scoped ContDiff

namespace Input

variable (D : Input)

/-- Mollification scale `w = d/(32(M+1))`. -/
def wSmooth : ℝ := D.d / (32 * (D.lipK + 1))

/-- **The smooth comparison function** `K`. -/
def Kcmp : ℝ → ℝ := smoothK D.h D.lipK D.wSmooth D.KN

variable {D}

lemma Hyp.lipK_nonneg (hD : D.Hyp) : 0 ≤ D.lipK :=
  div_nonneg hD.LP_nonneg (by linarith [hD.lam_bounds.2])

lemma Hyp.wSmooth_pos (hD : D.Hyp) : 0 < D.wSmooth :=
  div_pos hD.d_pos (by linarith [hD.lipK_nonneg])

lemma Hyp.lipK_mul_w (hD : D.Hyp) : D.lipK * D.wSmooth ≤ D.d / 32 := by
  have hM := hD.lipK_nonneg
  have hd := hD.d_pos
  unfold wSmooth
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem Hyp.Kcmp_contDiff (hD : D.Hyp) : ContDiff ℝ ∞ D.Kcmp :=
  smoothK_contDiff hD.h_pos.le hD.lipK_nonneg hD.wSmooth_pos (hD.iter_continuousOn _)

theorem Hyp.Kcmp_convex (hD : D.Hyp) : ConvexOn ℝ univ D.Kcmp :=
  smoothK_convex hD.h_pos.le hD.lipK_nonneg hD.wSmooth_pos (hD.iter_continuousOn _)
    (hD.iter_convexOn _)

theorem Hyp.Kcmp_close (hD : D.Hyp) {p : ℝ} (hp : p ∈ Icc 0 D.h) :
    |D.Kcmp p - D.KN p| ≤ D.d / 32 :=
  (smoothK_close hD.h_pos.le hD.lipK_nonneg hD.wSmooth_pos (hD.iter_continuousOn _)
    (hD.iter_lipschitz _) hp).trans hD.lipK_mul_w

/-- **The scalar comparison**: `R(K - P) ≤ K - 13d/16` on `[0, h]`. -/
theorem Hyp.Kcmp_gap (hD : D.Hyp) {I : ℝ} (hI : I ∈ Icc 0 D.h) :
    rearr D.h (fun p => D.Kcmp p - D.P p) I ≤ D.Kcmp I - 13 * D.d / 16 := by
  have hKc : ContinuousOn D.Kcmp (Icc 0 D.h) :=
    (hD.Kcmp_contDiff.continuous).continuousOn
  have hKN := hD.iter_continuousOn D.nSteps
  have h1 := rearr_le_add (f := fun p => D.Kcmp p - D.P p) (g := fun p => D.KN p - D.P p)
    (hKc.sub hD.cont.continuousOn) (hKN.sub hD.cont.continuousOn) hI (ε := D.d / 32)
    (fun x hx => by have := (_root_.abs_le.1 (hD.Kcmp_close hx)).2; linarith)
  have h2 := hD.KN_gap hI
  have h3 := (_root_.abs_le.1 (hD.Kcmp_close hI)).1
  linarith

end Input

end SymplecticPacking.Branch2.Cmp
