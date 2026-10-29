import Mathlib
import SymplecticPacking.Explicit

/-!
# Inverse of a proper strictly increasing function

Generic inverse of a strictly increasing proper continuous function `ℝ → ℝ`, defined by
definite description (`Explicit.the`), with smoothness via the one-dimensional inverse
function theorem. Used for `Xtilde = f_R⁻¹` and `Ytilde = f_V⁻¹` of `sec:pll-morse`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology
open scoped ContDiff

open Classical in
/-- The inverse of `f` (written `Σ` in the paper): the unique preimage of `y` if it exists, `0` otherwise. -/
def invR (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  if h : ∃! x, f x = y then Explicit.the h else 0

section

variable {f : ℝ → ℝ}

theorem invR_eq_of_apply_eq (hinj : Function.Injective f) {x y : ℝ} (hx : f x = y) :
    invR f y = x := by
  have h : ∃! x, f x = y := ⟨x, hx, fun z hz => hinj (hz.trans hx.symm)⟩
  unfold invR
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Explicit.the_eq h hx

theorem invR_apply (hinj : Function.Injective f) (x : ℝ) : invR f (f x) = x :=
  invR_eq_of_apply_eq hinj rfl

theorem apply_invR (hinj : Function.Injective f) (hsurj : Function.Surjective f) (y : ℝ) :
    f (invR f y) = y := by
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invR_apply hinj]

variable (hc : Continuous f) (hm : StrictMono f) (ht : Tendsto f atTop atTop)
  (hb : Tendsto f atBot atBot)
include hc hm ht hb

omit hm in
theorem surjective_of_proper : Function.Surjective f := hc.surjective ht hb

theorem apply_invR' (y : ℝ) : f (invR f y) = y :=
  apply_invR hm.injective (surjective_of_proper hc ht hb) y

omit hc ht hb in
theorem invR_apply' (x : ℝ) : invR f (f x) = x := invR_apply hm.injective x

theorem invR_strictMono : StrictMono (invR f) := by
  intro y₁ y₂ hy
  have h1 := apply_invR' hc hm ht hb y₁
  have h2 := apply_invR' hc hm ht hb y₂
  by_contra hle
  have := hm.monotone (not_lt.mp hle)
  rw [h1, h2] at this
  linarith

theorem invR_continuous : Continuous (invR f) :=
  (invR_strictMono hc hm ht hb).monotone.continuous_of_surjective
    fun x => ⟨f x, invR_apply' hm x⟩

/-- `f` as a homeomorphism of `ℝ` whose inverse is `invR f`. -/
def invRHomeomorph : ℝ ≃ₜ ℝ where
  toFun := f
  invFun := invR f
  left_inv := invR_apply' hm
  right_inv := apply_invR' hc hm ht hb
  continuous_toFun := hc
  continuous_invFun := invR_continuous hc hm ht hb

omit hc ht hb in
/-- If `f x = c x` on `[-a, a]` (`c > 0`), then `invR f y = y / c` for `|y| ≤ c a`. -/
theorem invR_linear {c a : ℝ} (hcpos : 0 < c) (hlin : ∀ x, |x| ≤ a → f x = c * x) {y : ℝ}
    (hy : |y| ≤ c * a) : invR f y = y / c := by
  apply invR_eq_of_apply_eq hm.injective
  rw [hlin _ ?_]
  · field_simp
  · rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]; linarith

variable {f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 < f' x)
include hd hpos

theorem hasDerivAt_invR (y : ℝ) : HasDerivAt (invR f) (f' (invR f y))⁻¹ y :=
  HasDerivAt.of_local_left_inverse (invR_continuous hc hm ht hb).continuousAt (hd _)
    (hpos _).ne' (Eventually.of_forall (apply_invR' hc hm ht hb))

theorem deriv_invR (y : ℝ) : deriv (invR f) y = 1 / f' (invR f y) := by
  rw [(hasDerivAt_invR hc hm ht hb hd hpos y).deriv, one_div]

theorem deriv_invR_pos (y : ℝ) : 0 < deriv (invR f) y := by
  rw [deriv_invR hc hm ht hb hd hpos]; exact one_div_pos.mpr (hpos _)

theorem invR_contDiff {n : WithTop ℕ∞} (hs : ContDiff ℝ n f) : ContDiff ℝ n (invR f) :=
  (invRHomeomorph hc hm ht hb).contDiff_symm_deriv (fun x => (hpos x).ne') hd hs

end

/-- Version with `deriv`: a `C^∞` function with positive derivative, proper at `±∞`. -/
theorem invR_contDiff_of_deriv {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < deriv f x)
    (ht : Tendsto f atTop atTop) (hb : Tendsto f atBot atBot) :
    ContDiff ℝ ∞ (invR f) ∧ ∀ y, deriv (invR f) y = 1 / deriv f (invR f y) := by
  have hdiff : Differentiable ℝ f := hs.differentiable (by simp)
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x => (hdiff x).hasDerivAt
  have hm : StrictMono f := strictMono_of_deriv_pos hpos
  exact ⟨invR_contDiff hdiff.continuous hm ht hb hd hpos hs,
    deriv_invR hdiff.continuous hm ht hb hd hpos⟩

end SymplecticPacking.Inner
