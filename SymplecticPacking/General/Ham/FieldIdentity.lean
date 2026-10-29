import SymplecticPacking.General.Ham.Primitive

/-!
# The Hamiltonian vector field on the balls

`sec:ham-hamiltonian`, formula (26): on the unit balls the Hamiltonian vector field of `H = ofIsotopy F r₁ r₂ r₃`
is the velocity of the isotopy, `X_H(t, F_i t u) = ∂_t F_i t u` for `‖u‖ < r₁`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter ContinuousLinearMap Problem
open scoped ContDiff Topology

variable {n : ℕ}

variable {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n} {r1 r2 r3 ρ : Fin k → ℝ}

lemma CommonIsotopy.sympFamily (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) :
    SympFamily (F i) (ρ i) where
  smooth _ _ hy := (hF.smooth i).contDiffAt
    (prod_mem_nhds univ_mem (isOpen_ball.mem_nhds hy))
  sympl s y hy := hF.sympl i s y hy

/-- **Formula (26).** For `‖u₀‖ < r₁`: `X_H(t, F_i t u₀) = ∂_t F_i t u₀`. -/
theorem hamVF_ofIsotopy_image (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) (t : ℝ)
    {u₀ : E n} (hu₀ : ‖u₀‖ < r1 i) :
    Problem.hamVF (ofIsotopy F r1 r2 r3) t (F i t u₀) = deriv (fun s => F i s u₀) t := by
  obtain ⟨h1r1, hr12, hr23, hr3ρ⟩ := hF.radii i
  have hS := hF.sympFamily i
  have hu₀ρ : u₀ ∈ ball (0 : E n) (ρ i) := mem_ball_zero_iff.mpr (by linarith)
  have hdiff := hS.differentiableAt (s := t) hu₀ρ
  -- strict derivative of the slice and its inverse
  have hcd : ContDiffAt ℝ ∞ (F i t) u₀ := by
    have h := hS.smooth t u₀ hu₀ρ
    exact h.comp u₀ (contDiffAt_const.prodMk contDiffAt_id)
  set A := fderiv ℝ (F i t) u₀
  have hA : IsSymplecticLinear A := hF.sympl i t u₀ hu₀ρ
  set e := symplEquiv hA
  have hstrict : HasStrictFDerivAt (F i t) (e : E n →L[ℝ] E n) u₀ := by
    rw [symplEquiv_coe]; exact hcd.hasStrictFDerivAt (by simp)
  set g := hstrict.localInverse (F i t) e u₀
  have hg : HasFDerivAt g (e.symm : E n →L[ℝ] E n) (F i t u₀) := hstrict.to_localInverse.hasFDerivAt
  have hgu : g (F i t u₀) = u₀ := hstrict.localInverse_apply_image
  have hgc : ContinuousAt g (F i t u₀) := hstrict.localInverse_continuousAt
  -- near `F u₀`, `H t = h_t ∘ g`
  have hball : ball u₀ (r1 i - ‖u₀‖) ∈ 𝓝 u₀ := ball_mem_nhds u₀ (by linarith)
  have hev : ofIsotopy F r1 r2 r3 t =ᶠ[𝓝 (F i t u₀)] fun y => sourcePrimitive (F i) t (g y) := by
    have hnear : ∀ᶠ y in 𝓝 (F i t u₀), g y ∈ ball u₀ (r1 i - ‖u₀‖) :=
      hgc.preimage_mem_nhds (by rw [hgu]; exact hball)
    filter_upwards [hnear, hstrict.eventually_right_inverse] with y hy hy'
    have hgy : ‖g y‖ < r1 i := by
      have := norm_le_norm_add_norm_sub' (g y) u₀
      rw [mem_ball, dist_eq_norm] at hy
      linarith
    have hgy3 : g y ∈ closedBall (0 : E n) (r3 i) := mem_closedBall_zero_iff.mpr (by linarith)
    have := ofIsotopy_apply_image (r1 := r1) (r2 := r2) (fun j => hF.inj j t)
      (fun j hji => hF.disj j i t hji) hgy3
    rw [hy'] at this
    rw [this, radialCutoff_eq_one hr12 (by linarith) hgy.le, one_mul]
  have hprim := hasFDerivAt_sourcePrimitive hS (t := t) (b := g (F i t u₀)) (by rw [hgu]; exact hu₀ρ)
  have hcomp := (hprim.comp (F i t u₀) hg).congr_of_eventuallyEq hev
  apply hamVF_eq_of_hasFDerivAt hcomp
  intro w
  rw [hgu]
  simp only [coe_comp, Function.comp_apply, oneForm, omega0L_apply, ContinuousLinearEquiv.coe_coe]
  rw [← (hasDerivAt_time hdiff).deriv]
  congr 1
  have h1 : (fderiv ℝ (unc (F i)) (t, u₀)).comp (inr ℝ ℝ (E n)) = A :=
    (hasFDerivAt_slice hdiff).fderiv.symm
  have h2 : (fderiv ℝ (unc (F i)) (t, u₀)).comp (inr ℝ ℝ (E n)) (e.symm w) = w := by
    rw [h1]; exact e.apply_symm_apply w
  exact h2

end SymplecticPacking.General.Ham
