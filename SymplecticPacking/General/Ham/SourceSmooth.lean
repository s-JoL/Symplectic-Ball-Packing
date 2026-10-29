import SymplecticPacking.General.Ham.Primitive
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy

/-!
# Joint smoothness of the source primitive

`sec:ham-hamiltonian`: joint smoothness of the source primitive `(t,u) ↦ h_t(u)` on `ℝ × B(ρ')`, `ρ' < ρ`.

The integrand `(r, t, u) ↦ a_t(r u)[u]` is only known to be smooth where `r u ∈ B(ρ)`; we multiply
it by a radial cutoff in `r u` that is `1` on `B̄(ρ')` and vanishes outside `B(ρ'')`, which makes it
smooth everywhere without changing the integral over `r ∈ [0,1]` for `u ∈ B(ρ')`, and apply the
fixed-interval parametric integral lemma of the vendored OAI library.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter ContinuousLinearMap Problem
open scoped ContDiff Topology

variable {n : ℕ}

/-- If `f` is smooth on an open set `O` and `c` is smooth with `tsupport c ⊆ O`, then `c * f` is
smooth everywhere. -/
lemma contDiff_mul_of_tsupport {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c f : X → ℝ} {O : Set X} (hO : IsOpen O) (hc : ContDiff ℝ ∞ c) (hf : ContDiffOn ℝ ∞ f O)
    (hcO : tsupport c ⊆ O) : ContDiff ℝ ∞ (fun x => c x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hc.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport c := fun h => hx (hcO h)
    have hev : (fun x => c x * f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq (f := c) (x := x)).mp hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma tsupport_radialCutoff_subset {ron roff : ℝ} (h : ron < roff) (h0 : 0 ≤ ron) :
    tsupport (radialCutoff (n := n) ron roff) ⊆ closedBall (0 : E n) roff := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hy'
  rw [mem_closedBall_zero_iff, not_le] at hy'
  exact hy (radialCutoff_eq_zero h h0 hy'.le)

variable {F : ℝ → E n → E n} {ρ : ℝ}

/-- `oneForm` is jointly smooth in `(t, y)` on `ℝ × B(ρ)`. -/
lemma contDiffOn_oneForm (hsm : ContDiffOn ℝ ∞ (unc F) (univ ×ˢ ball (0 : E n) ρ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => oneForm F p.1 p.2) (univ ×ˢ ball (0 : E n) ρ) := by
  have hO : IsOpen (univ ×ˢ ball (0 : E n) ρ) := (isOpen_univ (X := ℝ)).prod isOpen_ball
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (unc F)) (univ ×ˢ ball (0 : E n) ρ) :=
    hsm.fderiv_of_isOpen hO (by simp)
  unfold oneForm
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × E n => omega0L (fderiv ℝ (unc F) p (1, 0)))
      (univ ×ˢ ball (0 : E n) ρ) :=
    omega0L.contDiff.comp_contDiffOn (hD.clm_apply contDiffOn_const)
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × E n => (fderiv ℝ (unc F) p).comp (inr ℝ ℝ (E n)))
      (univ ×ˢ ball (0 : E n) ρ) := hD.clm_comp contDiffOn_const
  exact h1.clm_comp h2

/-- The cut-off integrand. -/
def cutIntegrand (F : ℝ → E n → E n) (ρ' ρ'' : ℝ) (q : ℝ × (ℝ × E n)) : ℝ :=
  radialCutoff ρ' ρ'' (q.1 • q.2.2) * oneForm F q.2.1 (q.1 • q.2.2) q.2.2

lemma contDiff_cutIntegrand (hsm : ContDiffOn ℝ ∞ (unc F) (univ ×ˢ ball (0 : E n) ρ))
    {ρ' ρ'' : ℝ} (h0 : 0 ≤ ρ') (h1 : ρ' < ρ'') (h2 : ρ'' < ρ) :
    ContDiff ℝ ∞ (cutIntegrand F ρ' ρ'') := by
  set O : Set (ℝ × (ℝ × E n)) := {q | q.1 • q.2.2 ∈ ball (0 : E n) ρ}
  have hO : IsOpen O := isOpen_ball.preimage (continuous_fst.smul continuous_snd.snd)
  have hsmul : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × E n) => q.1 • q.2.2) :=
    contDiff_fst.smul contDiff_snd.snd
  have hc : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × E n) => radialCutoff ρ' ρ'' (q.1 • q.2.2)) :=
    radialCutoff_contDiff.comp hsmul
  have hf : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × E n) => oneForm F q.2.1 (q.1 • q.2.2) q.2.2) O := by
    have hA := (contDiffOn_oneForm hsm).comp (contDiff_snd.fst.prodMk hsmul).contDiffOn
      (s := O) (fun q hq => ⟨mem_univ _, hq⟩)
    exact hA.clm_apply contDiff_snd.snd.contDiffOn
  apply contDiff_mul_of_tsupport hO hc hf
  intro q hq
  have hq' : q.1 • q.2.2 ∈ tsupport (radialCutoff ρ' ρ'') :=
    tsupport_comp_subset_preimage (radialCutoff ρ' ρ'') hsmul.continuous hq
  have := tsupport_radialCutoff_subset h1 h0 hq'
  rw [mem_closedBall_zero_iff] at this
  exact mem_ball_zero_iff.mpr (lt_of_le_of_lt this h2)

/-- **Joint smoothness of the source primitive** on `ℝ × B(ρ')`, for `ρ' < ρ`. -/
theorem contDiffOn_sourcePrimitive (hF : SympFamily F ρ)
    (hsm : ContDiffOn ℝ ∞ (unc F) (univ ×ˢ ball (0 : E n) ρ)) {ρ' : ℝ} (h0 : 0 ≤ ρ')
    (h1 : ρ' < ρ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => sourcePrimitive F p.1 p.2) (univ ×ˢ ball (0 : E n) ρ') := by
  set ρ'' := (ρ' + ρ) / 2
  have hI := OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral
    (contDiff_cutIntegrand hsm (ρ'' := ρ'') h0 (by simp only [ρ'']; linarith)
      (by simp only [ρ'']; linarith))
  apply hI.contDiffOn.congr
  rintro ⟨t, u⟩ ⟨-, hu⟩
  rw [mem_ball_zero_iff] at hu
  simp only [sourcePrimitive]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le zero_le_one] at hr
  have hru : ‖r • u‖ ≤ ‖u‖ := by
    rw [norm_smul, Real.norm_of_nonneg hr.1]
    calc r * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact hr.2
      _ = ‖u‖ := one_mul _
  have hruρ : r • u ∈ ball (0 : E n) ρ := mem_ball_zero_iff.mpr (by linarith)
  simp only [cutIntegrand]
  rw [radialCutoff_eq_one (by simp only [ρ'']; linarith) h0 (by linarith), one_mul,
    sourceOneForm_eq (hF.differentiableAt hruρ)]

end SymplecticPacking.General.Ham
