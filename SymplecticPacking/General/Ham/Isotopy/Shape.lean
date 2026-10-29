import SymplecticPacking.General.Ham.SourceSmooth

/-!
# The relative nonlinear shape

`sec:iso-shape`, formulas (18)–(19): the relative nonlinear shape
`κ_s(u) = ∫₀¹ Df(σ s u) u dσ`, which equals `(f(su) - f(0))/s` for `s ≠ 0` and `Df(0) u` for
`s = 0`, has spatial derivative `Df(s u)`, and is jointly smooth in `(s, u)`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Filter ContinuousLinearMap SymplecticPacking.General.Ham Problem
open scoped ContDiff Topology

/-- The shape family (18). -/
def shape {n : ℕ} (f : E n → E n) (s : ℝ) (u : E n) : E n :=
  ∫ σ in (0 : ℝ)..1, fderiv ℝ f (σ • (s • u)) u

variable {n : ℕ} {f : E n → E n} {ρ : ℝ}

lemma shape_zero (u : E n) : shape f 0 u = fderiv ℝ f 0 u := by
  simp [shape]

lemma norm_smul_le_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (x : E n) : ‖σ • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg hσ.1]
  calc σ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr; exact hσ.2
    _ = ‖x‖ := one_mul _

/-- `(18)` for `s ≠ 0`: `s κ_s(u) = f(su) - f(0)` when `s u ∈ B(ρ)`. -/
theorem smul_shape (hf : ContDiffOn ℝ ∞ f (ball 0 ρ)) {s : ℝ} {u : E n}
    (hsu : s • u ∈ ball (0 : E n) ρ) : s • shape f s u = f (s • u) - f 0 := by
  have hseg : ∀ σ ∈ Icc (0 : ℝ) 1, σ • (s • u) ∈ ball (0 : E n) ρ := fun σ hσ =>
    mem_ball_zero_iff.mpr ((norm_smul_le_of_mem_Icc hσ _).trans_lt (mem_ball_zero_iff.mp hsu))
  have hderiv : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun σ : ℝ => f (σ • (s • u)))
      (fderiv ℝ f (σ • (s • u)) (s • u)) σ := by
    intro σ hσ
    rw [uIcc_of_le zero_le_one] at hσ
    have hd : DifferentiableAt ℝ f (σ • (s • u)) :=
      (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds (hseg σ hσ))
    have h1 : HasDerivAt (fun σ : ℝ => σ • (s • u)) (s • u) σ := by
      simpa using (hasDerivAt_id σ).smul_const (s • u)
    exact hd.hasFDerivAt.comp_hasDerivAt σ h1
  have hcont : ContinuousOn (fun σ : ℝ => fderiv ℝ f (σ • (s • u)) (s • u)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    have hD : ContinuousOn (fderiv ℝ f) (ball 0 ρ) :=
      (hf.continuousOn_fderiv_of_isOpen isOpen_ball (by simp))
    exact (hD.comp (continuous_id.smul continuous_const).continuousOn hseg).clm_apply
      continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  simp only [one_smul, zero_smul] at hFTC
  rw [← hFTC, shape, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [map_smul]

/-- `κ_s(u) = (f(su) - f(0)) / s` for `s ≠ 0`. -/
theorem shape_eq (hf : ContDiffOn ℝ ∞ f (ball 0 ρ)) {s : ℝ} (hs : s ≠ 0) {u : E n}
    (hsu : s • u ∈ ball (0 : E n) ρ) : shape f s u = s⁻¹ • (f (s • u) - f 0) := by
  rw [← smul_shape hf hsu, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- **(19)**: `D_u κ_s(u) = Df(s u)`. -/
theorem hasFDerivAt_shape (hf : ContDiffOn ℝ ∞ f (ball 0 ρ)) {s : ℝ} {u : E n}
    (hsu : s • u ∈ ball (0 : E n) ρ) :
    HasFDerivAt (shape f s) (fderiv ℝ f (s • u)) u := by
  by_cases hs : s = 0
  · subst hs
    have : shape f 0 = fderiv ℝ f 0 := funext shape_zero
    rw [this, zero_smul]
    exact (fderiv ℝ f 0).hasFDerivAt
  · -- near `u`, `κ_s = s⁻¹ (f(s ·) - f 0)`
    have hopen : {v : E n | s • v ∈ ball (0 : E n) ρ} ∈ 𝓝 u :=
      (isOpen_ball.preimage (continuous_const_smul s)).mem_nhds hsu
    have hev : (fun v => s⁻¹ • (f (s • v) - f 0)) =ᶠ[𝓝 u] shape f s := by
      filter_upwards [hopen] with v hv using (shape_eq hf hs hv).symm
    have hd : DifferentiableAt ℝ f (s • u) :=
      (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hsu)
    have h1 : HasFDerivAt (fun v : E n => s • v) (s • ContinuousLinearMap.id ℝ (E n)) u :=
      (hasFDerivAt_id u).const_smul s
    have h2 := ((hd.hasFDerivAt.comp u h1).sub_const (f 0)).const_smul s⁻¹
    apply (h2.congr_of_eventuallyEq hev.symm).congr_fderiv
    ext v
    simp [smul_smul, inv_mul_cancel₀ hs]

/-- **Bound**: `‖κ_s(u)‖ ≤ L ‖u‖` if `‖Df‖ ≤ L` on `B̄(R)` and `‖s u‖ ≤ R`. -/
theorem norm_shape_le {L R : ℝ} (hL : ∀ y ∈ closedBall (0 : E n) R, ‖fderiv ℝ f y‖ ≤ L)
    {s : ℝ} {u : E n} (hsu : ‖s • u‖ ≤ R) : ‖shape f s u‖ ≤ L * ‖u‖ := by
  unfold shape
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := L * ‖u‖) (f := fun σ => fderiv ℝ f (σ • (s • u)) u) (by
      intro σ hσ
      rw [uIoc_of_le zero_le_one] at hσ
      have hy : σ • (s • u) ∈ closedBall (0 : E n) R := mem_closedBall_zero_iff.mpr
        ((norm_smul_le_of_mem_Icc ⟨hσ.1.le, hσ.2⟩ _).trans hsu)
      exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hL _ hy) (norm_nonneg _)))
  simpa using this

/-! ### Joint smoothness -/

/-- Vector-valued version of `contDiff_mul_of_tsupport`. -/
lemma contDiff_smul_of_tsupport {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {c : X → ℝ} {g : X → Y} {O : Set X} (hO : IsOpen O) (hc : ContDiff ℝ ∞ c)
    (hg : ContDiffOn ℝ ∞ g O) (hcO : tsupport c ⊆ O) : ContDiff ℝ ∞ (fun x => c x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hc.contDiffAt.smul (hg.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport c := fun h => hx (hcO h)
    have hev : (fun x => c x • g x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq (f := c) (x := x)).mp hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **Joint smoothness of the shape family** on `{|s| ≤ 1} × B(ρa)` for `ρa < ρ`. -/
theorem contDiffOn_shape (hf : ContDiffOn ℝ ∞ f (ball 0 ρ)) {ρa : ℝ} (h0 : 0 ≤ ρa)
    (h1 : ρa < ρ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => shape f p.1 p.2) (Icc (-1) 1 ×ˢ ball (0 : E n) ρa) := by
  set ρb := (ρa + ρ) / 2
  set O : Set (ℝ × (ℝ × E n)) := {q | q.1 • (q.2.1 • q.2.2) ∈ ball (0 : E n) ρ}
  have hO : IsOpen O := isOpen_ball.preimage
    (continuous_fst.smul (continuous_snd.fst.smul continuous_snd.snd))
  have hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × E n) => q.1 • (q.2.1 • q.2.2)) :=
    contDiff_fst.smul (contDiff_snd.fst.smul contDiff_snd.snd)
  have hc : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × E n) => radialCutoff ρa ρb (q.1 • (q.2.1 • q.2.2))) :=
    radialCutoff_contDiff.comp hsm
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (ball 0 ρ) := hf.fderiv_of_isOpen isOpen_ball (by simp)
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × E n) => fderiv ℝ f (q.1 • (q.2.1 • q.2.2)) q.2.2) O :=
    (hDf.comp hsm.contDiffOn fun q hq => hq).clm_apply contDiff_snd.snd.contDiffOn
  have hI := OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral
    (contDiff_smul_of_tsupport hO hc hg (by
      intro q hq
      have hq' : q.1 • (q.2.1 • q.2.2) ∈ tsupport (radialCutoff ρa ρb) :=
        tsupport_comp_subset_preimage (radialCutoff ρa ρb) hsm.continuous hq
      have := tsupport_radialCutoff_subset (by simp only [ρb]; linarith) h0 hq'
      rw [mem_closedBall_zero_iff] at this
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt this (by simp only [ρb]; linarith))))
  apply hI.contDiffOn.congr
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  rw [mem_ball_zero_iff] at hu
  simp only [shape]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le zero_le_one] at hσ
  have hsu : ‖s • u‖ ≤ ‖u‖ := by
    rw [norm_smul]
    calc ‖s‖ * ‖u‖ ≤ 1 * ‖u‖ := by
          gcongr; rw [Real.norm_eq_abs, abs_le]; exact ⟨hs.1, hs.2⟩
      _ = ‖u‖ := one_mul _
  have : ‖σ • (s • u)‖ ≤ ρa := ((norm_smul_le_of_mem_Icc hσ _).trans hsu).trans hu.le
  rw [radialCutoff_eq_one (by simp only [ρb]; linarith) h0 this, one_smul]

end SymplecticPacking.General.Ham.Isotopy
