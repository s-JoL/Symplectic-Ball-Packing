import SymplecticPacking.General.Ham.TimeSupport
import SymplecticPacking.General.Ham.Smooth

/-!
# Global integral curves

Global integral curves of the Hamiltonian vector field of a smooth Hamiltonian that is
compactly supported in space and whose field vanishes for `t ∉ (0,1)`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter Problem
open scoped ContDiff Topology NNReal

variable {n : ℕ}

/-- The Hamiltonian vector field as a function of `(t, y)`. -/
def hamField (H : ℝ → E n → ℝ) (p : ℝ × E n) : E n := Problem.hamVF H p.1 p.2

lemma contDiff_partial {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (j : Fin (2 * n)) : ContDiff ℝ ∞ (fun p : ℝ × E n => Problem.partialDeriv (H p.1) j p.2) := by
  unfold Problem.partialDeriv
  have h1 : ContDiff ℝ ∞ (fun q : (ℝ × E n) × E n => H q.1.1 q.2) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have h2 := ContDiff.fderiv (f := fun (q : ℝ × E n) (y : E n) => H q.1 y) (g := fun q => q.2)
    h1 contDiff_snd (m := ∞) (n := ∞) (by simp)
  exact h2.clm_apply contDiff_const

lemma hamField_contDiff {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)) :
    ContDiff ℝ ∞ (hamField H) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × E n => (fun i : Fin (2 * n) =>
      if h : (i : ℕ) < n then Problem.partialDeriv (H p.1) ⟨i + n, by omega⟩ p.2
      else -Problem.partialDeriv (H p.1) ⟨i - n, by have := i.isLt; omega⟩ p.2)) := by
    rw [contDiff_pi]
    intro i
    by_cases h : (i : ℕ) < n
    · simp only [h, dite_true]; exact contDiff_partial hH _
    · simp only [h, dite_false]; exact (contDiff_partial hH _).neg
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2 * n) => ℝ)).symm.contDiff.comp hc

/-- A smooth Hamiltonian, supported in `B̄(S)` in space and with field zero outside `(0,1)`,
has a globally Lipschitz and bounded Hamiltonian vector field. -/
theorem hamVF_lipschitz_bound {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {S : ℝ} (hS : ∀ t, ∀ y ∉ closedBall (0 : E n) S, H t y = 0)
    (hT : ∀ t y, (t ≤ 0 ∨ 1 ≤ t) → Problem.hamVF H t y = 0) :
    ∃ K : ℝ≥0, ∃ C : ℝ, (∀ t, LipschitzWith K (Problem.hamVF H t)) ∧ ∀ t y, ‖Problem.hamVF H t y‖ ≤ C := by
  set V := hamField H
  have hV : ContDiff ℝ ∞ V := hamField_contDiff hH
  -- the field vanishes outside `[0,1] × B̄(S)`
  have hVzero : ∀ p : ℝ × E n, p ∉ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E n) S → V p = 0 := by
    rintro ⟨t, y⟩ hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with ht | hy
    · apply hT
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl ht.le
      · exact Or.inr ht.le
    · have hev : H t =ᶠ[𝓝 y] fun _ => 0 := by
        have : (closedBall (0 : E n) S)ᶜ ∈ 𝓝 y := isClosed_closedBall.isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz using hS t z hz
      have hd : fderiv ℝ (H t) y = 0 := by
        rw [hev.fderiv_eq]; simp
      exact hamVF_eq_zero_of_fderiv hd
  have hcs : HasCompactSupport V := by
    apply HasCompactSupport.intro ((isCompact_Icc).prod (isCompact_closedBall 0 S))
    intro p hp; exact hVzero p hp
  obtain ⟨K, hK⟩ := hV.lipschitzWith_of_hasCompactSupport hcs (by simp)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hV.continuous
  refine ⟨K, C, fun t => ?_, fun t y => hC (t, y)⟩
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have := hK.dist_le_mul (t, y) (t, z)
  simpa [Prod.dist_eq, V, hamField] using this

/-- Hypotheses: smooth, compactly supported in space (inside `B̄(S)`), field zero outside `(0,1)`. -/
theorem exists_integralCurve {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {S : ℝ} (hS : ∀ t, ∀ y ∉ closedBall (0 : E n) S, H t y = 0)
    (hT : ∀ t y, (t ≤ 0 ∨ 1 ≤ t) → Problem.hamVF H t y = 0) (x : E n) :
    ∃ γ : ℝ → E n, γ 0 = x ∧ IsIntegralCurve γ (Problem.hamVF H) := by
  set V := hamField H
  have hV : ContDiff ℝ ∞ V := hamField_contDiff hH
  -- the field vanishes outside `[0,1] × B̄(S)`
  have hVzero : ∀ p : ℝ × E n, p ∉ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E n) S → V p = 0 := by
    rintro ⟨t, y⟩ hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with ht | hy
    · apply hT
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl ht.le
      · exact Or.inr ht.le
    · have hev : H t =ᶠ[𝓝 y] fun _ => 0 := by
        have : (closedBall (0 : E n) S)ᶜ ∈ 𝓝 y := isClosed_closedBall.isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz using hS t z hz
      have hd : fderiv ℝ (H t) y = 0 := by
        rw [hev.fderiv_eq]; simp
      exact hamVF_eq_zero_of_fderiv hd
  have hcs : HasCompactSupport V := by
    apply HasCompactSupport.intro ((isCompact_Icc).prod (isCompact_closedBall 0 S))
    intro p hp; exact hVzero p hp
  obtain ⟨K, hK⟩ := hV.lipschitzWith_of_hasCompactSupport hcs (by simp)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hV.continuous
  set C' : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hC' : ∀ p, ‖V p‖ ≤ C' := fun p => (hC p).trans (le_max_left _ _)
  have hlip : ∀ t, LipschitzWith K (fun y => V (t, y)) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    have := hK.dist_le_mul (t, y) (t, z)
    simpa [Prod.dist_eq] using this
  -- Picard–Lindelöf on `[0,1]`
  have hPL : IsPicardLindelof (fun t y => V (t, y)) (tmin := 0) (tmax := 1)
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ x C' 0 C' K := by
    refine ⟨fun t _ => (hlip t).lipschitzOnWith, fun y _ => ?_, fun t _ y _ => hC' _, ?_⟩
    · exact (hV.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · simp
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- extend by constants
  set γ : ℝ → E n := fun t => α (max 0 (min t 1)) with hγdef
  have hγα : ∀ t ∈ Icc (0 : ℝ) 1, γ t = α t := by
    intro t ht; simp [hγdef, min_eq_left ht.2, max_eq_right ht.1]
  have hγ0 : γ 0 = x := by rw [hγα 0 (left_mem_Icc.mpr zero_le_one)]; exact hα0
  refine ⟨γ, hγ0, fun t => ?_⟩
  change HasDerivAt γ (V (t, γ t)) t
  have hlo : ∀ s ≤ 0, γ s = x := by
    intro s hs; simp only [hγdef]; rw [max_eq_left (by simp [hs.trans zero_le_one, hs])]
    exact hα0
  have hhi : ∀ s ≥ 1, γ s = α 1 := by
    intro s hs; simp [hγdef, min_eq_right hs]
  have hVlo : ∀ s ≤ 0, ∀ y, V (s, y) = 0 := fun s hs y => hT s y (Or.inl hs)
  have hVhi : ∀ s ≥ 1, ∀ y, V (s, y) = 0 := fun s hs y => hT s y (Or.inr hs)
  have hIcc : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (V (s, γ s)) (Icc 0 1) s := by
    intro s hs
    rw [hγα s hs]
    exact (hα s hs).congr (fun r hr => hγα r hr) (hγα s hs)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · -- left of 0: locally constant
    rw [hVlo t ht.le]
    apply (hasDerivAt_const t x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs using hlo s hs.le
  · -- at 0: glue left-constant and the solution on `[0,1]`
    rw [hγ0, hVlo 0 le_rfl x]
    have hleft : HasDerivWithinAt γ 0 (Iic 0) 0 :=
      (hasDerivWithinAt_const 0 (Iic 0) x).congr (fun s hs => hlo s hs) hγ0
    have hright : HasDerivWithinAt γ 0 (Ici 0) 0 := by
      have h := hIcc 0 (left_mem_Icc.mpr zero_le_one)
      rw [hγ0, hVlo 0 le_rfl x] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one)
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · -- interior
      have h := hIcc t ⟨ht.le, ht1.le⟩
      exact h.hasDerivAt (Icc_mem_nhds ht ht1)
    · rw [hhi 1 le_rfl, hVhi 1 le_rfl]
      have hright : HasDerivWithinAt γ 0 (Ici 1) 1 :=
        (hasDerivWithinAt_const 1 (Ici 1) (α 1)).congr (fun s hs => hhi s hs) (hhi 1 le_rfl)
      have hleft : HasDerivWithinAt γ 0 (Iic 1) 1 := by
        have h := hIcc 1 (right_mem_Icc.mpr zero_le_one)
        rw [hVhi 1 le_rfl] at h
        exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE zero_lt_one)
      have := hleft.union hright
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [hVhi t ht1.le]
      apply (hasDerivAt_const t (α 1)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht1] with s hs using hhi s hs.le

/-- **`sec:ham-hamiltonian`, global integral curves**, from smoothness (`ofIsotopy_smooth`). -/
theorem ofIsotopy_exists_curve' {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n}
    {r1 r2 r3 ρ : Fin k → ℝ}
    (hF : CommonIsotopy F s r1 r2 r3 ρ) (x : E n) :
    ∃ γ : ℝ → E n, γ 0 = x ∧ IsIntegralCurve γ (Problem.hamVF (ofIsotopy F r1 r2 r3)) := by
  obtain ⟨S, hS⟩ := hF.bounded
  exact exists_integralCurve (ofIsotopy_smooth hF) (ofIsotopy_support hS)
    (fun t y ht => hamVF_ofIsotopy_eq_zero_of_time hF ht y) x

end SymplecticPacking.General.Ham
