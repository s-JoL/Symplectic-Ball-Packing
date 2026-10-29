import SymplecticPacking.HighDim.Handle.QuadricBoxInside

/-!
# Ordinary grid boxes covering the quadric

Quantitative sheet control for a predetermined rational coordinate grid.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

theorem div_rootNear_re_pos {c d : ℂ} (hc : c ≠ 0)
    (hd : 0 < (1+d/c^2 : ℂ).re) : 0 < (c/rootNear c d).re := by
  have hs := sqrt_re_pos hd
  have hs₀ : Complex.sqrt (1+d/c^2) ≠ 0 := by
    intro hh
    rw [hh] at hs
    exact (lt_irrefl 0) hs
  have he : c/rootNear c d = (Complex.sqrt (1+d/c^2))⁻¹ := by
    unfold rootNear
    field_simp
  rw [he, Complex.inv_re]
  exact div_pos hs (Complex.normSq_pos.mpr hs₀)

/-- Away from the branch loci, a fixed mesh bound suffices: a scalar inequality usable by a
predetermined finite grid, in place of an unspecified Lebesgue number. -/
theorem ordinary_grid_box_cover {m : ℕ} {a : Fin m → ℂ} (x : locus a)
    {R η r : ℝ} (hR : ‖x.val.1‖ ≤ R) (hη : 0 < η) (hr : 0 < r)
    (hxη : ∀ j, η ≤ ‖x.val.2 j‖) (q : ℂ)
    (hq : q ∈ Metric.closedBall x.val.1 (r/8))
    (hsmall : 4*r*(2*R+4*r) < η^2) :
    ∃ ε : Fin m → Bool,
      let c := ordinaryPresentationCenter a ε q
      ∃ hc : ∀ j, c.val.2 j ≠ 0,
      ∃ hm : ordinaryBoxMargin r c, x ∈ (ordinaryRawBox c hc r hr hm).innerOpen := by
  have hx (j : Fin m) : x.val.2 j ≠ 0 :=
    norm_pos_iff.mp (hη.trans_le (hxη j))
  let c := ordinaryLocalLift x hx q
  let e := r*(2*R+4*r)
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans hR
  have he : 0 < e := mul_pos hr (by positivity)
  have hs : 4*e < η^2 := by dsimp [e]; nlinarith [hsmall]
  have hd : ‖q^2-x.val.1^2‖ ≤ e := by
    apply (norm_square_difference_le hq).trans
    exact mul_le_mul (by linarith) (by linarith) (by positivity) hr.le
  have hqdist : ‖q-x.val.1‖ ≤ r/8 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq
  have hqn : ‖q‖ ≤ R+r := by
    have hn : ‖q‖ ≤ ‖q-x.val.1‖+‖x.val.1‖ := by
      simpa only [sub_add_cancel] using norm_add_le (q-x.val.1) x.val.1
    linarith
  have hηsq (j : Fin m) : η^2 ≤ ‖x.val.2 j‖^2 :=
    pow_le_pow_left₀ hη.le (hxη j) 2
  have hforward (j : Fin m) : 0 < (1+(q^2-x.val.1^2)/(x.val.2 j)^2 : ℂ).re := by
    apply rootArgument_re_pos (hx j)
    nlinarith [hd, hηsq j]
  have hc (j : Fin m) : c.val.2 j ≠ 0 := by
    change rootNear (x.val.2 j) (q^2-x.val.1^2) ≠ 0
    apply mul_ne_zero (hx j)
    intro hh
    have hp := sqrt_re_pos (hforward j)
    rw [hh] at hp
    exact (lt_irrefl 0) hp
  have hlower (j : Fin m) : η^2-e ≤ ‖c.val.2 j‖^2 := by
    have heq : (x.val.2 j)^2 = (c.val.2 j)^2-(q^2-x.val.1^2) := by
      change (x.val.2 j)^2 = rootNear (x.val.2 j) (q^2-x.val.1^2)^2-(q^2-x.val.1^2)
      rw [rootNear_sq (hx j)]
      ring
    have hn : ‖x.val.2 j‖^2 ≤ ‖c.val.2 j‖^2+‖q^2-x.val.1^2‖ := by
      rw [← norm_pow, heq]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_pow])
    linarith [hηsq j]
  have hm : ordinaryBoxMargin r c := by
    intro j
    have hb : (2*r)*(2*‖c.val.1‖+2*r) ≤ 2*e := by
      change (2*r)*(2*‖q‖+2*r) ≤ 2*e
      dsimp only [e]
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hqn)]
    linarith [hlower j]
  have hsource : x ∈ ordinaryLocalSource c := by
    refine ⟨?_, ?_⟩
    · intro j
      change 0 < (1+(x.val.1^2-q^2)/(c.val.2 j)^2 : ℂ).re
      apply rootArgument_re_pos (hc j)
      rw [norm_sub_rev]
      linarith [hlower j]
    · intro j
      exact div_rootNear_re_pos (hx j) (hforward j)
  have hin : x ∈ (ordinaryRawBox c hc r hr hm).innerOpen := by
    refine ⟨⟨hsource, Set.mem_univ _⟩, ?_⟩
    change Complex.equivRealProdCLM x.val.1 ∈ Metric.ball (Complex.equivRealProdCLM q) (r/4)
    rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
    have hh : ‖x.val.1-q‖ ≤ r/8 := by simpa only [norm_sub_rev] using hqdist
    exact (Complex.equivRealProd_apply_le _).trans_lt (by linarith)
  obtain ⟨ε, hε⟩ := ordinaryPresentationCenter_complete a c
  have hc0 : c.val.1 = q := rfl
  rw [hc0] at hε
  refine ⟨ε, ?_⟩
  change ∃ hc' hm', x ∈ (ordinaryRawBox _ hc' r hr hm').innerOpen
  rw [hε]
  exact ⟨hc, hm, hin⟩

end SymplecticPacking.HighDim.ToricPackingStages
