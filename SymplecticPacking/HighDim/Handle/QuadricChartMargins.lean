import SymplecticPacking.HighDim.Handle.QuadricExplicitCharts

/-!
# Margins of the explicit quadric charts

Quantitative open certificates for the explicit quadric coordinates.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

theorem rootArgument_re_pos {c d : ℂ} (hc : c ≠ 0) (hd : ‖d‖ < ‖c‖^2) :
    0 < (1+d/c^2 : ℂ).re := by
  have hdiv : ‖d/c^2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (pow_pos (norm_pos_iff.mpr hc) 2)]
    exact hd
  have hr := (abs_le.mp (Complex.abs_re_le_norm (d/c^2))).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem norm_square_difference_le {u v : ℂ} {r : ℝ} (hu : u ∈ Metric.closedBall v r) :
    ‖u^2-v^2‖ ≤ r*(2*‖v‖+r) := by
  have hdiff : ‖u-v‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
  have hr : 0 ≤ r := (norm_nonneg _).trans hdiff
  have hsum : ‖u+v‖ ≤ 2*‖v‖+r := by
    calc
      ‖u+v‖ = ‖(u-v)+(v+v)‖ := by congr 1; ring
      _ ≤ ‖u-v‖+‖v+v‖ := norm_add_le _ _
      _ ≤ r+(‖v‖+‖v‖) := add_le_add hdiff (norm_add_le _ _)
      _ = 2*‖v‖+r := by ring
  calc
    ‖u^2-v^2‖ = ‖u-v‖*‖u+v‖ := by rw [← norm_mul]; congr 1; ring
    _ ≤ r*(2*‖v‖+r) := mul_le_mul hdiff hsum (norm_nonneg _) hr

/-- Each closed coordinate disc can be certified by finitely many strict scalar inequalities. -/
theorem ordinaryLocalTarget_closedBall {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) {r : ℝ}
    (hr : ∀ j, r*(2*‖c.val.1‖+r) < ‖c.val.2 j‖^2) :
    Metric.closedBall c.val.1 r ⊆ ordinaryLocalTarget c := by
  intro u hu j
  exact rootArgument_re_pos (hc j) ((norm_square_difference_le hu).trans_lt (hr j))

theorem branchLocalTarget_closedBall {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) {r : ℝ}
    (hr₀ : r*(2*‖c.val.2 i‖+r) < ‖c.val.1‖^2)
    (hr : ∀ j, j≠i → r*(2*‖c.val.2 i‖+r) < ‖c.val.2 j‖^2) :
    Metric.closedBall (c.val.2 i) r ⊆ branchLocalTarget c i := by
  intro v hv
  refine ⟨rootArgument_re_pos hc.1 ((norm_square_difference_le hv).trans_lt hr₀), ?_⟩
  intro j hji
  exact rootArgument_re_pos (hc.2 j hji) ((norm_square_difference_le hv).trans_lt (hr j hji))

end SymplecticPacking.HighDim.ToricPackingStages
