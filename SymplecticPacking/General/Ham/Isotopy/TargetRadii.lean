import SymplecticPacking.General.Ham.Isotopy.Radii
import SymplecticPacking.General.Ham.Isotopy.Bounds

/-!
# The target bound for the branch embeddings

The embedding data of a branch, with the radii `rad c s D j`, satisfy `TargetIsoInput` with
target radius `capRadius C` (`targetIsoInput`).
-/

noncomputable section
namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Problem

/-- The embedding data satisfy the full target-bounded isotopy input of the paper. -/
theorem targetIsoInput {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {D : General.EmbeddingData n k} (hn : 1 ≤ n) (hk : 1 ≤ k) (hC : 0 < C)
    (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s)
    (hD : General.EmbeddingSpec n k C c D) :
    TargetIsoInput D.f s (rad c s D 1) (rad c s D 2) (rad c s D 3)
      (rad c s D 4) (domRad D) (capRadius C) := by
  refine ⟨isoInput hn hc hs hD, hk, capRadius_pos hC, ?_⟩
  intro i u hu
  have he : 0 ≤ D.enlarged i := ((hc i).trans (hD.lt_enlarged i)).le
  have hu' : u ∈ capBall (0 : E n) (D.enlarged i) := by
    rw [capBall_zero_eq he]
    exact closedBall_subset_closedBall (rad_four_lt hc hs hD i).le hu
  have hb := hD.into i ⟨u, hu', rfl⟩
  rw [capBallOpen_zero_eq hC.le, mem_ball_zero_iff] at hb
  exact hb

end SymplecticPacking.General.Ham.Isotopy
