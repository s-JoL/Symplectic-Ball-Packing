import SymplecticPacking.General.Ham.Isotopy.Geometry

/-!
# Radii of the Hamiltonian end, chosen from the input

From capacities `cᵢ`, pairwise disjoint closed source balls `sᵢ + B(cᵢ)` and the data
`(fᵢ, c'ᵢ, aᵢ)` of the geometric stage, the Euclidean radii

  `aᵢ = √(cᵢ/π) < r₁ᵢ < r₂ᵢ < r₃ᵢ < r₄ᵢ < √(c'ᵢ/π) < ρᵢ = √(aᵢ/π)`,   `r_mᵢ = aᵢ + m δᵢ / 5`,

with `δᵢ = min(g/4, √(c'ᵢ/π) - aᵢ)` and `g = min_{i≠j} (|sᵢ - sⱼ| - aᵢ - aⱼ) > 0` the smallest gap
between the source balls. Then `r₃ᵢ + r₃ⱼ < |sᵢ - sⱼ|`, and the input satisfies `IsoInput`.
(This shrinks the enlargement `c'ᵢ` of the geometric stage as far as the centre gaps require.)
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Finset Problem
open scoped ContDiff

variable {n k : ℕ}

/-- Euclidean radius `√(c/π)` of the ball of capacity `c`. -/
def capRadius (c : ℝ) : ℝ := Real.sqrt (c / Real.pi)

lemma capRadius_nonneg (c : ℝ) : 0 ≤ capRadius c := Real.sqrt_nonneg _

lemma capRadius_lt {c c' : ℝ} (hc : 0 ≤ c) (h : c < c') : capRadius c < capRadius c' :=
  Real.sqrt_lt_sqrt (div_nonneg hc Real.pi_pos.le) (div_lt_div_of_pos_right h Real.pi_pos)

lemma capRadius_pos {c : ℝ} (hc : 0 < c) : 0 < capRadius c :=
  Real.sqrt_pos.mpr (div_pos hc Real.pi_pos)

lemma mem_capBall_iff {s y : E n} {c : ℝ} (hc : 0 ≤ c) :
    y ∈ capBall s c ↔ ‖y - s‖ ≤ capRadius c := by
  rw [capBall, Set.mem_setOf_eq, capRadius,
    Real.le_sqrt (norm_nonneg _) (div_nonneg hc Real.pi_pos.le), le_div_iff₀ Real.pi_pos, mul_comm]

lemma capBall_zero_eq {c : ℝ} (hc : 0 ≤ c) : capBall (0 : E n) c = closedBall 0 (capRadius c) := by
  ext y; rw [mem_capBall_iff hc, mem_closedBall_zero_iff, sub_zero]

lemma capBallOpen_zero_eq {c : ℝ} (hc : 0 ≤ c) :
    capBallOpen (0 : E n) c = ball 0 (capRadius c) := by
  ext y
  rw [capBallOpen, Set.mem_setOf_eq, mem_ball_zero_iff, capRadius, Real.lt_sqrt (norm_nonneg _),
    lt_div_iff₀ Real.pi_pos, mul_comm, sub_zero]

/-- Pairwise disjoint closed balls of positive capacity have `|sᵢ - sⱼ| > aᵢ + aⱼ`. -/
lemma dist_gt_of_ballsDisjoint {c : Fin k → ℝ} {s : Fin k → E n} (hc : ∀ i, 0 < c i)
    (hs : BallsDisjoint n k c s) {i j : Fin k} (hij : i ≠ j) :
    capRadius (c i) + capRadius (c j) < dist (s i) (s j) := by
  by_contra hle
  push Not at hle
  set a := capRadius (c i)
  set b := capRadius (c j)
  have ha : 0 < a := capRadius_pos (hc i)
  have hb : 0 < b := capRadius_pos (hc j)
  have hab : a + b ≠ 0 := by positivity
  set τ := a / (a + b)
  set p : E n := s i + τ • (s j - s i)
  have hτ0 : 0 ≤ τ := div_nonneg ha.le (by linarith)
  have hτ1 : 1 - τ = b / (a + b) := by
    simp only [τ]; field_simp; ring
  have hd : ‖s j - s i‖ = dist (s i) (s j) := by rw [dist_comm, dist_eq_norm]
  have h1 : p ∈ capBall (s i) (c i) := by
    rw [mem_capBall_iff (hc i).le]
    simp only [p, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0, hd]
    calc τ * dist (s i) (s j) ≤ τ * (a + b) := mul_le_mul_of_nonneg_left hle hτ0
      _ = a := by simp only [τ]; field_simp
  have h2 : p ∈ capBall (s j) (c j) := by
    rw [mem_capBall_iff (hc j).le]
    have : p - s j = (1 - τ) • (s i - s j) := by
      simp only [p]; rw [sub_smul, one_smul, smul_sub, smul_sub]; abel
    rw [this, norm_smul, Real.norm_of_nonneg (by rw [hτ1]; positivity), ← dist_eq_norm, hτ1]
    calc b / (a + b) * dist (s i) (s j) ≤ b / (a + b) * (a + b) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = b := by field_simp
  exact Set.disjoint_left.mp (hs i j hij) h1 h2

open scoped Classical in
/-- The smallest gap `min_{i ≠ j} (|sᵢ - sⱼ| - aᵢ - aⱼ)` (`1` if `k ≤ 1`). -/
def centreGap (c : Fin k → ℝ) (s : Fin k → E n) : ℝ :=
  if h : (univ : Finset (Fin k)).offDiag.Nonempty then
    univ.offDiag.inf' h fun p => dist (s p.1) (s p.2) - capRadius (c p.1) - capRadius (c p.2)
  else 1

/-- The step `δᵢ = min(g/4, √(c'ᵢ/π) - aᵢ)`. -/
def radStep (c : Fin k → ℝ) (s : Fin k → E n) (D : General.EmbeddingData n k) (i : Fin k) : ℝ :=
  min (centreGap c s / 4) (capRadius (D.enlarged i) - capRadius (c i))

/-- The radii `r_mᵢ = aᵢ + m δᵢ / 5` (`m = 1, …, 4`). -/
def rad (c : Fin k → ℝ) (s : Fin k → E n) (D : General.EmbeddingData n k) (m : ℕ)
    (i : Fin k) : ℝ :=
  capRadius (c i) + m * radStep c s D i / 5

/-- The domain radius `ρᵢ = √(aᵢ/π)`. -/
def domRad (D : General.EmbeddingData n k) (i : Fin k) : ℝ := capRadius (D.domain i)

variable {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} {D : General.EmbeddingData n k}

lemma centreGap_pos (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s) : 0 < centreGap c s := by
  unfold centreGap
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    rintro ⟨i, j⟩ hp
    rw [Finset.mem_offDiag] at hp
    have := dist_gt_of_ballsDisjoint hc hs hp.2.2
    simp only; linarith
  · exact one_pos

lemma centreGap_le {i j : Fin k} (hij : i ≠ j) :
    centreGap c s ≤ dist (s i) (s j) - capRadius (c i) - capRadius (c j) := by
  have hmem : (i, j) ∈ (univ : Finset (Fin k)).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩
  unfold centreGap
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.inf'_le (fun p : Fin k × Fin k =>
    dist (s p.1) (s p.2) - capRadius (c p.1) - capRadius (c p.2)) hmem

lemma radStep_pos (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s)
    (hD : General.EmbeddingSpec n k C c D) (i : Fin k) : 0 < radStep c s D i :=
  lt_min (by linarith [centreGap_pos hc hs])
    (by linarith [capRadius_lt (hc i).le (hD.lt_enlarged i)])

lemma source_lt_rad_one (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s)
    (hD : General.EmbeddingSpec n k C c D) (i : Fin k) : capRadius (c i) < rad c s D 1 i := by
  have := radStep_pos hc hs hD i
  unfold rad; push_cast; linarith

lemma rad_four_lt (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s)
    (hD : General.EmbeddingSpec n k C c D) (i : Fin k) :
    rad c s D 4 i < capRadius (D.enlarged i) := by
  have h1 := radStep_pos hc hs hD i
  have h2 : radStep c s D i ≤ capRadius (D.enlarged i) - capRadius (c i) := min_le_right _ _
  unfold rad; push_cast; linarith

/-- **The input of the isotopy construction.** -/
theorem isoInput (hn : 1 ≤ n) (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s)
    (hD : General.EmbeddingSpec n k C c D) :
    IsoInput D.f s (rad c s D 1) (rad c s D 2) (rad c s D 3) (rad c s D 4) (domRad D) := by
  have hδ := radStep_pos hc hs hD
  have he : ∀ i, 0 ≤ D.enlarged i := fun i => ((hc i).trans (hD.lt_enlarged i)).le
  have hd : ∀ i, 0 ≤ D.domain i := fun i => (he i).trans (hD.enlarged_lt_domain i).le
  have h4 := rad_four_lt hc hs hD
  have hed : ∀ i, capRadius (D.enlarged i) < domRad D i := fun i =>
    capRadius_lt (he i) (hD.enlarged_lt_domain i)
  have hsub4 : ∀ i, closedBall (0 : E n) (rad c s D 4 i) ⊆ capBall 0 (D.enlarged i) := fun i => by
    rw [capBall_zero_eq (he i)]; exact closedBall_subset_closedBall (h4 i).le
  refine ⟨hn, fun i => ?_, fun i => ?_, fun i u hu => ?_, fun i => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩
  · have := hδ i
    have := capRadius_nonneg (c i)
    refine ⟨?_, ?_, ?_, ?_, (h4 i).trans (hed i)⟩ <;> unfold rad <;> push_cast <;> nlinarith
  · have := hD.smooth i
    rwa [capBallOpen_zero_eq (hd i)] at this
  · exact hD.sympl i u (by rw [capBallOpen_zero_eq (hd i)]; exact hu)
  · exact (hD.inj i).mono (hsub4 i)
  · exact (hD.disj i j hij).mono (image_mono (hsub4 i)) (image_mono (hsub4 j))
  · have hg := centreGap_le (c := c) (s := s) hij
    have hgi : radStep c s D i ≤ centreGap c s / 4 := min_le_left _ _
    have hgj : radStep c s D j ≤ centreGap c s / 4 := min_le_left _ _
    have hg0 := centreGap_pos hc hs
    unfold rad; push_cast; linarith

end SymplecticPacking.General.Ham.Isotopy
