import SymplecticPacking.BranchSmall.VectorTransferSpecFlow

/-!
# Fixed sets of linear reflections along complete trajectories

A symmetric cutoff is formed as `χ(x)χ(Rx)`. It agrees with the original field on
the compact trajectory, so reflection invariance transfers to the curve.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Metric
open SymplecticPacking.Return (CSField flow)
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem trajectory_reflection_fixed_iff {V : ℝ → E → E}
    (hV : ContDiff ℝ ∞ (fun p : ℝ × E => V p.1 p.2))
    (R : E →L[ℝ] E) (hRR : ∀ x, R (R x) = x) (hRn : ∀ x, ‖R x‖ = ‖x‖)
    (hRV : ∀ t x, V t (R x) = R (V t x)) {γ : ℝ → E}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (V t (γ t)) (Icc 0 1) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    R (γ t) = γ t ↔ R (γ 0) = γ 0 := by
  have hγc : ContinuousOn γ (Icc (0 : ℝ) 1) := fun t ht => (hγ t ht).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγc
  let r : ℝ := max M 1 + 1
  have hr : 0 < r := by dsimp only [r]; linarith [le_max_right M 1]
  let χ : ContDiffBump (0 : E) := ⟨r, r + 1, hr, by linarith⟩
  let ρ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩
  let φ : ℝ × E → ℝ := fun p => ρ p.1 * χ p.2 * χ (R p.2)
  let W : ℝ → E → E := fun t x => φ (t, x) • V t x
  have hφ : ContDiff ℝ ∞ φ :=
    (((ρ.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd)).mul
      (χ.contDiff.comp (R.contDiff.comp contDiff_snd)))
  have hW : CSField W := by
    refine ⟨hφ.smul hV, ?_⟩
    apply HasCompactSupport.intro ((isCompact_closedBall (1 / 2 : ℝ) (3 / 2)).prod
      (isCompact_closedBall (0 : E) (r + 1)))
    intro p hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · change ¬ dist p.1 (1 / 2 : ℝ) ≤ 3 / 2 at hp
      have hz : ρ p.1 = 0 := ρ.zero_of_le_dist (not_le.mp hp).le
      simp only [W, φ, hz, zero_mul, zero_smul]
    · change ¬ dist p.2 (0 : E) ≤ r + 1 at hp
      have hz : χ p.2 = 0 := χ.zero_of_le_dist (not_le.mp hp).le
      simp only [W, φ, hz, mul_zero, zero_mul, zero_smul]
  have hWeq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : W s (γ s) = V s (γ s) := by
    have hρ : ρ s = 1 := ρ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2])
    have hχ : χ (γ s) = 1 := χ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hM s hs).trans (by change M ≤ max M 1 + 1; linarith [le_max_left M 1]))
    have hχR : χ (R (γ s)) = 1 := χ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right, hRn]
      exact (hM s hs).trans (by change M ≤ max M 1 + 1; linarith [le_max_left M 1]))
    simp only [W, φ, hρ, hχ, hχR, mul_one, one_smul]
  have hWcomm (s : ℝ) (x : E) : W s (R x) = R (W s x) := by
    simp only [W, φ, hRR, hRV, map_smul]
    congr 1
    ring
  have hsol : IsSolI W 0 (γ 0) (fun s => γ (clampI s)) := by
    refine ⟨?_, ?_, ?_⟩
    · change γ (clampI 0) = γ 0
      rw [clampI_of_mem ⟨le_rfl, zero_le_one⟩]
    · intro s
      change γ (clampI s) = γ (clampI (clampI s))
      rw [clampI_clampI]
    · intro s hs
      change HasDerivWithinAt (fun s => γ (clampI s)) (W s (γ (clampI s))) (Icc 0 1) s
      rw [clampI_of_mem hs, hWeq s hs]
      exact (hγ s hs).congr_of_mem (fun s hs => congrArg γ (clampI_of_mem hs)) hs
  have hflow (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : γ s = flow W s (γ 0) := by
    have hh := isSolI_unique hW isOpen_univ (fun _ _ _ _ => rfl)
      (fun _ _ => mem_univ _) hsol s
    simpa only [clampI_of_mem hs] using hh
  rw [hflow t ht]
  constructor
  · intro hfix
    apply hW.flow_injective t
    rw [hW.flow_map hWcomm, hfix]
  · intro hfix
    rw [← hW.flow_map hWcomm, hfix]

end SymplecticPacking.BranchSmall.VT
