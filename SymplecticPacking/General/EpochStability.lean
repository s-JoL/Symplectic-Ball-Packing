import SymplecticPacking.General.EpochQuarter
import SymplecticPacking.General.Compile
import SymplecticPacking.Effective.PackingCertificate

/-!
# Stability of the four-dimensional theorem under C¹ approximation

The Hamiltonian `H_{k,ε} = epochHamiltonianQ k ε` carries the closed unit balls into the closed
ball of radius `R_Q = (k / (1 - ε/4))^{1/4}`, while the Epoch problem only asks for the closed
ball of radius `R = (k / (1 - ε/2))^{1/4}`, which still has `k / R⁴ = 1 - ε/2 > 1 - ε`. The
explicit gap `R - R_Q` absorbs evaluation errors: every smooth compactly supported `Ĥ` whose
field is `L`-Lipschitz on `[0,1]` and `η`-close to `X_{H_{k,ε}}` with `η e^L ≤ R - R_Q` solves
the problem as well. The radial gap is a closed formula in `(k, ε)`; the field tolerance also uses `L`.
-/

noncomputable section

namespace SymplecticPacking.General

open Set Metric Problem
open scoped NNReal ContDiff

/-- The margin `R - R_Q` is positive. -/
theorem epochRadiusQ_lt_epochRadius {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    epochRadiusQ k ε < epochRadius k ε := by
  have hk' : (0 : ℝ) < k := by have : (9 : ℝ) ≤ k := by exact_mod_cast hk
                               linarith
  have hlt : epochR4 k (ε / 2) < epochR4 k ε := by
    unfold epochR4
    apply div_lt_div_of_pos_left hk' (by linarith) (by linarith)
  have hnn : 0 ≤ epochR4 k (ε / 2) := by
    unfold epochR4; exact div_nonneg hk'.le (by linarith)
  exact Real.rpow_lt_rpow hnn hlt (by norm_num)

/-- `gronwallBound 0 L η 1 ≤ η e^L` for `η ≥ 0`. -/
theorem gronwallBound_zero_one_le {L : ℝ≥0} {η : ℝ} (hη : 0 ≤ η) :
    gronwallBound 0 L η 1 ≤ η * Real.exp L := by
  by_cases hL : (L : ℝ) = 0
  · rw [hL, gronwallBound_K0]; simp
  · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.2 (Ne.symm hL)
    rw [gronwallBound_of_K_ne_0 hL]
    simp only [zero_mul, zero_add, mul_one]
    have he : Real.exp L - 1 ≤ L * Real.exp L := by
      have h := Real.add_one_le_exp (-(L : ℝ))
      have hmul : Real.exp (-(L : ℝ)) * Real.exp L = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (L : ℝ)]
    calc η / L * (Real.exp L - 1) ≤ η / L * (L * Real.exp L) :=
          mul_le_mul_of_nonneg_left he (div_nonneg hη hLpos.le)
      _ = η * Real.exp L := by field_simp

/-- **Stability.** Let `k ≥ 10`, `ε ∈ (0,1)`. Every smooth compactly supported `Ĥ` whose
Hamiltonian field is `L`-Lipschitz for `t ∈ [0,1]` and within `η` of the field of
`H_{k,ε} = epochHamiltonianQ k ε` there, with `η e^L ≤ R - R_Q`, satisfies the Epoch
specification with radius `R = (k / (1 - ε/2))^{1/4}`. -/
theorem epoch_stability {k : ℕ} (hk : 10 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (Hh : ℝ → E 2 → ℝ) (hsm : ContDiff ℝ ∞ (fun p : ℝ × E 2 => Hh p.1 p.2))
    (hsupp : ∃ K : Set (E 2), IsCompact K ∧ ∀ t, ∀ y ∉ K, Hh t y = 0)
    (L : ℝ≥0) (hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith L (Problem.hamVF Hh t))
    (η : ℝ) (hη : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      ‖Problem.hamVF Hh t y - Problem.hamVF (epochHamiltonianQ k ε) t y‖ ≤ η)
    (hsmall : η * Real.exp L ≤ epochRadius k ε - epochRadiusQ k ε) :
    Problem.EpochSpecR k ε (epochRadius k ε) Hh := by
  have hk9 : 9 ≤ k := by omega
  have hE := epoch_general k hk9 ε h0 h1
  have hQ := epochQ_spec hk9 h0 h1
  obtain ⟨K, hK, hzero⟩ := hsupp
  obtain ⟨R0, hKR⟩ := hK.isBounded.subset_closedBall (0 : E 2)
  have hR0 : ∀ t (y : E 2), R0 < ‖y‖ → Hh t y = 0 := by
    intro t y hy
    apply hzero t y
    intro hyK
    have hh := hKR hyK
    rw [mem_closedBall, dist_zero_right] at hh
    linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 ⟨le_rfl, zero_le_one⟩ 0)
  refine ⟨hsm, ⟨K, hK, hzero⟩, hE.radius_pos, hE.density,
    fun i _ x _ => Compile.exists_integralCurve_global hsm hR0 x, ?_⟩
  intro i hi x hx γ hγ0 hγ
  obtain ⟨y, hy0, hy⟩ := hQ.exists_curve i hi x hx
  have hy1 := hQ.maps_into i hi x hx y hy0 (hy.isIntegralCurveOn _)
  let F : ℝ → E 2 → E 2 := fun t => Problem.hamVF Hh (Compile.clamp01 t)
  let G : ℝ → E 2 → E 2 := fun t => Problem.hamVF (epochHamiltonianQ k ε) (Compile.clamp01 t)
  have hF : ∀ t, LipschitzWith L (F t) := fun t => hL _ (Compile.clamp01_mem t)
  have hFG : ∀ t z, dist (G t z) (F t z) ≤ η := by
    intro t z
    rw [dist_eq_norm, norm_sub_rev]
    exact hη _ (Compile.clamp01_mem t) z
  have hγF : IsIntegralCurveOn γ F (Icc 0 1) := by
    intro t ht
    simpa only [F, Compile.clamp01_of_mem ht] using hγ t ht
  have hyG : IsIntegralCurveOn y G (Icc 0 1) := by
    intro t ht
    simpa only [G, Compile.clamp01_of_mem ht] using
      (hy.isIntegralCurveOn (Icc 0 1)) t ht
  have hd := Effective.PackingCertificate.flow_error_with_initial hF hFG hγF hyG
    (ρ := 0) (by rw [hy0, hγ0, dist_self]) 1 ⟨zero_le_one, le_rfl⟩
  have hd' : dist (y 1) (γ 1) ≤ η * Real.exp L := hd.trans (gronwallBound_zero_one_le hη0)
  rw [mem_closedBall, dist_zero_right] at hy1 ⊢
  calc ‖γ 1‖ ≤ ‖y 1‖ + dist (y 1) (γ 1) := by
        rw [dist_comm, dist_eq_norm]
        simpa using norm_le_insert' (γ 1) (y 1)
    _ ≤ epochRadiusQ k ε + η * Real.exp L := add_le_add hy1 hd'
    _ ≤ epochRadius k ε := by linarith

end SymplecticPacking.General
