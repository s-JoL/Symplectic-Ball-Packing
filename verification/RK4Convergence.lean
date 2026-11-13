import verification.Statement
import SymplecticPacking.General.CompileSupport
import SymplecticPacking.Effective.PackingCertificate

/-!
# Picard–Lindelöf certificates and fixed-step RK4 convergence

Two consequences of the ODE estimates underlying `Statement.lean`, addressing numerical
verification and the non-mathematical constraints of fixed-step floating-point integration:

1. **Picard–Lindelöf certificate (`picard_lindelof_curve_unique`, `picard_lindelof_epoch_certificate`).**
   If `H` is smooth and compactly supported and candidate trajectories `t ↦ Γ i x t` satisfy
   `Γ i x 0 = x`, `Γ i x 1 = F i x ∈ B(0, R₀)`, and `‖d/dt (Γ i x t) - X_H(t, Γ i x t)‖ ≤ δ`
   on `[0, 1]` with `δ e^L ≤ R - R₀`, then every integral curve of `X_H` from `x` stays within
   `δ e^L` of `F i x` at `t = 1` (`= F i x` when `δ = 0`), certifying `EpochSpecR k ε R H`.
   This formalises the ODE-uniqueness step of Paper IV, Proposition 8.1(ii).

2. **Perturbed fixed-step RK4 convergence (`epoch_rk4_convergence`, `epoch_exact_rk4_convergence`).**
   Defines the classical 4-stage Runge–Kutta step `rk4Step` and iteration `rk4Iter` from
   `Problem.hamVF` alone, and proves that for every `k ≥ 10` and `ε ∈ (0, 1)`, the explicit
   Hamiltonian `H = epochHamiltonianQ k ε` of Theorem A admits `N₀ ≥ 1` and `δ₀ > 0` such that
   for all step counts `N ≥ N₀`, every perturbed `N`-step RK4 trajectory starting within `δ₀` of
   a source ball `B_i` with per-step rounding error `≤ δ₀ / N` lands at `t = 1` inside the closed
   origin ball `B(0, R)` with `R = epochRadius k ε` (`k / R⁴ = 1 - ε/2 > 1 - ε`). Thus fixed-step
   RK4 succeeds mathematically on `epochHamiltonianQ k ε` once fixed step-count/time and fixed
   53-bit precision caps are lifted.
-/

noncomputable section

open Set Metric SymplecticPacking SymplecticPacking.Problem
open scoped ContDiff NNReal

/-! ## 1. Picard–Lindelöf uniqueness and quantitative trajectory certificates -/

/-- Uniqueness on `[0, 1]` for any Hamiltonian vector field that is `L`-Lipschitz in space:
if a closed-form curve `Γ` satisfies `Γ 0 = x` and `dΓ/dt = X_H(t, Γ t)` on `[0, 1]`, then every
integral curve `γ` of `X_H` on `[0, 1]` with `γ 0 = x` agrees with `Γ` throughout `[0, 1]`. -/
theorem picard_lindelof_curve_unique {n : ℕ} (H : ℝ → E n → ℝ) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith L (hamVF H t))
    (γ Γ : ℝ → E n) (h0 : γ 0 = Γ 0)
    (hγ : IsIntegralCurveOn γ (hamVF H) (Icc 0 1))
    (hΓ : IsIntegralCurveOn Γ (hamVF H) (Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t = Γ t := by
  let F : ℝ → E n → E n := fun t => hamVF H (General.Compile.clamp01 t)
  have hF : ∀ t, LipschitzWith L (F t) := fun t => hL _ (General.Compile.clamp01_mem t)
  have hγF : IsIntegralCurveOn γ F (Icc 0 1) := fun t ht => by
    simpa only [F, General.Compile.clamp01_of_mem ht] using hγ t ht
  have hΓF : IsIntegralCurveOn Γ F (Icc 0 1) := fun t ht => by
    simpa only [F, General.Compile.clamp01_of_mem ht] using hΓ t ht
  intro t ht
  have hd := Effective.PackingCertificate.flow_error_with_initial hF
    (G := F) (η := 0) (fun _ _ => by simp) hΓF hγF (ρ := 0) (by simp [h0]) t ht
  rw [gronwallBound_ε0, zero_mul, dist_le_zero] at hd
  exact hd

/-- Quantitative Picard–Lindelöf / Grönwall certificate for the Epoch specification: if curves
`t ↦ Γ i x t` connect `x ∈ B_i` at `t = 0` to `F i x ∈ B(0, R₀)` at `t = 1` with velocity defect
at most `δ` against `X_H`, where `δ e^L ≤ R - R₀`, then `H` satisfies `EpochSpecR k ε R H` (and
every integral curve ends within `δ e^L` of `F i x`, hence equals `F i x` when `δ = 0`). -/
theorem picard_lindelof_epoch_certificate (k : ℕ) (ε R₀ R δ : ℝ) (L : ℝ≥0)
    (H : ℝ → E 2 → ℝ)
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × E 2 => H p.1 p.2))
    (hsupp : ∃ K : Set (E 2), IsCompact K ∧ ∀ t, ∀ y ∉ K, H t y = 0)
    (_hR0 : 0 ≤ R₀) (hδ : 0 ≤ δ) (hgap : δ * Real.exp L ≤ R - R₀) (hRpos : 0 < R)
    (hdens : 1 - ε < (k : ℝ) / R ^ 4)
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith L (hamVF H t))
    (F : ℕ → E 2 → E 2) (Γ : ℕ → E 2 → ℝ → E 2)
    (hinit : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1, Γ i x 0 = x)
    (hend : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1,
      Γ i x 1 = F i x ∧ F i x ∈ closedBall (0 : E 2) R₀)
    (hode : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ v : E 2, HasDerivWithinAt (Γ i x) v (Icc 0 1) t ∧ ‖v - hamVF H t (Γ i x t)‖ ≤ δ) :
    EpochSpecR k ε R H ∧
      (∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1, ∀ γ : ℝ → E 2,
        γ 0 = x → IsIntegralCurveOn γ (hamVF H) (Icc 0 1) →
          dist (γ 1) (F i x) ≤ δ * Real.exp L) := by
  obtain ⟨K, hK, hzero⟩ := hsupp
  obtain ⟨B0, hKB⟩ := hK.isBounded.subset_closedBall (0 : E 2)
  have hB0 : ∀ t (y : E 2), B0 < ‖y‖ → H t y = 0 := by
    intro t y hy
    apply hzero t y
    intro hyK
    have hh := hKB hyK
    rw [mem_closedBall, dist_zero_right] at hh
    linarith
  have hdist : ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1, ∀ γ : ℝ → E 2,
      γ 0 = x → IsIntegralCurveOn γ (hamVF H) (Icc 0 1) →
        dist (γ 1) (F i x) ≤ δ * Real.exp L := by
    intro i hi x hx γ hγ0 hγ
    let Vf : ℝ → E 2 → E 2 := fun t => hamVF H (General.Compile.clamp01 t)
    have hVf : ∀ t, LipschitzWith L (Vf t) := fun t => hL _ (General.Compile.clamp01_mem t)
    choose g' hg_deriv hg_err using fun t =>
      hode i hi x hx (General.Compile.clamp01 t) (General.Compile.clamp01_mem t)
    have hIci : ∀ t ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) 1 ∈ nhdsWithin t (Ici t) := fun t ht =>
      Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
    have hd := dist_le_of_approx_trajectories_ODE (v := Vf) (K := L) (δ := 0)
      (εf := δ) (εg := 0) (f := Γ i x) (g := γ)
      (f' := g') (g' := fun t => Vf t (γ t)) hVf
      (fun t ht => by
        have hd_t : HasDerivWithinAt (Γ i x) (g' t) (Icc 0 1) t := by
          simpa only [General.Compile.clamp01_of_mem ht] using hg_deriv t
        exact hd_t.continuousWithinAt)
      (fun t ht => by
        have hmem := Ico_subset_Icc_self ht
        have hd_t : HasDerivWithinAt (Γ i x) (g' t) (Icc 0 1) t := by
          simpa only [General.Compile.clamp01_of_mem hmem] using hg_deriv t
        exact hd_t.mono_of_mem_nhdsWithin (hIci t ht))
      (fun t ht => by
        have hmem := Ico_subset_Icc_self ht
        simp only [Vf, General.Compile.clamp01_of_mem hmem, dist_eq_norm]
        simpa only [General.Compile.clamp01_of_mem hmem] using hg_err t)
      (fun t ht => (hγ t ht).continuousWithinAt)
      (fun t ht => by
        have hm := (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht)
        simpa only [Vf, General.Compile.clamp01_of_mem (Ico_subset_Icc_self ht)] using hm)
      (fun _ _ => by rw [dist_self])
      (by rw [hinit i hi x hx, hγ0, dist_self])
      1 ⟨zero_le_one, le_rfl⟩
    have hd1 : dist (Γ i x 1) (γ 1) ≤ δ * Real.exp L := by
      simp only [add_zero, sub_zero] at hd
      exact hd.trans (General.gronwallBound_zero_one_le (L := L) hδ)
    rw [dist_comm, ← (hend i hi x hx).1]
    exact hd1
  refine ⟨⟨hsm, ⟨K, hK, hzero⟩, hRpos, hdens,
    fun i _ x _ => General.Compile.exists_integralCurve_global hsm hB0 x, ?_⟩, hdist⟩
  intro i hi x hx γ hγ0 hγ
  have hd := hdist i hi x hx γ hγ0 hγ
  have hF_in := (hend i hi x hx).2
  rw [mem_closedBall, dist_zero_right] at hF_in ⊢
  calc ‖γ 1‖ ≤ ‖F i x‖ + dist (γ 1) (F i x) := by
        rw [dist_eq_norm]; simpa [add_comm] using norm_add_le (F i x) (γ 1 - F i x)
    _ ≤ R₀ + δ * Real.exp L := add_le_add hF_in hd
    _ ≤ R := by linarith

/-! ## 2. Classical 4-stage Runge–Kutta and convergence for `epochHamiltonianQ` -/

/-- Weighted slope `(k₁ + 2k₂ + 2k₃ + k₄) / 6` of classical 4th-order Runge–Kutta for `hamVF H`. -/
def rk4Slope {n : ℕ} (H : ℝ → E n → ℝ) (t dt : ℝ) (y : E n) : E n :=
  let k1 := hamVF H t y
  let k2 := hamVF H (t + dt / 2) (y + (dt / 2) • k1)
  let k3 := hamVF H (t + dt / 2) (y + (dt / 2) • k2)
  let k4 := hamVF H (t + dt) (y + dt • k3)
  ((1 : ℝ) / 6) • (k1 + (2 : ℝ) • k2 + (2 : ℝ) • k3 + k4)

/-- One classical 4th-order Runge–Kutta step from `(t, y)` with step size `dt`. -/
def rk4Step {n : ℕ} (H : ℝ → E n → ℝ) (t dt : ℝ) (y : E n) : E n :=
  y + dt • rk4Slope H t dt y

/-- Exact `N`-step fixed-step RK4 trajectory on `[0, 1]` (`dt = 1 / N`). -/
def rk4Iter {n : ℕ} (H : ℝ → E n → ℝ) (N : ℕ) (x : E n) : ℕ → E n
  | 0 => x
  | m + 1 => rk4Step H ((m : ℝ) / N) (1 / (N : ℝ)) (rk4Iter H N x m)

private lemma smooth_compact_ode_bounds {n : ℕ} {H : ℝ → E n → ℝ}
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (hsupp : ∃ K : Set (E n), IsCompact K ∧ ∀ t, ∀ y ∉ K, H t y = 0) :
    ∃ K C : ℝ≥0,
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        ‖hamVF H t x - hamVF H s x‖ ≤ K * |t - s|) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, ‖hamVF H t x - hamVF H t y‖ ≤ K * ‖x - y‖) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖hamVF H t y‖ ≤ C) := by
  obtain ⟨S, hS, hzero⟩ := hsupp
  obtain ⟨R, hSR⟩ := hS.isBounded.subset_closedBall (0 : E n)
  have hR : ∀ t (y : E n), R < ‖y‖ → H t y = 0 := by
    intro t y hy; apply hzero t y; intro hyS
    have hh := hSR hyS; rw [mem_closedBall, dist_zero_right] at hh; linarith
  have hV : ContDiff ℝ ∞ (General.Ham.hamField H) := General.Ham.hamField_contDiff hsm
  let ψ : ContDiffBump (0 : ℝ) := ⟨2, 3, by positivity, by norm_num⟩
  set Wf : ℝ × E n → E n := fun p => ψ p.1 • General.Ham.hamField H p
  have hW : ContDiff ℝ ∞ Wf := (ψ.contDiff.comp contDiff_fst).smul hV
  have hcs : HasCompactSupport Wf := by
    apply HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) 3).prod
      (isCompact_closedBall (0 : E n) R))
    rintro ⟨t, y⟩ hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with ht | hy
    · have : ψ t = 0 := by
        apply Function.notMem_support.mp; rw [ψ.support_eq]
        exact fun h => ht (ball_subset_closedBall h)
      simp [Wf, this]
    · have hy' : R < ‖y‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hy
      simp [Wf, General.Ham.hamField, General.Compile.hamVF_eq_zero_of_norm hR hy']
  obtain ⟨K, hK⟩ := hW.lipschitzWith_of_hasCompactSupport hcs (by simp)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hW.continuous
  have hWV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, Wf (t, y) = hamVF H t y := by
    intro t ht y
    have hball : t ∈ closedBall (0 : ℝ) 2 := by
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp [Wf, General.Ham.hamField, ψ.one_of_mem_closedBall hball]
  refine ⟨K, ⟨max C 0, le_max_right _ _⟩, ?_, ?_, ?_⟩
  · intro s hs t ht x
    have := hK.dist_le_mul (t, x) (s, x)
    rw [hWV t ht x, hWV s hs x] at this
    simpa [dist_eq_norm, Prod.dist_eq, Real.dist_eq] using this
  · intro t ht x y
    have := hK.dist_le_mul (t, x) (t, y)
    rw [hWV t ht x, hWV t ht y] at this
    simpa [dist_eq_norm, Prod.dist_eq] using this
  · intro t ht y
    rw [← hWV t ht y]
    exact (hC (t, y)).trans (le_max_left _ _)

private lemma rk4Slope_sub_hamVF_bound {n : ℕ} {H : ℝ → E n → ℝ} {K C : ℝ≥0}
    (htime : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖hamVF H t x - hamVF H s x‖ ≤ K * |t - s|)
    (hspace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, ‖hamVF H t x - hamVF H t y‖ ≤ K * ‖x - y‖)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖hamVF H t y‖ ≤ C)
    {t dt : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hdt : 0 ≤ dt) (htdt : t + dt ≤ 1) (y : E n) :
    ‖rk4Slope H t dt y - hamVF H t y‖ ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by
  have hstage : ∀ (α : ℝ) (v : E n), 0 ≤ α → α ≤ 1 → ‖v‖ ≤ C →
      ‖hamVF H (t + α * dt) (y + (α * dt) • v) - hamVF H t y‖ ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by
    intro α v hα0 hα1 hv
    have hmem : t + α * dt ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [ht.1], by nlinarith [htdt]⟩
    have h1 := hspace (t + α * dt) hmem (y + (α * dt) • v) y
    have h2 := htime t ht (t + α * dt) hmem y
    have hαdt : 0 ≤ α * dt := mul_nonneg hα0 hdt
    have hnorm : ‖y + (α * dt) • v - y‖ ≤ C * dt := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hαdt]
      have h1dt : 0 ≤ 1 * dt := by linarith
      calc (α * dt) * ‖v‖ ≤ (1 * dt) * C :=
            mul_le_mul (mul_le_mul_of_nonneg_right hα1 hdt) hv (norm_nonneg _) h1dt
        _ = C * dt := by ring
    have habs : |t + α * dt - t| ≤ dt := by
      rw [add_sub_cancel_left, abs_of_nonneg hαdt]
      nlinarith
    calc ‖hamVF H (t + α * dt) (y + (α * dt) • v) - hamVF H t y‖
        ≤ ‖hamVF H (t + α * dt) (y + (α * dt) • v) - hamVF H (t + α * dt) y‖ +
            ‖hamVF H (t + α * dt) y - hamVF H t y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (K : ℝ) * (C * dt) + (K : ℝ) * dt :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left hnorm K.2))
            (h2.trans (mul_le_mul_of_nonneg_left habs K.2))
      _ = ((K : ℝ) + (K : ℝ) * C) * dt := by ring
  set k1 := hamVF H t y
  set k2 := hamVF H (t + dt / 2) (y + (dt / 2) • k1)
  set k3 := hamVF H (t + dt / 2) (y + (dt / 2) • k2)
  set k4 := hamVF H (t + dt) (y + dt • k3)
  have hmem2 : t + dt / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [htdt]⟩
  have hk1 : ‖k1‖ ≤ C := hspeed t ht y
  have hk2 : ‖k2‖ ≤ C := hspeed _ hmem2 _
  have hk3 : ‖k3‖ ≤ C := hspeed _ hmem2 _
  have hd2 : ‖k2 - k1‖ ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by
    simpa [k2, div_eq_mul_inv, mul_comm] using hstage (1 / 2) k1 (by norm_num) (by norm_num) hk1
  have hd3 : ‖k3 - k1‖ ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by
    simpa [k3, div_eq_mul_inv, mul_comm] using hstage (1 / 2) k2 (by norm_num) (by norm_num) hk2
  have hd4 : ‖k4 - k1‖ ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by
    simpa [k4] using hstage 1 k3 zero_le_one le_rfl hk3
  have hid : rk4Slope H t dt y - k1 =
      ((1 : ℝ) / 6) • ((2 : ℝ) • (k2 - k1) + (2 : ℝ) • (k3 - k1) + (k4 - k1)) := by
    dsimp [rk4Slope, k1, k2, k3, k4]
    module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  have hsum : ‖(2 : ℝ) • (k2 - k1) + (2 : ℝ) • (k3 - k1) + (k4 - k1)‖ ≤
      5 * (((K : ℝ) + (K : ℝ) * C) * dt) := by
    calc ‖(2 : ℝ) • (k2 - k1) + (2 : ℝ) • (k3 - k1) + (k4 - k1)‖
        ≤ ‖(2 : ℝ) • (k2 - k1)‖ + ‖(2 : ℝ) • (k3 - k1)‖ + ‖k4 - k1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = 2 * ‖k2 - k1‖ + 2 * ‖k3 - k1‖ + ‖k4 - k1‖ := by
          simp [norm_smul]
      _ ≤ 2 * (((K : ℝ) + (K : ℝ) * C) * dt) + 2 * (((K : ℝ) + (K : ℝ) * C) * dt) +
            ((K : ℝ) + (K : ℝ) * C) * dt := by linarith
      _ = 5 * (((K : ℝ) + (K : ℝ) * C) * dt) := by ring
  have hKC : 0 ≤ ((K : ℝ) + (K : ℝ) * C) * dt := by positivity
  linarith

/-- **Perturbed fixed-step RK4 convergence for `epochHamiltonianQ`.**
For every `k ≥ 10` and `ε ∈ (0, 1)`, there exist a step threshold `N₀ ≥ 1` and a positive
perturbation tolerance `δ₀ > 0` such that for every `N ≥ N₀`, every source ball `i < k`, every
source point `x ∈ B_i`, and every numerical sequence `y : ℕ → ℝ⁴` starting within `δ₀` of `x`
and satisfying the fixed-step RK4 recurrence up to `δ₀ / N` rounding error per step, the terminal
iterate `y N` lies in the closed origin ball `B(0, epochRadius k ε)`, with
`k / (epochRadius k ε)⁴ = 1 - ε/2 > 1 - ε`. -/
theorem epoch_rk4_convergence (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let H := General.epochHamiltonianQ k ε
    let R := General.epochRadius k ε
    ∃ (N₀ : ℕ) (δ₀ : ℝ), 1 ≤ N₀ ∧ 0 < δ₀ ∧ (1 - ε < (k : ℝ) / R ^ 4) ∧
      ∀ (N : ℕ), N₀ ≤ N →
        ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1,
          ∀ y : ℕ → E 2,
            ‖y 0 - x‖ ≤ δ₀ →
            (∀ m < N, ‖y (m + 1) - rk4Step H ((m : ℝ) / N) (1 / (N : ℝ)) (y m)‖ ≤ δ₀ / N) →
            y N ∈ closedBall (0 : E 2) R := by
  intro H R
  have hthm := four_dim_theorem k hk ε hε0 hε1
  have hQ : EpochSpecR k ε (General.epochRadiusQ k ε) H := hthm.1
  have hE := epoch_theorem_ten k hk ε hε0 hε1
  have hgap : 0 < R - General.epochRadiusQ k ε :=
    sub_pos.mpr (General.epochRadiusQ_lt_epochRadius (by omega) hε0 hε1)
  obtain ⟨K, C, htime, hspace, hspeed⟩ := smooth_compact_ode_bounds hQ.smooth hQ.compactSupport
  set M_rk : ℝ := (K : ℝ) + (K : ℝ) * C
  have hM_nonneg : 0 ≤ M_rk := by dsimp [M_rk]; positivity
  set δ₀ : ℝ := (R - General.epochRadiusQ k ε) / (4 * Real.exp K)
  have hδ₀ : 0 < δ₀ := div_pos hgap (by positivity)
  set N₀ : ℕ := ⌈4 * M_rk * Real.exp K / (R - General.epochRadiusQ k ε)⌉₊ + 1
  refine ⟨N₀, δ₀, by omega, hδ₀, hE.density, ?_⟩
  intro N hN i hi x hx y hy0 hystep
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨γ, hγ0, hγ⟩ := hQ.exists_curve i hi x hx
  have hγ1 := hQ.maps_into i hi x hx γ hγ0 (hγ.isIntegralCurveOn _)
  have hB : Effective.ODE.Bounds (hamVF H) γ K K C :=
    ⟨K.2, K.2, C.2, fun t _ => hγ t, fun t ht => hspeed t ht (γ t), htime, hspace⟩
  let v : ℕ → E 2 := fun m => (N : ℝ) • (y (m + 1) - y m)
  have hv_step : ∀ m < N, y (m + 1) = y m + (1 / (N : ℝ)) • v m := by
    intro m _
    simp only [v, smul_smul]
    rw [one_div_mul_cancel hN'.ne', one_smul, add_sub_cancel]
  have hv_err : ∀ m < N,
      ‖v m - hamVF H (Effective.ODE.gridTime N m) (y m)‖ ≤ δ₀ + M_rk / N := by
    intro m hm
    have hm_mem : Effective.ODE.gridTime N m ∈ Icc (0 : ℝ) 1 :=
      Effective.ODE.gridTime_mem hNpos (by omega)
    have hm1_le : Effective.ODE.gridTime N m + 1 / (N : ℝ) ≤ 1 := by
      rw [← Effective.ODE.gridTime_succ]
      exact (Effective.ODE.gridTime_mem hNpos (by omega : m + 1 ≤ N)).2
    have hrk := rk4Slope_sub_hamVF_bound htime hspace hspeed hm_mem (by positivity) hm1_le (y m)
    have hpert := hystep m hm
    have hv_sub : v m - rk4Slope H ((m : ℝ) / N) (1 / (N : ℝ)) (y m) =
        (N : ℝ) • (y (m + 1) - rk4Step H ((m : ℝ) / N) (1 / (N : ℝ)) (y m)) := by
      simp only [v, rk4Step, smul_sub, smul_add, smul_smul]
      rw [mul_one_div_cancel hN'.ne', one_smul]
      abel
    have h1 : ‖v m - rk4Slope H (Effective.ODE.gridTime N m) (1 / (N : ℝ)) (y m)‖ ≤ δ₀ := by
      dsimp only [Effective.ODE.gridTime]
      rw [hv_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hN']
      calc (N : ℝ) * ‖y (m + 1) - rk4Step H ((m : ℝ) / N) (1 / (N : ℝ)) (y m)‖
          ≤ (N : ℝ) * (δ₀ / N) := mul_le_mul_of_nonneg_left hpert hN'.le
        _ = δ₀ := mul_div_cancel₀ _ hN'.ne'
    calc ‖v m - hamVF H (Effective.ODE.gridTime N m) (y m)‖
        ≤ ‖v m - rk4Slope H (Effective.ODE.gridTime N m) (1 / (N : ℝ)) (y m)‖ +
            ‖rk4Slope H (Effective.ODE.gridTime N m) (1 / (N : ℝ)) (y m) -
              hamVF H (Effective.ODE.gridTime N m) (y m)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ₀ + M_rk * (1 / (N : ℝ)) := add_le_add h1 hrk
      _ = δ₀ + M_rk / N := by ring
  have hgrid := Effective.PackingCertificate.grid_error hB hNpos y v
    (by positivity : 0 ≤ δ₀ + M_rk / N) hv_step hv_err le_rfl
  have hgt1 : Effective.ODE.gridTime N N = 1 := div_self hN'.ne'
  rw [hgt1, hγ0] at hgrid
  have hN_ge : 4 * M_rk * Real.exp K / (R - General.epochRadiusQ k ε) ≤ (N : ℝ) := by
    have hceil := Nat.le_ceil (4 * M_rk * Real.exp K / (R - General.epochRadiusQ k ε))
    have hN0_le : ((⌈4 * M_rk * Real.exp K / (R - General.epochRadiusQ k ε)⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (show _ ≤ N by omega)
    exact hceil.trans hN0_le
  have hterm : (2 * M_rk / (N : ℝ)) * Real.exp K ≤ (R - General.epochRadiusQ k ε) / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN']
    have := (div_le_iff₀ hgap).mp hN_ge
    linarith
  have hgrid' : ‖y N - γ 1‖ ≤ (‖y 0 - x‖ + (δ₀ + M_rk / N) + M_rk / N) * Real.exp K := by
    simpa only [M_rk] using hgrid
  have herr : ‖y N - γ 1‖ ≤ R - General.epochRadiusQ k ε := by
    calc ‖y N - γ 1‖
        ≤ (‖y 0 - x‖ + (δ₀ + M_rk / N) + M_rk / N) * Real.exp K := hgrid'
      _ ≤ (δ₀ + δ₀ + 2 * M_rk / N) * Real.exp K := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          have h_sum : ‖y 0 - x‖ + (δ₀ + M_rk / N) + M_rk / N ≤ δ₀ + (δ₀ + M_rk / N) + M_rk / N :=
            add_le_add (add_le_add hy0 le_rfl) le_rfl
          exact h_sum.trans (le_of_eq (by ring))
      _ = 2 * (δ₀ * Real.exp K) + (2 * M_rk / N) * Real.exp K := by ring
      _ ≤ 2 * ((R - General.epochRadiusQ k ε) / 4) + (R - General.epochRadiusQ k ε) / 2 := by
          have hd_eq : δ₀ * Real.exp K = (R - General.epochRadiusQ k ε) / 4 := by
            dsimp [δ₀]; field_simp
          rw [hd_eq]
          exact add_le_add le_rfl hterm
      _ = R - General.epochRadiusQ k ε := by ring
  rw [mem_closedBall, dist_zero_right] at hγ1 ⊢
  calc ‖y N‖ ≤ ‖γ 1‖ + ‖y N - γ 1‖ := by
        simpa [add_comm] using norm_add_le (γ 1) (y N - γ 1)
    _ ≤ General.epochRadiusQ k ε + (R - General.epochRadiusQ k ε) := add_le_add hγ1 herr
    _ = R := by ring

/-- Exact-real fixed-step RK4 corollary (`δ = 0`, `y = rk4Iter H N x`). -/
theorem epoch_exact_rk4_convergence (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let H := General.epochHamiltonianQ k ε
    let R := General.epochRadius k ε
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ (1 - ε < (k : ℝ) / R ^ 4) ∧
      ∀ N ≥ N₀, ∀ i < k, ∀ x ∈ closedBall (epochCenter i) 1,
        rk4Iter H N x N ∈ closedBall (0 : E 2) R := by
  intro H R
  obtain ⟨N₀, δ₀, hN₀, hδ₀, hdens, hconv⟩ := epoch_rk4_convergence k hk ε hε0 hε1
  refine ⟨N₀, hN₀, hdens, fun N hN i hi x hx => hconv N hN i hi x hx (rk4Iter H N x) ?_ ?_⟩
  · simp [rk4Iter, hδ₀.le]
  · intro m hm
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) (hN₀.trans hN))
    have hstep_eq : rk4Iter H N x (m + 1) = rk4Step H ((m : ℝ) / N) (1 / (N : ℝ)) (rk4Iter H N x m) := rfl
    rw [hstep_eq, sub_self, norm_zero]
    exact div_nonneg hδ₀.le hNpos.le

#assert_publication_axioms picard_lindelof_curve_unique
#assert_publication_axioms picard_lindelof_epoch_certificate
#assert_publication_axioms epoch_rk4_convergence
#assert_publication_axioms epoch_exact_rk4_convergence
#check_explicit rk4Slope
#check_explicit rk4Step
#check_explicit rk4Iter
