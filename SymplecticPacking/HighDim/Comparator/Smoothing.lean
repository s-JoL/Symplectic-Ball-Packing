import SymplecticPacking.HighDim.Comparator.Poly

/-!
# Smoothing by log-sum-exp (paper `thm:cmp-main`)

`lse c F = c⁻¹ log Σ_r exp(c ℓ_r)` is smooth and satisfies
`max_r ℓ_r ≤ lse c F ≤ max_r ℓ_r + (log #r)/c`.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m : ℕ}

/-- `c⁻¹ log Σ_r exp(c ℓ_r(p))`. -/
def lse (c : ℝ) (F : PolyFn m) (p : Moments m) : ℝ :=
  c⁻¹ * Real.log (F.map fun a => Real.exp (c * a.eval p)).sum

/-- An explicit integer scale with `log(#r)/c < δ`: `c = ⌈#r/δ⌉ + 1` (since `log x ≤ x`). -/
def lseScale (F : PolyFn m) (δ : ℝ) : ℝ := (⌈(F.length : ℝ) / δ⌉₊ + 1 : ℕ)

/-- The exponential sum `S(p) = Σ_r exp(c ℓ_r(p))`. -/
def expSum (c : ℝ) (F : PolyFn m) (p : Moments m) : ℝ :=
  (F.map fun a => Real.exp (c * a.eval p)).sum

theorem expSum_pos (c : ℝ) {F : PolyFn m} (hF : F ≠ []) (p : Moments m) : 0 < expSum c F p := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil F hF
  have hmem : Real.exp (c * a.eval p) ∈ F.map fun a => Real.exp (c * a.eval p) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  exact lt_of_lt_of_le (Real.exp_pos _) (List.single_le_sum
    (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact (Real.exp_pos _).le) _ hmem)

theorem expSum_smooth (c : ℝ) (F : PolyFn m) : ContDiff ℝ ∞ (expSum c F) := by
  unfold expSum
  induction F with
  | nil => simpa using contDiff_const
  | cons a F ih =>
    simp only [List.map_cons, List.sum_cons]
    refine ContDiff.add ?_ ih
    refine Real.contDiff_exp.comp (contDiff_const.mul ?_)
    unfold AffinePiece.eval
    fun_prop

theorem lse_smooth (c : ℝ) {F : PolyFn m} (hF : F ≠ []) : ContDiff ℝ ∞ (lse c F) := by
  have : lse c F = fun p => c⁻¹ * Real.log (expSum c F p) := rfl
  rw [this]
  exact contDiff_const.mul ((expSum_smooth c F).log fun p => (expSum_pos c hF p).ne')

theorem eval_le_lse {c : ℝ} (hc : 0 < c) {F : PolyFn m} (hF : F ≠ []) (p : Moments m) :
    PolyFn.eval F p ≤ lse c F p := by
  obtain ⟨a, ha, he⟩ := PolyFn.eval_mem hF p
  have hmem : Real.exp (c * a.eval p) ∈ F.map fun a => Real.exp (c * a.eval p) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hle : Real.exp (c * a.eval p) ≤ expSum c F p :=
    List.single_le_sum (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact (Real.exp_pos _).le) _ hmem
  have hlog : c * a.eval p ≤ Real.log (expSum c F p) := by
    rw [← Real.log_exp (c * a.eval p)]
    exact Real.log_le_log (Real.exp_pos _) hle
  change PolyFn.eval F p ≤ c⁻¹ * Real.log (expSum c F p)
  rw [he, ← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]
  exact hlog

theorem lse_le_eval {c : ℝ} (hc : 0 < c) {F : PolyFn m} (hF : F ≠ []) (p : Moments m) :
    lse c F p ≤ PolyFn.eval F p + Real.log F.length / c := by
  have hlen : (0 : ℝ) < F.length := by
    have := List.length_pos_of_ne_nil hF
    exact_mod_cast this
  have hS : expSum c F p ≤ F.length * Real.exp (c * PolyFn.eval F p) := by
    have := List.sum_le_card_nsmul (F.map fun a => Real.exp (c * a.eval p))
      (Real.exp (c * PolyFn.eval F p)) (fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (PolyFn.le_eval hb p) hc.le))
    simpa [expSum, nsmul_eq_mul] using this
  have hlog : Real.log (expSum c F p) ≤ Real.log F.length + c * PolyFn.eval F p := by
    calc Real.log (expSum c F p) ≤ Real.log (F.length * Real.exp (c * PolyFn.eval F p)) :=
          Real.log_le_log (expSum_pos c hF p) hS
      _ = Real.log F.length + c * PolyFn.eval F p := by
          rw [Real.log_mul hlen.ne' (Real.exp_pos _).ne', Real.log_exp]
  change c⁻¹ * Real.log (expSum c F p) ≤ _
  rw [← div_eq_inv_mul, div_le_iff₀ hc]
  have : (PolyFn.eval F p + Real.log F.length / c) * c =
      c * PolyFn.eval F p + Real.log F.length := by
    field_simp
  rw [this]
  linarith

theorem lse_lseScale_le {F : PolyFn m} (hF : F ≠ []) {δ : ℝ} (hδ : 0 < δ) (p : Moments m) :
    lse (lseScale F δ) F p < PolyFn.eval F p + δ := by
  have hlen : (0 : ℝ) < F.length := by
    have := List.length_pos_of_ne_nil hF
    exact_mod_cast this
  set c := lseScale F δ
  have hc1 : (F.length : ℝ) / δ < c := by
    simp only [c, lseScale]
    push_cast
    linarith [Nat.le_ceil ((F.length : ℝ) / δ)]
  have hc : 0 < c := lt_trans (div_pos hlen hδ) hc1
  have hlog : Real.log F.length < F.length := by
    have := Real.log_le_sub_one_of_pos hlen
    linarith
  have h2 : Real.log F.length / c < δ := by
    rw [div_lt_iff₀ hc]
    have : (F.length : ℝ) < δ * c := by
      rw [div_lt_iff₀ hδ] at hc1; linarith
    linarith
  have := lse_le_eval hc hF p
  linarith

end SymplecticPacking.HighDim
