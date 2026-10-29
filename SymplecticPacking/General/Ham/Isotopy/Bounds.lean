import SymplecticPacking.General.Ham.Isotopy.Geometry

/-!
# A uniform bound for the common isotopy

For embeddings with images in the ball `B(R₀)` (`TargetIsoInput`), every stage of the common
isotopy `isoF` stays in the ball of the explicit radius `isotopyRadius f s r₃ R₀`
(`TargetIsoInput.isoF_norm_le`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Finset Problem
open scoped Classical RealInnerProductSpace

variable {n k : ℕ}

/-- The input including the target bound used in the paper. -/
structure TargetIsoInput (f : Fin k → E n → E n) (s : Fin k → E n)
    (r1 r2 r3 r4 ρ : Fin k → ℝ) (R0 : ℝ) : Prop extends IsoInput f s r1 r2 r3 r4 ρ where
  one_le_k : 1 ≤ k
  target_pos : 0 < R0
  target : ∀ i, ∀ u ∈ closedBall (0 : E n) (r4 i), ‖f i u‖ < R0

lemma rank_lt (h : Fin k → ℝ) (i : Fin k) : rank h i < k := by
  have hh : (univ.filter fun j => prec h j i) ⊂ (univ : Finset (Fin k)) := by
    refine ⟨filter_subset _ _, ?_⟩
    intro hs
    have hi := hs (mem_univ i)
    exact prec_irrefl h i (Finset.mem_filter.mp hi).2
  simpa [rank] using Finset.card_lt_card hh

lemma routeConst_one_le {s C : Fin k → E n} {r3 : Fin k → ℝ}
    (hr : ∀ i, 0 ≤ r3 i) : 1 ≤ routeConst s C r3 := by
  unfold routeConst
  have := sum_nonneg (s := univ) (f := fun i => 2 * (r3 i + ‖s i‖ + ‖C i‖))
    (fun i _ => by have := hr i; positivity)
  linarith

lemma routeConst_single {s C : Fin k → E n} {r3 : Fin k → ℝ}
    (hr : ∀ i, 0 ≤ r3 i) (i : Fin k) :
    r3 i + ‖s i‖ + ‖C i‖ ≤ routeConst s C r3 := by
  have hh := single_le_sum (f := fun j => 2 * (r3 j + ‖s j‖ + ‖C j‖))
    (fun j _ => by have := hr j; positivity) (mem_univ i)
  unfold routeConst
  linarith [hr i, norm_nonneg (s i), norm_nonneg (C i)]

/-- The sharper route estimate stated before the common isotopy bound. -/
theorem routePos_norm_le (hn : 0 < n) {s C : Fin k → E n} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) {σ : Fin 5 → ℝ} (hσ : ∀ j, σ j ∈ Icc (0 : ℝ) 1)
    (i : Fin k) :
    ‖routePos s C Λ σ i‖ ≤ max ‖s i‖ ‖C i‖ + 2 * ((k : ℝ) - 1) * Λ := by
  have hc := hσ 2
  have hc0 : 0 ≤ 1 - σ 2 := by linarith [hc.2]
  have hconv : s i + σ 2 • (C i - s i) = (1 - σ 2) • s i + σ 2 • C i := by module
  have hb : ‖s i + σ 2 • (C i - s i)‖ ≤ max ‖s i‖ ‖C i‖ := by
    rw [hconv]
    calc
      _ ≤ ‖(1 - σ 2) • s i‖ + ‖σ 2 • C i‖ := norm_add_le _ _
      _ = (1 - σ 2) * ‖s i‖ + σ 2 * ‖C i‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg hc.1]
      _ ≤ (1 - σ 2) * max ‖s i‖ ‖C i‖ + σ 2 * max ‖s i‖ ‖C i‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hc.1)
      _ = _ := by ring
  have hd (a b : Fin 5) : |σ a - σ b| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(hσ a).1, (hσ a).2, (hσ b).1, (hσ b).2]
  have hr (h : Fin k → ℝ) : (rank h i : ℝ) ≤ (k : ℝ) - 1 := by
    have hlt := rank_lt h i
    have : (rank h i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    linarith
  have hterm (a b : Fin 5) (h : Fin k → ℝ) (v : E n) (hv : ‖v‖ = 1) :
      ‖((σ a - σ b) * Λ * rank h i) • v‖ ≤ ((k : ℝ) - 1) * Λ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hΛ, abs_of_nonneg (Nat.cast_nonneg (rank h i) : (0 : ℝ) ≤ rank h i),
      hv, mul_one]
    calc
      _ ≤ 1 * Λ * (rank h i : ℝ) := by gcongr; exact hd a b
      _ ≤ 1 * Λ * ((k : ℝ) - 1) := by gcongr; exact hr h
      _ = _ := by ring
  have hq := hterm 0 3 (height s (dirQ n)) (dirQ n) (norm_dirQ hn)
  have hp := hterm 1 4 (height C (dirP n)) (dirP n) (norm_dirP hn)
  unfold routePos
  have ha := norm_add_le
    (s i + σ 2 • (C i - s i))
    (((σ 0 - σ 3) * Λ * rank (height s (dirQ n)) i) • dirQ n)
  have hb' := norm_add_le
    (s i + σ 2 • (C i - s i) +
      ((σ 0 - σ 3) * Λ * rank (height s (dirQ n)) i) • dirQ n)
    (((σ 1 - σ 4) * Λ * rank (height C (dirP n)) i) • dirP n)
  linarith

variable {f : Fin k → E n → E n} {s : Fin k → E n}
  {r1 r2 r3 r4 ρ : Fin k → ℝ} {R0 : ℝ}

/-- The uniform radius of the paper's common isotopy. -/
def isotopyRadius (f : Fin k → E n → E n) (s : Fin k → E n)
    (r3 : Fin k → ℝ) (R0 : ℝ) : ℝ :=
  2 * k * routeConst s (farC f r3) r3 + bigL f r3 * rsum r3 + R0 / tau f r3

/-- Every stage satisfies the explicit radius, rather than only some compact bound. -/
theorem TargetIsoInput.isoF_norm_le (hf : TargetIsoInput f s r1 r2 r3 r4 ρ R0)
    (i : Fin k) (t : ℝ) {u : E n} (hu : u ∈ closedBall (0 : E n) (r3 i)) :
    ‖isoF f s r3 i t u‖ ≤ isotopyRadius f s r3 R0 := by
  let h := hf.toIsoInput
  let Λ := routeConst s (farC f r3) r3
  have hL := h.one_le_L
  have hsum := h.rsum_pos
  have hτ := h.tau_pos
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hf.one_le_k
  have hΛ : 1 ≤ Λ := routeConst_one_le (fun j => (h.r3_pos j).le)
  have hsingle : r3 i + ‖s i‖ + ‖farC f r3 i‖ ≤ Λ :=
    routeConst_single (fun j => (h.r3_pos j).le) i
  have hC : ‖farC f r3 i‖ ≤ Λ := by
    linarith [h.r3_pos i, norm_nonneg (s i)]
  have hprod : 0 ≤ bigL f r3 * rsum r3 := by positivity
  have htarget : 0 ≤ R0 / tau f r3 := (div_pos hf.target_pos hτ).le
  have hbase : Λ ≤ 2 * k * Λ := by nlinarith
  have hu4 : u ∈ ball (0 : E n) (r4 i) :=
    (closedBall_subset_ball (h.radii i).2.2.2.1) hu
  change ‖isoF f s r3 i t u‖ ≤ 2 * k * Λ + bigL f r3 * rsum r3 + R0 / tau f r3
  rcases slot_cases t with ht | ht | ht | ht
  · rw [isoF_route' ht]
    have hp := routePos_norm_le (n := n) (s := s) (C := farC f r3) (Λ := Λ)
      (σ := routeClocks t) (by have := h.one_le_n; omega) (by linarith : 0 ≤ Λ)
      (fun j => clk_mem j t) i
    have hm : max ‖s i‖ ‖farC f r3 i‖ + r3 i ≤ Λ := by
      rw [← max_add_add_right, max_le_iff]
      constructor <;> linarith [norm_nonneg (s i), norm_nonneg (farC f r3 i)]
    have hn := norm_add_le (pos f s r3 t i) u
    have huu := mem_closedBall_zero_iff.mp hu
    change ‖pos f s r3 t i‖ ≤ _ at hp
    nlinarith
  · rw [isoF_linear' ht]
    have hb := h.norm_linPath_le i (clk_mem 5 t) hu
    have hn := norm_add_le (farC f r3 i) (linPath f i (clk 5 t) u)
    have hh : bigL f r3 ≤ bigL f r3 * rsum r3 := by nlinarith
    linarith
  · rw [isoF_shape' h ht]
    have hs := h.shapeParam_mem t
    have hs01 : tau f r3 * clk 6 t ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1, hs.2.trans (by norm_num)⟩
    have hb := norm_shape_le (f := f i) (R := r3 i) (L := bigL f r3)
      (fun y hy => h.norm_fderiv_le i hy) (s := tau f r3 * clk 6 t) (u := u)
      ((norm_smul_le_of_mem_Icc hs01 u).trans (mem_closedBall_zero_iff.mp hu))
    have hb' : ‖shape (f i) (tau f r3 * clk 6 t) u‖ ≤ bigL f r3 * rsum r3 :=
      hb.trans (mul_le_mul_of_nonneg_left
        ((mem_closedBall_zero_iff.mp hu).trans (h.r3_le_rsum i)) (by linarith))
    have hn := norm_add_le (farC f r3 i) (shape (f i) (tau f r3 * clk 6 t) u)
    linarith
  · rw [isoF_tail' h ht i hu4]
    let v := tau f r3 + (1 - tau f r3) * clk 7 t
    have hv := tailParam_mem (f := f) (r3 := r3) t
    have hv0 : 0 < v := hτ.trans_le hv.1
    have hvu : v • u ∈ closedBall (0 : E n) (r4 i) :=
      mem_closedBall_zero_iff.mpr ((norm_smul_le_of_mem_Icc
        ⟨hv0.le, hv.2⟩ u).trans ((mem_closedBall_zero_iff.mp hu).trans
          (h.radii i).2.2.2.1.le))
    have hb := hf.target i (v • u) hvu
    have hr : ‖tailMap f i v u‖ ≤ R0 / tau f r3 := by
      rw [tailMap, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hv0).le]
      calc
        _ ≤ v⁻¹ * R0 := mul_le_mul_of_nonneg_left hb.le (inv_pos.mpr hv0).le
        _ = R0 / v := by ring
        _ ≤ R0 / tau f r3 := div_le_div_of_nonneg_left hf.target_pos.le hτ hv.1
    change ‖tailMap f i v u‖ ≤ _
    have : 0 ≤ 2 * (k : ℝ) * Λ := by positivity
    linarith

end SymplecticPacking.General.Ham.Isotopy
