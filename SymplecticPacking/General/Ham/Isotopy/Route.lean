import SymplecticPacking.General.Ham.Isotopy.Data

/-!
# The translation route from the source centres to the far centres

Arbitrary pairwise separated centres `sᵢ` are moved to the far centres `Cᵢ` along
`pᵢ = sᵢ + σ₂ (Cᵢ - sᵢ) + (σ₀ - σ₃) Λ ρᵢ e_q + (σ₁ - σ₄) Λ ρ'ᵢ e_p`, in five phases run by the
clocks `σ₀, …, σ₄`:

1. rise in the `q₁`-direction to the level `Λ ρᵢ`, `ρᵢ` the rank of `sᵢ` by its `q₁`-coordinate;
2. rise in the `p₁`-direction to `Λ ρ'ᵢ`, `ρ'ᵢ` the rank of `Cᵢ` by its `p₁`-coordinate;
3. move straight from `sᵢ` to `Cᵢ`, keeping both offsets;
4. remove the `q₁`-offset; 5. remove the `p₁`-offset.

Ranks are taken by the coordinate, ties broken by the index, so a rank difference has the sign of
the coordinate difference: phases 1 and 5 do not decrease distances, and in phases 2–4 one of the
offsets separates the balls by `Λ`. With `Λ = 1 + Σᵢ 2(r₃ᵢ + |sᵢ| + |Cᵢ|)` all balls of radii
`r₃ᵢ` stay disjoint.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Finset Problem
open scoped Classical RealInnerProductSpace ContDiff

variable {n k : ℕ}

/-! ### Directions -/

/-- The unit vector `e_{q₁}` (`0` if `n = 0`). -/
def dirQ (n : ℕ) : E n := if h : 0 < n then EuclideanSpace.single ⟨0, by omega⟩ 1 else 0
/-- The unit vector `e_{p₁}` (`0` if `n = 0`). -/
def dirP (n : ℕ) : E n := if h : 0 < n then EuclideanSpace.single ⟨n, by omega⟩ 1 else 0

lemma norm_dirQ (hn : 0 < n) : ‖dirQ n‖ = 1 := by
  simp [dirQ, hn]

lemma norm_dirP (hn : 0 < n) : ‖dirP n‖ = 1 := by
  simp [dirP, hn]

lemma inner_dirQ_dirP : ⟪dirQ n, dirP n⟫ = 0 := by
  unfold dirQ dirP
  split_ifs with h
  · rw [EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply, Fin.ext_iff]; omega
  · simp

/-! ### Ranks -/

/-- `j ≺ i`: lexicographic order on (height, index). -/
def prec (h : Fin k → ℝ) (j i : Fin k) : Prop := h j < h i ∨ (h j = h i ∧ j < i)

/-- Rank of `i` in the order `≺`. -/
def rank (h : Fin k → ℝ) (i : Fin k) : ℕ := (univ.filter fun j => prec h j i).card

lemma prec_irrefl (h : Fin k → ℝ) (i : Fin k) : ¬ prec h i i := by simp [prec]

lemma prec_trans {h : Fin k → ℝ} {a b c : Fin k} (h1 : prec h a b) (h2 : prec h b c) :
    prec h a c := by
  unfold prec at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

lemma prec_total {h : Fin k → ℝ} {a b : Fin k} (hab : a ≠ b) : prec h a b ∨ prec h b a := by
  unfold prec
  rcases lt_trichotomy (h a) (h b) with e | e | e
  · exact Or.inl (Or.inl e)
  · rcases lt_or_gt_of_ne hab with e' | e'
    · exact Or.inl (Or.inr ⟨e, e'⟩)
    · exact Or.inr (Or.inr ⟨e.symm, e'⟩)
  · exact Or.inr (Or.inl e)

lemma rank_lt_of_prec {h : Fin k → ℝ} {a b : Fin k} (hab : prec h a b) : rank h a < rank h b := by
  unfold rank
  apply Finset.card_lt_card
  refine ⟨fun j hj => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact prec_trans hj hab
  · have : a ∈ univ.filter fun j => prec h j a := hsub (by simpa using hab)
    simp [prec_irrefl] at this

/-- The rank difference has the sign of the height difference, and is nonzero. -/
lemma rank_sign (h : Fin k → ℝ) {i j : Fin k} (hij : i ≠ j) :
    0 ≤ (h i - h j) * ((rank h i : ℝ) - rank h j) ∧ (1 : ℝ) ≤ |(rank h i : ℝ) - rank h j| := by
  rcases prec_total (h := h) hij with e | e
  · have hr := rank_lt_of_prec e
    have hle : h i ≤ h j := by rcases e with e | ⟨e, -⟩ <;> linarith
    have hr' : (rank h i : ℝ) + 1 ≤ rank h j := by exact_mod_cast hr
    refine ⟨mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith), ?_⟩
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have hr := rank_lt_of_prec e
    have hle : h j ≤ h i := by rcases e with e | ⟨e, -⟩ <;> linarith
    have hr' : (rank h j : ℝ) + 1 ≤ rank h i := by exact_mod_cast hr
    refine ⟨mul_nonneg (by linarith) (by linarith), ?_⟩
    rw [abs_of_nonneg (by linarith)]; linarith

/-! ### The route -/

/-- The height of a point in direction `e`. -/
def height (x : Fin k → E n) (e : E n) (i : Fin k) : ℝ := ⟪x i, e⟫

/-- The route constant `Λ = 1 + Σᵢ 2 (r₃ᵢ + |sᵢ| + |Cᵢ|)`. -/
def routeConst (s C : Fin k → E n) (r3 : Fin k → ℝ) : ℝ :=
  1 + ∑ i, 2 * (r3 i + ‖s i‖ + ‖C i‖)

/-- The route position of ball `i` for the clock values `σ₀, …, σ₄`. -/
def routePos (s C : Fin k → E n) (Λ : ℝ) (σ : Fin 5 → ℝ) (i : Fin k) : E n :=
  s i + σ 2 • (C i - s i) + ((σ 0 - σ 3) * Λ * rank (height s (dirQ n)) i) • dirQ n
    + ((σ 1 - σ 4) * Λ * rank (height C (dirP n)) i) • dirP n

/-- Clock values on the route: in phase `m` the earlier clocks are `1`, the later ones `0`. -/
def RouteClocks (σ : Fin 5 → ℝ) : Prop :=
  ∃ m : Fin 5, (∀ l, l < m → σ l = 1) ∧ (∀ l, m < l → σ l = 0) ∧ σ m ∈ Icc (0 : ℝ) 1

lemma routePos_zero (s C : Fin k → E n) (Λ : ℝ) (i : Fin k) :
    routePos s C Λ (fun _ => 0) i = s i := by
  simp [routePos]

lemma routePos_one (s C : Fin k → E n) (Λ : ℝ) (i : Fin k) :
    routePos s C Λ (fun _ => 1) i = C i := by
  simp [routePos]

lemma contDiff_routePos (s C : Fin k → E n) (Λ : ℝ) (i : Fin k) :
    ContDiff ℝ ∞ (fun σ : Fin 5 → ℝ => routePos s C Λ σ i) := by
  unfold routePos
  have hσ : ∀ l : Fin 5, ContDiff ℝ ∞ (fun σ : Fin 5 → ℝ => σ l) := fun l => contDiff_apply ℝ ℝ l
  refine ((contDiff_const.add ((hσ 2).smul contDiff_const)).add ?_).add ?_
  · exact ((((hσ 0).sub (hσ 3)).mul contDiff_const).mul contDiff_const).smul contDiff_const
  · exact ((((hσ 1).sub (hσ 4)).mul contDiff_const).mul contDiff_const).smul contDiff_const

/-- `‖v + x e‖ ≥ ‖v‖` when `x ⟪v, e⟫ ≥ 0`. -/
lemma norm_le_norm_add_smul {v e : E n} {x : ℝ} (h : 0 ≤ x * ⟪v, e⟫) : ‖v‖ ≤ ‖v + x • e‖ := by
  have hsq : ‖v‖ ^ 2 ≤ ‖v + x • e‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right]
    nlinarith [sq_nonneg ‖x • e‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- `Λ ≤ |δ + Λ m|` when `δ m ≥ 0` and `|m| ≥ 1`. -/
lemma le_abs_add_mul {δ m Λ : ℝ} (hδm : 0 ≤ δ * m) (hm : 1 ≤ |m|) (hΛ : 0 ≤ Λ) :
    Λ ≤ |δ + Λ * m| := by
  have hm2 : 1 ≤ m ^ 2 := by
    have := mul_le_mul hm hm zero_le_one (abs_nonneg m)
    rwa [one_mul, ← abs_mul, abs_mul_self, ← sq] at this
  have h2 : Λ ^ 2 ≤ (δ + Λ * m) ^ 2 := by nlinarith [sq_nonneg δ, mul_nonneg hΛ hδm]
  have := sq_le_sq.mp h2
  rwa [abs_of_nonneg hΛ] at this

/-- `|⟪w, e⟫| ≤ ‖w‖` for a unit vector `e`. -/
lemma abs_inner_le_norm_of_unit {w e : E n} (he : ‖e‖ = 1) : |⟪w, e⟫| ≤ ‖w‖ := by
  have := abs_real_inner_le_norm w e
  rwa [he, mul_one] at this

/-- **Route separation.** On the route, the balls `B̄(pᵢ, r₃ᵢ)` are pairwise disjoint. -/
theorem route_sep (hn : 0 < n) {s C : Fin k → E n} {r3 : Fin k → ℝ} (hr : ∀ i, 0 ≤ r3 i)
    (hs : ∀ i j, i ≠ j → r3 i + r3 j < dist (s i) (s j))
    (hC : ∀ i j, i ≠ j → r3 i + r3 j < dist (C i) (C j))
    {σ : Fin 5 → ℝ} (hσ : RouteClocks σ) {i j : Fin k} (hij : i ≠ j) :
    r3 i + r3 j < dist (routePos s C (routeConst s C r3) σ i)
      (routePos s C (routeConst s C r3) σ j) := by
  set Λ := routeConst s C r3
  set eQ := dirQ n
  set eP := dirP n
  have hQ : ‖eQ‖ = 1 := norm_dirQ hn
  have hP : ‖eP‖ = 1 := norm_dirP hn
  have hQP : ⟪eQ, eP⟫ = 0 := inner_dirQ_dirP
  have hPQ : ⟪eP, eQ⟫ = 0 := by rw [real_inner_comm]; exact hQP
  have hQQ : ⟪eQ, eQ⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hQ]; norm_num
  have hPP : ⟪eP, eP⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hP]; norm_num
  set m : ℝ := (rank (height s eQ) i : ℝ) - rank (height s eQ) j
  set m' : ℝ := (rank (height C eP) i : ℝ) - rank (height C eP) j
  set d := s i - s j
  set dC := C i - C j
  obtain ⟨hsm, hm1⟩ := rank_sign (height s eQ) hij
  obtain ⟨hCm, hm1'⟩ := rank_sign (height C eP) hij
  have hdQ : ⟪d, eQ⟫ = height s eQ i - height s eQ j := by
    simp only [d, height, inner_sub_left]
  have hdP : ⟪dC, eP⟫ = height C eP i - height C eP j := by
    simp only [dC, height, inner_sub_left]
  rw [← hdQ] at hsm
  rw [← hdP] at hCm
  -- the route constant
  have hΛ : r3 i + r3 j + ‖d‖ + ‖dC‖ < Λ := by
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun l => 2 * (r3 l + ‖s l‖ + ‖C l‖))
      (show ({i, j} : Finset (Fin k)) ⊆ univ from Finset.subset_univ _)
      (fun l _ _ => by have := hr l; positivity)
    rw [Finset.sum_pair hij] at hpair
    have h1 : ‖d‖ ≤ ‖s i‖ + ‖s j‖ := norm_sub_le _ _
    have h2 : ‖dC‖ ≤ ‖C i‖ + ‖C j‖ := norm_sub_le _ _
    have := hr i; have := hr j
    show r3 i + r3 j + ‖d‖ + ‖dC‖ < 1 + ∑ l, 2 * (r3 l + ‖s l‖ + ‖C l‖)
    linarith [norm_nonneg (s i), norm_nonneg (s j), norm_nonneg (C i), norm_nonneg (C j)]
  have hΛ0 : 0 ≤ Λ := by linarith [norm_nonneg d, norm_nonneg dC, hr i, hr j]
  have hsd : r3 i + r3 j < ‖d‖ := by rw [← dist_eq_norm]; exact hs i j hij
  have hCd : r3 i + r3 j < ‖dC‖ := by rw [← dist_eq_norm]; exact hC i j hij
  -- the difference of positions
  have hdiff : routePos s C Λ σ i - routePos s C Λ σ j =
      d + σ 2 • (dC - d) + ((σ 0 - σ 3) * Λ * m) • eQ + ((σ 1 - σ 4) * Λ * m') • eP := by
    simp only [routePos, d, dC, m, m', eQ, eP]
    module
  rw [dist_eq_norm, hdiff]
  obtain ⟨l, hlt, hgt, hl⟩ := hσ
  have key : ∀ (w : E n) (e : E n), ‖e‖ = 1 → |⟪w, e⟫| ≤ ‖w‖ := fun w e he =>
    abs_inner_le_norm_of_unit he
  have hl5 : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by fin_cases l <;> simp
  rcases hl5 with rfl | rfl | rfl | rfl | rfl
  · -- phase 0: rise in `q₁`
    have e1 := hgt 1 (by decide); have e2 := hgt 2 (by decide)
    have e3 := hgt 3 (by decide); have e4 := hgt 4 (by decide)
    simp only [e1, e2, e3, e4, zero_smul, add_zero, sub_zero, zero_mul]
    refine hsd.trans_le (norm_le_norm_add_smul ?_)
    have := mul_nonneg (mul_nonneg hl.1 hΛ0) hsm
    nlinarith
  · -- phase 1: rise in `p₁`
    have e0 := hlt 0 (by decide); have e2 := hgt 2 (by decide)
    have e3 := hgt 3 (by decide); have e4 := hgt 4 (by decide)
    simp only [e0, e2, e3, e4, zero_smul, add_zero, sub_zero, one_mul]
    have hin : ⟪d + (Λ * m) • eQ + ((σ 1) * Λ * m') • eP, eQ⟫ = ⟪d, eQ⟫ + Λ * m := by
      simp only [inner_add_left, real_inner_smul_left, hQQ, hPQ]; ring
    have h1 := le_abs_add_mul (Λ := Λ) hsm hm1 hΛ0
    have h2 := key (d + (Λ * m) • eQ + ((σ 1) * Λ * m') • eP) eQ hQ
    rw [hin] at h2
    linarith [norm_nonneg d, norm_nonneg dC]
  · -- phase 2: straight move
    have e0 := hlt 0 (by decide); have e1 := hlt 1 (by decide)
    have e3 := hgt 3 (by decide); have e4 := hgt 4 (by decide)
    simp only [e0, e1, e3, e4, sub_zero, one_mul]
    set w := d + σ 2 • (dC - d)
    have hw : ‖w‖ ≤ ‖d‖ + ‖dC‖ := by
      have : w = (1 - σ 2) • d + σ 2 • dC := by simp only [w]; module
      rw [this]
      have h0 : 0 ≤ 1 - σ 2 := by linarith [hl.2]
      calc ‖(1 - σ 2) • d + σ 2 • dC‖ ≤ (1 - σ 2) * ‖d‖ + σ 2 * ‖dC‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg hl.1]
        _ ≤ ‖d‖ + ‖dC‖ := by nlinarith [norm_nonneg d, norm_nonneg dC, hl.1, hl.2]
    have hin : ⟪w + (Λ * m) • eQ + (Λ * m') • eP, eQ⟫ = ⟪w, eQ⟫ + Λ * m := by
      simp only [inner_add_left, real_inner_smul_left, hQQ, hPQ]; ring
    have h1 : Λ ≤ |Λ * m| := by
      rw [abs_mul, abs_of_nonneg hΛ0]; nlinarith
    have h3 := key w eQ hQ
    have h2 := key (w + (Λ * m) • eQ + (Λ * m') • eP) eQ hQ
    rw [hin] at h2
    have h4 : |Λ * m| ≤ |⟪w, eQ⟫ + Λ * m| + |⟪w, eQ⟫| := by
      have := abs_sub (⟪w, eQ⟫ + Λ * m) ⟪w, eQ⟫
      simp only [add_sub_cancel_left] at this
      linarith
    linarith
  · -- phase 3: remove the `q₁`-offset
    have e0 := hlt 0 (by decide); have e1 := hlt 1 (by decide)
    have e2 := hlt 2 (by decide); have e4 := hgt 4 (by decide)
    simp only [e0, e1, e2, e4, sub_zero, one_smul, add_sub_cancel, one_mul]
    have hin : ⟪dC + ((1 - σ 3) * Λ * m) • eQ + (Λ * m') • eP, eP⟫ = ⟪dC, eP⟫ + Λ * m' := by
      simp only [inner_add_left, real_inner_smul_left, hPP, hQP]; ring
    have h1 := le_abs_add_mul (Λ := Λ) hCm hm1' hΛ0
    have h2 := key (dC + ((1 - σ 3) * Λ * m) • eQ + (Λ * m') • eP) eP hP
    rw [hin] at h2
    linarith [norm_nonneg d, norm_nonneg dC]
  · -- phase 4: remove the `p₁`-offset
    have e0 := hlt 0 (by decide); have e1 := hlt 1 (by decide)
    have e2 := hlt 2 (by decide); have e3 := hlt 3 (by decide)
    simp only [e0, e1, e2, e3, sub_self, one_smul, add_sub_cancel, zero_mul, zero_smul, add_zero]
    refine hCd.trans_le (norm_le_norm_add_smul ?_)
    have h0 : 0 ≤ 1 - σ 4 := by linarith [hl.2]
    have := mul_nonneg (mul_nonneg h0 hΛ0) hCm
    nlinarith

end SymplecticPacking.General.Ham.Isotopy
