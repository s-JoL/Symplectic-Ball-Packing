import SymplecticPacking.Handle.HandleDeck

/-!
# Periodisation in `u` over the cover

`sec:shd-four` (`cons:shd4-moser`): periodisation in `u` of families of one-forms supported over
the single strip `u ∈ [u₀, u₁]` of the cover (`StripSupp`), applied to the strip primitives
`η_λ`, `ξ` of the handle.

The lift of such a family `E` to the whole cover is `perJ E = E ∘ Ush(−⌊u⌋)`,
`Ush k = Tu^k : (w, u, v) ↦ ((−1)^k w, u + k, v)`.
* `perJ_smooth`: the periodisation of a jointly smooth family supported over the strip is
  jointly smooth;
* `perJ_TuE`, `perJ_TvE`: invariance under `Tu` and (if `E` is) `Tv`;
* `perJ_eq_on_strip`: `perJ E = E` on `{u₁ − 1 < u < 1 + u₀}` (so on the fundamental strip);
* `chartInv_TvE`: `chartInv ∘ Tv = (v + 1) ∘ chartInv`, from `frameA(u, v+1) = φ³ frameA`
  (`frameA_add_one_right`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap _root_.Complex ComplexConjugate
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE Zunit phaseV frameA u0 u1 annulus stepA bB bB_add_one)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

/-! ### The iterated `u`-deck map and the periodisation -/

/-- `Ush k = Tu^k : (w, u, v) ↦ ((−1)^k w, u + k, v)`. -/
def Ush (k : ℤ) (X : E4) : E4 := mk (((-1 : ℝ) ^ k) • wL X) (X 2 + k) (X 3)

lemma contDiff_Ush (k : ℤ) : ContDiff ℝ ∞ (Ush k) := by
  have : Ush k = fun X => mkL (((-1 : ℝ) ^ k) • wL X, dc 2 X + k, dc 3 X) := rfl
  rw [this]
  exact mkL.contDiff.comp (((contDiff_const (c := ((-1 : ℝ) ^ k))).smul wL.contDiff).prodMk
    (((dc 2).contDiff.add (contDiff_const (c := (k : ℝ)))).prodMk (dc 3).contDiff))

@[simp] lemma Ush_apply2 (k : ℤ) (X : E4) : Ush k X 2 = X 2 + k := by simp [Ush]
@[simp] lemma Ush_apply3 (k : ℤ) (X : E4) : Ush k X 3 = X 3 := by simp [Ush]
@[simp] lemma pE_Ush (k : ℤ) (X : E4) : pE (Ush k X) = pE X := by
  simp [Ush, pE_eq]

lemma Ush_zero (X : E4) : Ush 0 X = X := by simp [Ush]

/-- The periodisation in `u` of a family of one-forms. -/
def perJ (E : ℝ × E4 → (E4 →L[ℝ] ℝ)) (q : ℝ × E4) : E4 →L[ℝ] ℝ :=
  E (q.1, Ush (-⌊q.2 2⌋) q.2)

lemma floor_TuE (X : E4) : ⌊TuE X 2⌋ = ⌊X 2⌋ + 1 := by
  simp [TuE, Int.floor_add_one]

lemma Ush_TuE (X : E4) : Ush (-⌊TuE X 2⌋) (TuE X) = Ush (-⌊X 2⌋) X := by
  rw [floor_TuE]
  simp only [Ush, TuE, mk_apply2, mk_apply3, wL_mk]
  congr 1
  · rw [show -(⌊X 2⌋ + 1) = -⌊X 2⌋ - 1 by ring, zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [smul_neg, ← neg_smul]; congr 1; norm_num
  · push_cast; ring

lemma Ush_TvE (k : ℤ) (Y : E4) : Ush k (TvE Y) = TvE (Ush k Y) := by
  simp only [Ush, TvE, mk_apply2, mk_apply3, wL_mk, cV_add_int_left]
  rw [mul_smul_comm]

lemma floor_TvE (X : E4) : ⌊TvE X 2⌋ = ⌊X 2⌋ := by simp [TvE]

theorem perJ_TuE (E : ℝ × E4 → (E4 →L[ℝ] ℝ)) (s : ℝ) (X : E4) :
    perJ E (s, TuE X) = perJ E (s, X) := by
  simp only [perJ, Ush_TuE]

theorem perJ_TvE {E : ℝ × E4 → (E4 →L[ℝ] ℝ)} (hE : ∀ s Y, E (s, TvE Y) = E (s, Y)) (s : ℝ)
    (X : E4) : perJ E (s, TvE X) = perJ E (s, X) := by
  simp only [perJ, floor_TvE, Ush_TvE, hE]

lemma fract_eq_Ush (X : E4) : Ush (-⌊X 2⌋) X 2 = Int.fract (X 2) := by
  rw [Ush_apply2, Int.fract]; push_cast; ring

/-- Strip support: vanishing for `u ≤ u₀` or `u ≥ u₁`. -/
def StripSupp (E : ℝ × E4 → (E4 →L[ℝ] ℝ)) : Prop :=
  ∀ s Y, (Y 2 ≤ u0 ∨ u1 ≤ Y 2) → E (s, Y) = 0

lemma perJ_zero {E : ℝ × E4 → (E4 →L[ℝ] ℝ)} (hE : StripSupp E) {s : ℝ} {X : E4}
    (h : Int.fract (X 2) ≤ u0 ∨ u1 ≤ Int.fract (X 2)) : perJ E (s, X) = 0 := by
  simp only [perJ]
  exact hE _ _ (by rw [fract_eq_Ush]; exact h)

lemma u0_pos : (0 : ℝ) < u0 := by norm_num [u0]
lemma u1_lt_one : u1 < 1 := by norm_num [u1]
lemma u1_pos : (0 : ℝ) < u1 := by norm_num [u1]
lemma u0_lt_one : u0 < 1 := by norm_num [u0]
lemma u0_lt_u1' : u0 < u1 := by norm_num [u0, u1]

/-- On `{u₁ − 1 < u < 1 + u₀}` the periodisation is the original family. -/
theorem perJ_eq_on_strip {E : ℝ × E4 → (E4 →L[ℝ] ℝ)} (hE : StripSupp E) {s : ℝ} {X : E4}
    (h1 : u1 - 1 < X 2) (h2 : X 2 < 1 + u0) : perJ E (s, X) = E (s, X) := by
  have := u1_pos; have := u0_lt_one; have := u0_pos; have := u1_lt_one
  rcases lt_or_ge (X 2) 0 with h0 | h0
  · have hf : ⌊X 2⌋ = -1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [perJ_zero hE (Or.inr (by rw [Int.fract, hf]; push_cast; linarith)),
      hE _ _ (Or.inl (by linarith [u0_pos]))]
  rcases lt_or_ge (X 2) 1 with h3 | h3
  · have hf : ⌊X 2⌋ = 0 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    simp [perJ, hf, Ush_zero]
  · have hf : ⌊X 2⌋ = 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [perJ_zero hE (Or.inl (by rw [Int.fract, hf]; push_cast; linarith)),
      hE _ _ (Or.inr (by linarith [u1_lt_one]))]

/-- **Smoothness of the periodisation.** -/
theorem perJ_smooth {E : ℝ × E4 → (E4 →L[ℝ] ℝ)} (hs : ContDiff ℝ ∞ E) (hE : StripSupp E) :
    ContDiff ℝ ∞ (perJ E) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s, X⟩
  set n := ⌊X 2⌋
  by_cases hX : (n : ℝ) < X 2
  · -- locally `⌊u⌋ = n`
    have hO : {q : ℝ × E4 | (n : ℝ) < q.2 2 ∧ q.2 2 < n + 1} ∈ 𝓝 (s, X) :=
      ((isOpen_lt continuous_const ((dc 2).continuous.comp continuous_snd)).inter
        (isOpen_lt ((dc 2).continuous.comp continuous_snd) continuous_const)).mem_nhds
        ⟨hX, show X 2 < n + 1 from Int.lt_floor_add_one _⟩
    have hev : perJ E =ᶠ[𝓝 (s, X)] fun q => E (q.1, Ush (-n) q.2) := by
      filter_upwards [hO] with q hq
      have : ⌊q.2 2⌋ = n := by rw [Int.floor_eq_iff]; exact ⟨hq.1.le, hq.2⟩
      simp only [perJ, this]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (hs.comp (contDiff_fst.prodMk ((contDiff_Ush (-n)).comp contDiff_snd))).contDiffAt
  · -- `u = n` is an integer: the periodisation vanishes nearby
    have hXn : X 2 = n := le_antisymm (not_lt.mp hX) (Int.floor_le _)
    have hO : {q : ℝ × E4 | (n : ℝ) - 1 + u1 < q.2 2 ∧ q.2 2 < n + u0} ∈ 𝓝 (s, X) :=
      ((isOpen_lt continuous_const ((dc 2).continuous.comp continuous_snd)).inter
        (isOpen_lt ((dc 2).continuous.comp continuous_snd) continuous_const)).mem_nhds
        ⟨show (n : ℝ) - 1 + u1 < X 2 by rw [hXn]; linarith [u1_lt_one],
          show X 2 < n + u0 by rw [hXn]; linarith [u0_pos]⟩
    have hev : perJ E =ᶠ[𝓝 (s, X)] fun _ => 0 := by
      filter_upwards [hO] with q hq
      obtain ⟨q1, q2⟩ := q
      simp only at hq
      have := u1_pos; have := u0_lt_one
      rcases lt_or_ge (q2 2 : ℝ) (n : ℝ) with h | h
      · have hf : ⌊q2 2⌋ = n - 1 := by
          rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [u1_lt_one, hq.1]
        exact perJ_zero hE (Or.inr (by rw [Int.fract, hf]; push_cast; linarith [hq.1]))
      · have hf : ⌊q2 2⌋ = n := by
          rw [Int.floor_eq_iff]; constructor <;> linarith [u0_pos, hq.2, u0_lt_u1', u1_lt_one]
        exact perJ_zero hE (Or.inl (by rw [Int.fract, hf]; linarith [hq.2]))
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-! ### `Tv`-invariance of the strip primitives -/

lemma frameA_add_one_right (u v : ℝ) : frameA u (v + 1) = cV u v * frameA u v := by
  simp only [frameA, Bundle.Zunit_add_one_right, Pi.smul_apply, smul_eq_mul, norm_mul,
    Bundle.norm_phaseV, one_mul, cV_eq]
  ring

lemma chartInv_TvE (Y : E4) : chartInv (TvE Y) = mk (wL (chartInv Y)) (Y 2) (Y 3 + 1) := by
  simp only [chartInv, TvE, mk_apply2, mk_apply3, wL_mk, frameA_add_one_right, map_mul]
  congr 1
  have := conj_mul_cV (Y 2) (Y 3)
  linear_combination (conj (frameA (Y 2) (Y 3)) * wL Y) * this

end SymplecticPacking.Handle
