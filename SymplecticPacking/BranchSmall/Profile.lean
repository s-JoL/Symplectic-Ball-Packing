import SymplecticPacking.BranchSmall.Params
import SymplecticPacking.HighDim.Comparator.Datum

/-!
# Profile and comparator input of the quadric model (paper def:qdr-model, lem:qdr-volume)

Fibre rank `m + 2 = n − 1` (`n = m + 3`), polytope `Δ_h = {p ≥ 0, |p| ≤ h}`, base area
profile `H_b(p) = 2^{m+2}(1 − 2|p|)` and comparison profile
`P = H_b − Σ_i (a_i − |p|)_+` (the OpenAI library's `smallModelGap`).
`∫_{Δ_h} H_b = J_{m+2}(h)` (`smallModelMean`), `J(1/2) = 1/n!`,
`1/n! − J(h) ≤ 2δ²/(n−2)!` for `h = 1/2 − δ`, hence `∫ P > 7σ/(8 n!)`.
`−P` is given as data (`negPData`) for the finite comparator.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set MeasureTheory
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (smallModelGap smallModelMean momentSimplex)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)

variable {k : ℕ}

/-- The comparator input for `n = m + 3`. -/
def cmpInput (m : ℕ) (ρ : Fin k → ℝ) : CmpInput (m + 2) 1 where
  Δ := Polytope.simplex (m + 2) (hgt (m + 3) ρ)
  P := smallModelGap (capA (m + 3) ρ)
  τ := tau (m + 3) ρ
  β := beta (m + 3) ρ
  d := dgap (m + 3) ρ

/-- `−P` as a maximum of affine functions: `−H_b + Σ_i max(0, a_i − |p|)`, expanded as
pairwise sums. -/
def negPData (m : ℕ) (ρ : Fin k → ℝ) : PolyFn (m + 2) :=
  (List.finRange k).foldl
    (fun F i => PolyFn.add F [⟨0, 0⟩, ⟨fun _ => -1, capA (m + 3) ρ i⟩])
    [⟨fun _ => 2 ^ (m + 3), -2 ^ (m + 2)⟩]


/-- The two pieces of `max(0, a − |p|)`. -/
def capPair (m : ℕ) (a : ℝ) : PolyFn (m + 2) := [⟨0, 0⟩, ⟨fun _ => -1, a⟩]

theorem capPair_ne_nil (m : ℕ) (a : ℝ) : capPair m a ≠ [] := List.cons_ne_nil _ _

theorem capPair_eval (m : ℕ) (a : ℝ) (p : Moments (m + 2)) :
    PolyFn.eval (capPair m a) p = max (a - ∑ j, p j) 0 := by
  simp only [capPair, PolyFn.eval, List.foldl_cons, List.foldl_nil, AffinePiece.eval,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul, Finset.sum_neg_distrib]
  rw [max_comm]
  ring_nf

theorem foldl_capPair (m : ℕ) (a : Fin k → ℝ) (l : List (Fin k)) {F : PolyFn (m + 2)}
    (hF : F ≠ []) (p : Moments (m + 2)) :
    l.foldl (fun F i => PolyFn.add F (capPair m (a i))) F ≠ [] ∧
    PolyFn.eval (l.foldl (fun F i => PolyFn.add F (capPair m (a i))) F) p =
      PolyFn.eval F p + (l.map fun i => max (a i - ∑ j, p j) 0).sum := by
  induction l generalizing F with
  | nil => exact ⟨hF, by simp⟩
  | cons i l ih =>
    have hF' := PolyFn.add_ne_nil hF (capPair_ne_nil m (a i))
    obtain ⟨h1, h2⟩ := ih hF'
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons] at h1 h2 ⊢
    rw [h2, PolyFn.eval_add hF (capPair_ne_nil m (a i)), capPair_eval, List.map_cons,
      List.sum_cons]
    ring

theorem negPData_ne_nil (m : ℕ) (ρ : Fin k → ℝ) : negPData m ρ ≠ [] :=
  (foldl_capPair m (capA (m + 3) ρ) (List.finRange k) (List.cons_ne_nil _ _) 0).1

theorem negPData_eval (m : ℕ) (ρ : Fin k → ℝ) (p : Moments (m + 2)) :
    (cmpInput m ρ).P p = -PolyFn.eval (negPData m ρ) p := by
  have h := (foldl_capPair m (capA (m + 3) ρ) (List.finRange k)
    (F := [⟨fun _ => 2 ^ (m + 3), -2 ^ (m + 2)⟩]) (List.cons_ne_nil _ _) p).2
  change smallModelGap (capA (m + 3) ρ) p = -PolyFn.eval (negPData m ρ) p
  unfold capPair at h
  unfold negPData
  rw [h, ← Fin.sum_univ_def]
  simp only [smallModelGap, PolyFn.eval, List.foldl_nil, AffinePiece.eval, ← Finset.mul_sum]
  ring

/-- `1 − (M+1)x^M + M x^{M+1} = (1−x)² Σ_{j<M} (j+1)x^j ≤ (1−x)² M(M+1)/2` on `[0,1]`. -/
theorem tail_poly (M : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (M + 1) * x ^ M + M * x ^ (M + 1) ≤ (1 - x) ^ 2 * (M * (M + 1) / 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hxM : x ^ M ≤ 1 := pow_le_one₀ hx0 hx1
    have hsq : 0 ≤ (1 - x) ^ 2 := sq_nonneg _
    have e : 1 - ((M + 1 : ℕ) + 1) * x ^ (M + 1) + ((M + 1 : ℕ) : ℝ) * x ^ (M + 1 + 1) =
        (1 - (M + 1) * x ^ M + M * x ^ (M + 1)) + (M + 1) * x ^ M * (1 - x) ^ 2 := by
      push_cast; ring
    rw [e]
    have : (M + 1) * x ^ M * (1 - x) ^ 2 ≤ (M + 1) * (1 - x) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hxM hsq
      nlinarith
    push_cast
    nlinarith

/-- lem:qdr-volume, tail estimate: `1/n! − J_{n−1}(h) ≤ 2δ²/(n−2)!` for `h = 1/2 − δ`. -/
theorem smallModelMean_tail (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    1 / ((m + 3).factorial : ℝ) - smallModelMean (m + 2) (1 / 2 - δ) ≤
      2 * δ ^ 2 / ((m + 1).factorial : ℝ) := by
  set x : ℝ := 1 - 2 * δ with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hF : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  set F : ℝ := ((m + 1).factorial : ℝ)
  have h2 : ((m + 2).factorial : ℝ) = (m + 2) * F := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have h3 : ((m + 3).factorial : ℝ) = (m + 3) * (m + 2) * F := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ]
    push_cast
    rw [h2]; ring
  have hx : (2 : ℝ) ^ (m + 2) * (1 / 2 - δ) ^ (m + 2) = x ^ (m + 2) := by
    rw [← mul_pow]; congr 1; rw [hxdef]; ring
  have key := tail_poly (m + 2) hx0 hx1
  push_cast at key
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have e1 : 1 / ((m + 3).factorial : ℝ) - smallModelMean (m + 2) (1 / 2 - δ) =
      (1 - ((m : ℝ) + 2 + 1) * x ^ (m + 2) + ((m : ℝ) + 2) * x ^ (m + 2 + 1)) /
        ((m + 3) * (m + 2) * F) := by
    unfold OAI.PackingSufficiencySupport.smallModelMean
    rw [h3, h2, hx]
    push_cast
    field_simp
    rw [hxdef]
    ring
  have e2 : 2 * δ ^ 2 / F =
      ((1 - x) ^ 2 * (((m : ℝ) + 2) * ((m : ℝ) + 2 + 1) / 2)) / ((m + 3) * (m + 2) * F) := by
    rw [hxdef]
    field_simp
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key (by positivity)

theorem momentSimplex_subset_cube (m : ℕ) {h : ℝ} (hh1 : h ≤ 1) :
    momentSimplex m h ⊆ Icc (0 : Fin m → ℝ) 1 := by
  intro p hp
  refine ⟨fun j => hp.1 j, fun j => ?_⟩
  have : p j ≤ ∑ i, p i :=
    Finset.single_le_sum (fun i _ => hp.1 i) (Finset.mem_univ j)
  simp only [Pi.one_apply]
  linarith [hp.2]

theorem simplex_volume_le_one (m : ℕ) {h : ℝ} (hh1 : h ≤ 1) :
    (volume (momentSimplex m h)).toReal ≤ 1 := by
  have hc : volume (Icc (0 : Fin m → ℝ) 1) = 1 := by
    rw [Real.volume_Icc_pi]; simp
  have := measure_mono (μ := volume) (momentSimplex_subset_cube m hh1)
  rw [hc] at this
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

theorem simplex_volume_pos (m : ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < (volume (momentSimplex m h)).toReal := by
  set s : ℝ := h / (m + 1)
  have hs : 0 < s := div_pos hh (by positivity)
  have hsub : Icc (0 : Fin m → ℝ) (fun _ => s) ⊆ momentSimplex m h := by
    intro p hp
    refine ⟨fun j => hp.1 j, ?_⟩
    calc ∑ i, p i ≤ ∑ _i : Fin m, s := Finset.sum_le_sum fun i _ => hp.2 i
      _ = m * s := by simp
      _ ≤ h := by
        simp only [s]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  have hfin : volume (momentSimplex m h) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (momentSimplex_subset_cube m hh1))
    rw [Real.volume_Icc_pi]; simp
  have hpos : 0 < volume (Icc (0 : Fin m → ℝ) (fun _ => s)) := by
    rw [Real.volume_Icc_pi]
    refine pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    simpa using hs
  exact ENNReal.toReal_pos (lt_of_lt_of_le hpos (measure_mono hsub)).ne' hfin

/-- `∫_{Δ_h} P ≥ 7σ/(8 n!)`, hence `d < mean P` (lem:qdr-volume). -/
theorem dgap_lt_mean {m : ℕ} {ρ : Fin k → ℝ} (H : Hyp (m + 3) ρ) :
    (cmpInput m ρ).d < (cmpInput m ρ).mean := by
  have hh := hgt_pos H
  have hh1 : hgt (m + 3) ρ ≤ 1 := by linarith [hgt_lt_half H]
  have hvol := simplex_volume_pos (m + 2) hh hh1
  have hvol1 := simplex_volume_le_one (m + 2) hh1
  have hd := dgap_pos H
  have hσ := sigma_pos H
  have hδ := delta_pos H
  have hfac : (0 : ℝ) < (m + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  -- the integral
  have hint : ∫ p in momentSimplex (m + 2) (hgt (m + 3) ρ), smallModelGap (capA (m + 3) ρ) p =
      smallModelMean (m + 2) (hgt (m + 3) ρ) -
        (∑ i, capA (m + 3) ρ i ^ (m + 3)) / ((m + 3).factorial : ℝ) :=
    OAI.PackingSufficiencySupport.integral_smallModelGap _ (fun i => (capA_pos H i).le) hh.le
      (fun i => (le_aMax H i).trans (aMax_lt_hgt H).le)
  have hhd : hgt (m + 3) ρ = 1 / 2 - dlt (m + 3) ρ := rfl
  have htail := smallModelMean_tail m hδ.le (by linarith [hgt_pos H])
  have hδσ : dlt (m + 3) ρ ≤ sigma (m + 3) ρ / (4 * (m + 3 : ℕ) * ((m + 3 : ℕ) - 1)) :=
    min_le_right _ _
  have hδq : dlt (m + 3) ρ < 1 / 4 := by
    have : dlt (m + 3) ρ ≤ (1 / 2 - aMax (m + 3) ρ) / 2 := min_le_left _ _
    linarith [aMax_pos H]
  -- 2δ²/(n-2)! ≤ σ/(8 n!)
  have hsmall : 2 * dlt (m + 3) ρ ^ 2 / ((m + 1).factorial : ℝ) ≤
      sigma (m + 3) ρ / (8 * (m + 3).factorial) := by
    have e : ((m + 3).factorial : ℝ) = (m + 3) * (m + 2) * (m + 1).factorial := by
      rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hf1 : (0 : ℝ) < (m + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [e, div_le_div_iff₀ hf1 (by positivity)]
    have h1 : dlt (m + 3) ρ * (4 * ((m : ℝ) + 3) * ((m : ℝ) + 2)) ≤ sigma (m + 3) ρ := by
      have := hδσ
      have hm : (0 : ℝ) ≤ m := m.cast_nonneg
      push_cast at this
      rw [le_div_iff₀ (by nlinarith)] at this
      nlinarith
    have h2 : 2 * dlt (m + 3) ρ ^ 2 * (8 * (((m : ℝ) + 3) * ((m : ℝ) + 2))) ≤
        sigma (m + 3) ρ := by nlinarith
    nlinarith
  have hsum : ∑ i, capA (m + 3) ρ i ^ (m + 3) = 1 - sigma (m + 3) ρ := by
    simp [sigma]
  have hJ := htail
  rw [show 1 / 2 - dlt (m + 3) ρ = hgt (m + 3) ρ from rfl] at hJ
  have hint_lb : 7 * sigma (m + 3) ρ / (8 * (m + 3).factorial) ≤
      ∫ p in momentSimplex (m + 2) (hgt (m + 3) ρ), smallModelGap (capA (m + 3) ρ) p := by
    rw [hint, hsum]
    have : (1 - sigma (m + 3) ρ) / ((m + 3).factorial : ℝ) =
        1 / (m + 3).factorial - sigma (m + 3) ρ / (m + 3).factorial := by ring
    rw [this]
    have : 7 * sigma (m + 3) ρ / (8 * (m + 3).factorial) =
        sigma (m + 3) ρ / (m + 3).factorial - sigma (m + 3) ρ / (8 * (m + 3).factorial) := by
      field_simp; ring
    rw [this]
    linarith
  have hdle := dgap_le H
  change dgap (m + 3) ρ < (∫ p in (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set,
      smallModelGap (capA (m + 3) ρ) p) /
    (volume (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set).toReal
  rw [Polytope.simplex_set, lt_div_iff₀ hvol]
  have h7 : sigma (m + 3) ρ / (4 * (m + 3).factorial) <
      7 * sigma (m + 3) ρ / (8 * (m + 3).factorial) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc dgap (m + 3) ρ * (volume (momentSimplex (m + 2) (hgt (m + 3) ρ))).toReal
      ≤ dgap (m + 3) ρ * 1 := mul_le_mul_of_nonneg_left hvol1 hd.le
    _ < _ := by linarith

theorem cmpInput_spec {m : ℕ} {ρ : Fin k → ℝ} (H : Hyp (m + 3) ρ) : (cmpInput m ρ).Spec := by
  have hh := hgt_pos H
  refine ⟨Polytope.simplex_spec hh, ?_, ?_, ?_, tau_pos H, tau_lt_one H, ?_, dgap_pos H, ?_,
    dgap_lt_beta H⟩
  · exact (OAI.PackingSufficiencySupport.continuous_smallModelGap _).continuousOn
  · change ConcaveOn ℝ (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set
      (smallModelGap (capA (m + 3) ρ))
    rw [OAI.PackingSufficiencySupport.smallModelGap_eq_cappedAffine]
    exact OAI.PackingSufficiencySupport.concaveOn_cappedAffine _ _ _ _ (fun _ => by norm_num)
      (Polytope.convex_set _)
  · change 0 < (volume (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set).toReal
    rw [Polytope.simplex_set]
    exact simplex_volume_pos _ hh (by linarith [hgt_lt_half H])
  · intro p hp hout
    change p ∈ (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set at hp
    rw [Polytope.simplex_set] at hp
    have hs : tau (m + 3) ρ * hgt (m + 3) ρ < ∑ j, p j := by
      by_contra hle
      push Not at hle
      exact hout ⟨hp.1, fun _ => by simpa [cmpInput, Polytope.dilate, Polytope.simplex] using hle⟩
    have hzero (i : Fin k) : max (capA (m + 3) ρ i - ∑ j, p j) 0 = 0 :=
      max_eq_right (by linarith [capA_le_tau_hgt H i])
    change beta (m + 3) ρ ≤ smallModelGap (capA (m + 3) ρ) p
    simp only [smallModelGap, hzero, Finset.sum_const_zero, sub_zero, beta]
    have h2 := hp.2
    have : (m + 3 - 1 : ℕ) = m + 2 := rfl
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact dgap_lt_mean H

end SymplecticPacking.BranchSmall
