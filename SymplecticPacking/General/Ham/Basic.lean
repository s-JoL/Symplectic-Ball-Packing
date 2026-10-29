import SymplecticPacking.General.Ham.Defs

/-!
# Basic properties of the pushforward, the radial cutoff and `ofIsotopy`
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Problem
open scoped ContDiff

variable {n : ℕ}

/-! ### The radial cutoff -/

lemma radialCutoff_eq_one {ron roff : ℝ} (h : ron < roff) (h0 : 0 ≤ ron) {u : E n}
    (hu : ‖u‖ ≤ ron) : radialCutoff ron roff u = 1 := by
  simp only [radialCutoff]
  have hden : 0 < roff ^ 2 - ron ^ 2 := by nlinarith
  have : (‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg u]) hden.le
  rw [Real.smoothTransition.zero_of_nonpos this, sub_zero]

lemma radialCutoff_eq_zero {ron roff : ℝ} (h : ron < roff) (h0 : 0 ≤ ron) {u : E n}
    (hu : roff ≤ ‖u‖) : radialCutoff ron roff u = 0 := by
  simp only [radialCutoff]
  have hden : 0 < roff ^ 2 - ron ^ 2 := by nlinarith
  have hsq : roff ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by linarith) hu 2
  have : 1 ≤ (‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2) := by
    rw [le_div_iff₀ hden]; linarith
  rw [Real.smoothTransition.one_of_one_le this, sub_self]

lemma radialCutoff_contDiff {ron roff : ℝ} :
    ContDiff ℝ ∞ (radialCutoff (n := n) ron roff) := by
  rw [show radialCutoff ron roff = fun u =>
    1 - Real.smoothTransition ((‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2)) from rfl]
  apply contDiff_const.sub
  apply Real.smoothTransition.contDiff.comp
  apply ContDiff.div_const
  apply ContDiff.sub _ contDiff_const
  exact (contDiff_norm_sq ℝ)

/-! ### The pushforward -/

/-- On the image: `push(F u) = g u` when `F t` is injective on `B̄(r)` and `u ∈ B̄(r)`. -/
theorem pushforward_apply_image {F : ℝ → E n → E n} {r : ℝ} {g : ℝ → E n → ℝ} {t : ℝ} {u : E n}
    (hinj : InjOn (F t) (closedBall 0 r)) (hu : u ∈ closedBall (0 : E n) r) :
    pushforward F r g t (F t u) = g t u := by
  have hex : ∃! v, v ∈ closedBall (0 : E n) r ∧ F t v = F t u :=
    ⟨u, ⟨hu, rfl⟩, fun v hv => hinj hv.1 hu hv.2⟩
  unfold pushforward
  rw [dif_pos hex]
  congr 1
  exact Explicit.the_eq hex ⟨hu, rfl⟩

/-- Off the image the pushforward vanishes. -/
theorem pushforward_eq_zero_of_notMem {F : ℝ → E n → E n} {r : ℝ} {g : ℝ → E n → ℝ} {t : ℝ}
    {y : E n} (hy : y ∉ F t '' closedBall 0 r) : pushforward F r g t y = 0 := by
  unfold pushforward
  rw [dif_neg]
  rintro ⟨u, ⟨hu, rfl⟩, -⟩
  exact hy ⟨u, hu, rfl⟩

/-- The pushforward vanishes at `y` whenever `g t` vanishes at every preimage of `y` in `B̄(r)`. -/
theorem pushforward_eq_zero {F : ℝ → E n → E n} {r : ℝ} {g : ℝ → E n → ℝ} {t : ℝ} {y : E n}
    (hg : ∀ u ∈ closedBall (0 : E n) r, F t u = y → g t u = 0) : pushforward F r g t y = 0 := by
  unfold pushforward
  split_ifs with h
  · exact hg _ (Explicit.the_spec h).1 (Explicit.the_spec h).2
  · rfl

/-! ### The global Hamiltonian on one image -/

/-- **(25) on the `i`-th image.** If the images `F j t '' B̄(r₃)` are pairwise disjoint and each
`F j t` is injective on `B̄(r₃)`, then on the `i`-th image `H` equals the `i`-th source function. -/
theorem ofIsotopy_apply_image {k : ℕ} {F : Fin k → ℝ → E n → E n} {r1 r2 r3 : Fin k → ℝ}
    {t : ℝ} {i : Fin k}
    {u : E n} (hinj : ∀ j, InjOn (F j t) (closedBall 0 (r3 j)))
    (hdisj : ∀ j, j ≠ i →
      Disjoint (F j t '' closedBall 0 (r3 j)) (F i t '' closedBall 0 (r3 i)))
    (hu : u ∈ closedBall (0 : E n) (r3 i)) :
    ofIsotopy F r1 r2 r3 t (F i t u) =
      radialCutoff (r1 i) (r2 i) u * sourcePrimitive (F i) t u := by
  unfold ofIsotopy
  rw [Finset.sum_eq_single i]
  · exact pushforward_apply_image (hinj i) hu
  · intro j _ hji
    apply pushforward_eq_zero_of_notMem
    intro hmem
    exact Set.disjoint_left.mp (hdisj j hji) hmem ⟨u, hu, rfl⟩
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Outside all images `H` vanishes. -/
theorem ofIsotopy_eq_zero {k : ℕ} {F : Fin k → ℝ → E n → E n} {r1 r2 r3 : Fin k → ℝ} {t : ℝ}
    {y : E n} (hy : ∀ j, y ∉ F j t '' closedBall 0 (r3 j)) : ofIsotopy F r1 r2 r3 t y = 0 := by
  unfold ofIsotopy
  exact Finset.sum_eq_zero fun j _ => pushforward_eq_zero_of_notMem (hy j)

end SymplecticPacking.General.Ham

namespace SymplecticPacking.General.Ham

open Metric Set Problem

variable {n : ℕ}

/-- **Compact support (`sec:ham-hamiltonian`).** If all images `F j t '' B̄(r₃)` lie in `B̄(S)`, then `H(t, ·)`
vanishes outside `B̄(S)` for every `t`. -/
theorem ofIsotopy_support {k : ℕ} {F : Fin k → ℝ → E n → E n} {r1 r2 r3 : Fin k → ℝ} {S : ℝ}
    (hS : ∀ j t, ∀ u ∈ closedBall (0 : E n) (r3 j), ‖F j t u‖ ≤ S) :
    ∀ t, ∀ y ∉ closedBall (0 : E n) S, ofIsotopy F r1 r2 r3 t y = 0 := by
  intro t y hy
  apply ofIsotopy_eq_zero
  rintro j ⟨u, hu, rfl⟩
  exact hy (mem_closedBall_zero_iff.mpr (hS j t u hu))

/-- Compact support in the form used by `PackingSpec`. -/
theorem ofIsotopy_compactSupport {k : ℕ} {F : Fin k → ℝ → E n → E n} {r1 r2 r3 : Fin k → ℝ}
    (hb : ∃ S, ∀ j t, ∀ u ∈ closedBall (0 : E n) (r3 j), ‖F j t u‖ ≤ S) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ t, ∀ y ∉ K, ofIsotopy F r1 r2 r3 t y = 0 := by
  obtain ⟨S, hS⟩ := hb
  exact ⟨closedBall 0 S, isCompact_closedBall 0 S, ofIsotopy_support hS⟩

end SymplecticPacking.General.Ham
