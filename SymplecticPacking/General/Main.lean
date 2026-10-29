import SymplecticPacking.HamEnd.End
import SymplecticPacking.Branch2.Embeddings
import SymplecticPacking.BranchSmall.Embeddings
import SymplecticPacking.BranchLargeHigh.Embeddings
import SymplecticPacking.BranchLarge3.Embeddings

/-!
# The general construction and the main theorem

`packingHamiltonian n k C c s` selects the geometric branch by the dimension and by whether some
ball has capacity at least `C/2` (a case distinction on propositions, allowed at level L1), and
passes the branch's explicit embeddings to the Hamiltonian end:

* `n = 2`                         → `Branch2`          (all `3 c_i < C`);
* `n ≥ 3`, all `2 c_i < C`        → `BranchSmall`;
* `n = 3`, some `2 c_j ≥ C`       → `BranchLarge3`;
* `n ≥ 4`, some `2 c_j ≥ C`       → `BranchLargeHigh`.

`packing_main` is proved from the four branch specifications and the Hamiltonian end.
`epoch_general` derives the Epoch statement (`n = 2`, `k ≥ 9` unit balls at `(3i,0,0,0)`;
Epoch's `k ≥ 10` is a special case) from `packing_main`.
-/

noncomputable section

namespace SymplecticPacking.General

open Metric Set Problem
open scoped ContDiff

/-- Branch selection: the explicit embeddings for the input `(n, k, C, c)`. -/
def selectEmbeddings (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData n k :=
  open Classical in
  if n = 2 then Branch2.embeddings n k C c
  else if ∃ j, C ≤ 2 * c j then
    (if n = 3 then BranchLarge3.embeddings n k C c else BranchLargeHigh.embeddings n k C c)
  else BranchSmall.embeddings n k C c

/-- **The explicit Hamiltonian** `H[n, k, C, c, s]`. -/
def packingHamiltonian (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n) :
    ℝ → E n → ℝ :=
  HamEnd.hamiltonianOfEmbeddings n k c s (selectEmbeddings n k C c)

theorem selectEmbeddings_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} (hA : Admissible n k C c) :
    EmbeddingSpec n k C c (selectEmbeddings n k C c) := by
  have h2 := hA.two_le
  unfold selectEmbeddings
  split_ifs with hn hlarge hn3
  · subst hn
    exact Branch2.embeddings_spec rfl hA.one_le hA.C_pos hA.c_pos (hA.dim_two rfl) hA.volume
  · exact BranchLarge3.embeddings_spec hn3 hA.one_le hA.C_pos hA.c_pos (hA.pair (by omega))
      hA.volume hlarge
  · exact BranchLargeHigh.embeddings_spec (by omega) hA.one_le hA.C_pos hA.c_pos
      (hA.pair (by omega)) hA.volume hlarge
  · push Not at hlarge
    exact BranchSmall.embeddings_spec (by omega) hA.one_le hA.C_pos hA.c_pos hlarge hA.volume

/-- **Main theorem.** For admissible input with pairwise disjoint closed source balls, the
explicit Hamiltonian `packingHamiltonian n k C c s` satisfies the packing specification. -/
theorem packing_main {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    PackingSpec n k C c s (packingHamiltonian n k C c s) :=
  HamEnd.hamiltonian_end (by have := hA.two_le; omega) hA.c_pos hs (selectEmbeddings_spec hA)

/-! ### The Epoch corollary -/

/-- `R⁴ = m := k / (1 - ε/2)`, so that `k / R⁴ = 1 - ε/2 > 1 - ε`. -/
def epochR4 (k : ℕ) (ε : ℝ) : ℝ := k / (1 - ε / 2)

/-- The target radius `R = m^{1/4}`. -/
def epochRadius (k : ℕ) (ε : ℝ) : ℝ := epochR4 k ε ^ (1 / 4 : ℝ)

/-- The Epoch input: `k` balls of capacity `π` (unit radius) at `(3i, 0, 0, 0)`, target
capacity `C = π R²`. -/
def epochHamiltonian (k : ℕ) (ε : ℝ) : ℝ → E 2 → ℝ :=
  packingHamiltonian 2 k (Real.pi * epochRadius k ε ^ 2) (fun _ => Real.pi)
    (fun i => epochCenter i)

lemma epochR4_bounds {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (k : ℝ) < epochR4 k ε ∧ (k : ℝ) / epochR4 k ε = 1 - ε / 2 := by
  have hk' : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 1 - ε / 2 := by linarith
  unfold epochR4
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · field_simp

lemma epochRadius_pow_four {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    epochRadius k ε ^ 4 = epochR4 k ε := by
  have hm : 0 ≤ epochR4 k ε := by
    have := (epochR4_bounds hk h0 h1).1; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  unfold epochRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul hm]
  norm_num

lemma epochRadius_pos {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 < epochRadius k ε := by
  have := (epochR4_bounds hk h0 h1).1
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact Real.rpow_pos_of_pos (by linarith) _

lemma mem_capBall_pi_iff {n : ℕ} {s x : E n} : x ∈ capBall s Real.pi ↔ x ∈ closedBall s 1 := by
  simp only [capBall, mem_ofPred_eq, mem_closedBall, dist_eq_norm]
  constructor
  · intro h
    have h' : ‖x - s‖ ^ 2 ≤ 1 := by
      have := Real.pi_pos; nlinarith
    nlinarith [norm_nonneg (x - s)]
  · intro h
    have : ‖x - s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - s)]
    have := Real.pi_pos; nlinarith

lemma epoch_admissible {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Admissible 2 k (Real.pi * epochRadius k ε ^ 2) (fun _ => Real.pi) := by
  have hR4 := epochRadius_pow_four hk h0 h1
  have hb := epochR4_bounds hk h0 h1
  have hk' : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have hR := epochRadius_pos hk h0 h1
  have hR2 : 3 < epochRadius k ε ^ 2 := by
    by_contra hcon; push Not at hcon
    have : epochRadius k ε ^ 4 ≤ 9 := by
      have h0' : 0 ≤ epochRadius k ε ^ 2 := by positivity
      calc epochRadius k ε ^ 4 = (epochRadius k ε ^ 2) ^ 2 := by ring
        _ ≤ 3 ^ 2 := by gcongr
        _ = 9 := by norm_num
    linarith
  refine ⟨le_rfl, by omega, by positivity, fun _ => hpi, ?_, fun _ _ => by nlinarith,
    fun h => by omega⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (k : ℝ) * Real.pi ^ 2 < epochR4 k ε * Real.pi ^ 2 := by gcongr; exact hb.1
    _ = (Real.pi * epochRadius k ε ^ 2) ^ 2 := by rw [← hR4]; ring

lemma epochCenter_dist {i j : ℕ} (hij : i ≠ j) : 3 ≤ ‖epochCenter i - epochCenter j‖ := by
  unfold epochCenter
  rw [← PiLp.single_sub, PiLp.norm_single, ← mul_sub, norm_mul]
  have : (1 : ℝ) ≤ ‖(i : ℝ) - j‖ := by
    rw [Real.norm_eq_abs]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have h3 : ‖(3 : ℝ)‖ = 3 := by norm_num
  rw [h3]; linarith

lemma epoch_disjoint (k : ℕ) :
    BallsDisjoint 2 k (fun _ => Real.pi) (fun i => epochCenter i) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [mem_capBall_pi_iff, mem_closedBall, dist_eq_norm] at hxi hxj
  have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h3 := epochCenter_dist hne
  have : ‖epochCenter i - epochCenter j‖ ≤ ‖x - epochCenter j‖ + ‖x - epochCenter i‖ := by
    calc ‖epochCenter i - epochCenter j‖ = ‖(x - epochCenter j) - (x - epochCenter i)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- **Epoch corollary.** For `k ≥ 9` (Epoch's `k ≥ 10` is a special case) and `0 < ε < 1`,
`epochHamiltonian k ε` moves the `k` closed unit balls at `(3i,0,0,0)` into the closed ball `B(R)`, `R = epochRadius k ε`, with
`k / R⁴ = 1 - ε/2 > 1 - ε`. Derived from `packing_main` with `c_i = π`, `C = πR²`
(`R⁴ = k/(1-ε/2) > 9`, so `3π < C`). -/
theorem epoch_general (k : ℕ) (hk : 9 ≤ k) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    Problem.EpochSpecR k ε (epochRadius k ε) (epochHamiltonian k ε) := by
  have hP := packing_main (epoch_admissible hk h0 h1) (epoch_disjoint k)
  have hR := epochRadius_pos hk h0 h1
  have hb := epochR4_bounds hk h0 h1
  refine ⟨hP.smooth, hP.compactSupport, hR, ?_, ?_, ?_⟩
  · rw [epochRadius_pow_four hk h0 h1, hb.2]; linarith
  · intro i hi x hx
    exact hP.exists_curve ⟨i, hi⟩ x (mem_capBall_pi_iff.2 hx)
  · intro i hi x hx γ hγ0 hγ
    have h := hP.maps_into ⟨i, hi⟩ x (mem_capBall_pi_iff.2 hx) γ hγ0 hγ
    simp only [capBallOpen, mem_ofPred_eq, sub_zero] at h
    rw [mem_closedBall_zero_iff]
    have : ‖γ 1‖ ^ 2 < epochRadius k ε ^ 2 := by
      have := Real.pi_pos
      exact lt_of_mul_lt_mul_left h this.le
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le (by norm_num)).1 this |>.le

end SymplecticPacking.General
