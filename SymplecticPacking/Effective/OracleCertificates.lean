import SymplecticPacking.Effective.Oracle

/-!
# Finite rational certificates from a name oracle

The oracle query `pair (pair candidate precision) inequality` returns a rational code.
Each stage makes exactly the finite number of queries specified by `count`. All tests
and search are recursive relative to that oracle. No oracle for the search result is used.
-/

namespace SymplecticPacking.Effective.Oracle

open RationalCode

def failure (u n : ℕ) : ℕ := if PositiveAt u n then 0 else 1

theorem failure_zero (u n : ℕ) : failure u n = 0 ↔ PositiveAt u n := by
  by_cases h : PositiveAt u n <;> simp [failure, h]

theorem primitive_failure : Primrec₂ failure :=
  Primrec.ite primitive_positiveAt (Primrec.const 0) (Primrec.const 1)

theorem left {O : Set (ℕ →. ℕ)} : Total O (fun n => (Nat.unpair n).1) :=
  of_computable (Primrec.fst.comp Primrec.unpair).to_comp

theorem right {O : Set (ℕ →. ℕ)} : Total O (fun n => (Nat.unpair n).2) :=
  of_computable (Primrec.snd.comp Primrec.unpair).to_comp

theorem addPair {O : Set (ℕ →. ℕ)} :
    Total O (fun n => (Nat.unpair n).1 + (Nat.unpair n).2) :=
  of_computable (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp

def term (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  failure (q x) (Nat.unpair (Nat.unpair x).1).2

theorem total_term {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Total O q) :
    Total O (term q) := by
  have hf : Total O (fun n => failure (Nat.unpair n).1 (Nat.unpair n).2) :=
    of_computable (primitive_failure.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have h := comp hf (pair hq (comp right left))
  exact h.of_eq fun n => by simp only [Nat.unpair_pair]; rfl

def sum (q : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sum q a n + term q (Nat.pair a n)

theorem sum_eq_rec (q : ℕ → ℕ) (a n : ℕ) :
    sum q a n = n.rec 0 (fun i acc => acc + term q (Nat.pair a i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih]

set_option maxHeartbeats 1200000 in
theorem total_sum {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Total O q) :
    Total O (fun p => sum q (Nat.unpair p).1 (Nat.unpair p).2) := by
  have hk := pair (left (O := O)) (comp (left (O := O)) (right (O := O)))
  have ht := comp (total_term hq) hk
  have hs₀ := comp (addPair (O := O)) (pair (comp (right (O := O)) (right (O := O))) ht)
  have hs : Total O (fun x => (Nat.unpair (Nat.unpair x).2).2 +
      term q (Nat.pair (Nat.unpair x).1 (Nat.unpair (Nat.unpair x).2).1)) :=
    hs₀.of_eq fun x => by simp only [Nat.unpair_pair]
  exact (prec (of_computable (Computable.const 0)) hs).of_eq fun p => by
    simp only [sum_eq_rec, Nat.unpair_pair]

theorem sum_zero_iff (q : ℕ → ℕ) (a n : ℕ) :
    sum q a n = 0 ↔ ∀ i < n, PositiveAt (q (Nat.pair a i)) (Nat.unpair a).2 := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp only [sum, Nat.add_eq_zero_iff, ih, term, Nat.unpair_pair, failure_zero]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

def stage (count q : ℕ → ℕ) (s : ℕ) : ℕ := sum q s (count (Nat.unpair s).1)

theorem total_stage {O : Set (ℕ →. ℕ)} {count q : ℕ → ℕ}
    (hc : Computable count) (hq : Total O q) : Total O (stage count q) := by
  have h := comp (total_sum hq)
    (pair (of_computable Computable.id) (comp (of_computable hc) left))
  exact h.of_eq fun s => by simp only [Nat.unpair_pair]; rfl

theorem stage_zero_iff (count q : ℕ → ℕ) (s : ℕ) :
    stage count q s = 0 ↔ ∀ i < count (Nat.unpair s).1,
      radius (Nat.unpair s).2 < value (q (Nat.pair s i)) := by
  simp only [stage, sum_zero_iff, positiveAt_iff]

/-- A finite evaluator reduced to the input oracles can be followed by the search.
No oracle for the search result is added. -/
theorem search_reduction {O : Set (ℕ →. ℕ)} {count q : ℕ → ℕ}
    (hc : Computable count) (hq : Total O q)
    (hex : ∃ s, stage count q s = 0) :
    Total O (fun _ => Nat.find hex) := by
  have hcheck := comp (total_stage hc hq) right
  have h := firstZero hcheck (fun _ => by simpa only [Nat.unpair_pair] using hex)
  exact h.of_eq fun a => by simp only [Nat.unpair_pair]

def family (count q : ℕ → ℕ) : CertificateFamily where
  count := count
  approx c i n := value (q (Nat.pair (Nat.pair c n) i))

theorem stage_family (count q : ℕ → ℕ) (s : ℕ) :
    stage count q s = 0 ↔ (family count q).stage s = true := by
  rw [stage_zero_iff]
  simp only [CertificateFamily.stage, CertificateFamily.certified, family,
    decide_eq_true_eq, Nat.pair_unpair]
  constructor
  · intro h i
    exact h i i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

/-- Name accuracy and one strictly feasible candidate imply termination of the 
natural-arithmetic checker, including candidates with zero inequalities. -/
theorem exists_stage_from_names {count q : ℕ → ℕ}
    {x : (c : ℕ) → Fin (count c) → ℝ}
    (hx : (family count q).NamesMargins x) (hex : ∃ c, ∀ i, 0 < x c i) :
    ∃ s, stage count q s = 0 := by
  obtain ⟨s, hs⟩ := (family count q).exists_stage hx hex
  exact ⟨s, (stage_family count q s).mpr hs⟩

theorem search_sound_from_names {count q : ℕ → ℕ}
    {x : (c : ℕ) → Fin (count c) → ℝ}
    (hx : (family count q).NamesMargins x) (hex : ∃ s, stage count q s = 0) :
    ∀ i, 0 < x (Nat.unpair (Nat.find hex)).1 i := by
  exact (family count q).certified_sound hx
    ((stage_family count q (Nat.find hex)).mp (Nat.find_spec hex))

end SymplecticPacking.Effective.Oracle
