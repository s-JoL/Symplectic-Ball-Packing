import SymplecticPacking.Effective.Search

/-!
# Finite natural-number codes for rational certificate values

The code `pair (pair a b) d` denotes `(a-b)/(d+1)`. No normalization or arbitrary
enumeration of rationals is needed to test its sign against the dyadic error radius.
The test is proved primitive recursive, and so is the finite conjunction of tests.
-/

namespace SymplecticPacking.Effective

namespace RationalCode

def positiveNumerator (u : ℕ) : ℕ := (Nat.unpair (Nat.unpair u).1).1
def negativeNumerator (u : ℕ) : ℕ := (Nat.unpair (Nat.unpair u).1).2
def denominator (u : ℕ) : ℕ := (Nat.unpair u).2 + 1

def value (u : ℕ) : ℚ :=
  ((positiveNumerator u : ℚ) - negativeNumerator u) / denominator u

def encode (a b d : ℕ) : ℕ := Nat.pair (Nat.pair a b) d

theorem value_encode (a b d : ℕ) :
    value (encode a b d) = ((a : ℚ) - b) / (d + 1) := by
  simp [value, encode, positiveNumerator, negativeNumerator, denominator, Nat.unpair_pair]

/-- A concrete code for every rational, including negative rationals. -/
def ofRat (q : ℚ) : ℕ := encode q.num.toNat (-q.num).toNat (q.den - 1)

theorem value_ofRat (q : ℚ) : value (ofRat q) = q := by
  rw [ofRat, value_encode]
  have hden : ((q.den - 1 : ℕ) : ℚ) + 1 = q.den := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ q.den by have := q.den_pos; omega))
  have hnum : ((q.num.toNat : ℕ) : ℚ) - ((-q.num).toNat : ℕ) = (q.num : ℚ) := by
    have h : (q.num.toNat : ℤ) - ((-q.num).toNat : ℤ) = q.num := by omega
    exact_mod_cast h
  rw [hden, hnum]
  exact q.num_div_den

/-- Cross multiplication tests a rational margin using only natural arithmetic. -/
def PositiveAt (u n : ℕ) : Prop :=
  negativeNumerator u * 2 ^ n + denominator u < positiveNumerator u * 2 ^ n

instance : DecidableRel PositiveAt := fun _ _ => inferInstanceAs (Decidable (_ < _))

theorem positiveAt_iff (u n : ℕ) : PositiveAt u n ↔ radius n < value u := by
  have hd : (0 : ℚ) < denominator u := by unfold denominator; positivity
  have hp : (0 : ℚ) < 2 ^ n := by positivity
  unfold PositiveAt radius value
  rw [div_pow, one_pow, div_lt_div_iff₀ hp hd]
  constructor
  · intro h
    have hq : (negativeNumerator u : ℚ) * 2 ^ n + denominator u <
        (positiveNumerator u : ℚ) * 2 ^ n := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (negativeNumerator u : ℚ) * 2 ^ n + denominator u <
        (positiveNumerator u : ℚ) * 2 ^ n := by nlinarith
    exact_mod_cast hq

theorem primitive_positiveAt : PrimrecRel PositiveAt := by
  have ha : Primrec positiveNumerator :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hb : Primrec negativeNumerator :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hd : Primrec denominator :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)
  have hp : Primrec (fun n : ℕ => 2 ^ n) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (hb.comp Primrec.fst) (hp.comp Primrec.snd))
      (hd.comp Primrec.fst))
    (Primrec.nat_mul.comp (ha.comp Primrec.fst) (hp.comp Primrec.snd))

/-- The complete finite rational certificate test, with no real-valued decisions. -/
def allPositive (codes : List ℕ) (n : ℕ) : Bool :=
  decide (∀ u ∈ codes, PositiveAt u n)

theorem primitive_allPositive : Primrec₂ allPositive :=
  primitive_positiveAt.forall_mem_list.decide

/-- Encode the finite list of rational inequalities of a certificate family. -/
def familyValues (F : CertificateFamily) (c n : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (F.count c) => ofRat (F.approx c i n)

theorem allPositive_familyValues (F : CertificateFamily) (c n : ℕ) :
    allPositive (familyValues F c n) n = F.certified c n := by
  unfold allPositive CertificateFamily.certified
  congr 1
  apply propext
  constructor
  · intro h i
    exact (positiveAt_iff _ _).mp (h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) |>.trans_eq (by rw [value_ofRat])
  · intro h u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact (positiveAt_iff _ _).mpr (by simpa [value_ofRat] using h i)

/-- From a computable finite list of named rational values at each stage, the 
certificate predicate is computable. This proves the finite-checker bridge, not the
computability of the geometric evaluator which supplies those values. -/
theorem computable_stages {α : Type*} [Primcodable α]
    (codes : α → ℕ → List ℕ)
    (hcodes : Computable (fun p : α × ℕ => codes p.1 p.2)) :
    Computable (fun p : α × ℕ => allPositive (codes p.1 p.2) (Nat.unpair p.2).2) := by
  exact primitive_allPositive.to_comp.comp hcodes
    (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd))

theorem computable_search {α : Type*} [Primcodable α] (codes : α → ℕ → List ℕ)
    (hcodes : Computable (fun p : α × ℕ => codes p.1 p.2))
    (hex : ∀ a, ∃ s, allPositive (codes a s) (Nat.unpair s).2 = true) :
    Computable (fun a => Nat.find (hex a)) :=
  computable_first_stage (fun a s => allPositive (codes a s) (Nat.unpair s).2)
    (computable_stages codes hcodes) hex

end RationalCode

end SymplecticPacking.Effective
