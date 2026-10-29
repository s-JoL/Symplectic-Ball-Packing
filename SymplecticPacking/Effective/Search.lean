import SymplecticPacking.Effective.Names
import Mathlib.Computability.RE

/-!
# Certified dovetailed search over finite rational inequalities

Candidates are indexed by naturals. Each candidate has finitely many named real margins.
Pairing enumerates candidate/precision pairs; every test uses only a finite list of rational
values. The first certified candidate is returned, rather than the least valid candidate.
-/

namespace SymplecticPacking.Effective

open Filter Topology

/-- Rational oracle values for finitely many inequalities of each candidate. -/
structure CertificateFamily where
  count : ℕ → ℕ
  approx : (candidate : ℕ) → Fin (count candidate) → ℕ → ℚ

namespace CertificateFamily

variable (F : CertificateFamily)

/-- A candidate passes when all its rational lower endpoints are positive. -/
def certified (candidate precision : ℕ) : Bool :=
  decide (∀ i, radius precision < F.approx candidate i precision)

/-- Cantor-style pairing dovetails candidates and precision, without waiting on one candidate. -/
def stage (s : ℕ) : Bool := F.certified (Nat.unpair s).1 (Nat.unpair s).2

/-- The family names the real margins of the candidates. -/
def NamesMargins (x : (candidate : ℕ) → Fin (F.count candidate) → ℝ) : Prop :=
  ∀ c i, Names (F.approx c i) (x c i)

theorem certified_sound {x : (c : ℕ) → Fin (F.count c) → ℝ} (hx : F.NamesMargins x)
    {c n : ℕ} (hcert : F.certified c n = true) : ∀ i, 0 < x c i := by
  have hc : ∀ i, radius n < F.approx c i n := of_decide_eq_true hcert
  exact fun i => positive_of_certificate (hx c i) (hc i)

theorem eventually_certified {x : (c : ℕ) → Fin (F.count c) → ℝ} (hx : F.NamesMargins x)
    {c : ℕ} (hc : ∀ i, 0 < x c i) : ∀ᶠ n in atTop, F.certified c n = true := by
  have h := Filter.eventually_all.mpr fun i => eventually_positive_certificate (hx c i) (hc i)
  filter_upwards [h] with n hn
  exact decide_eq_true hn

/-- Nonemptiness of the rational, genuinely decidable stage predicate. -/
theorem exists_stage {x : (c : ℕ) → Fin (F.count c) → ℝ} (hx : F.NamesMargins x)
    (hex : ∃ c, ∀ i, 0 < x c i) : ∃ s, F.stage s = true := by
  obtain ⟨c, hc⟩ := hex
  obtain ⟨n, hn⟩ := (F.eventually_certified hx hc).exists
  exact ⟨Nat.pair c n, by simpa [stage, Nat.unpair_pair] using hn⟩

/-- Search over the certified finite stage predicate. The proof is erased from execution. -/
def findStage (h : ∃ s, F.stage s = true) : ℕ := Nat.find h

/-- The returned finite certificate is the candidate index together with its certified precision. -/
def search (h : ∃ s, F.stage s = true) : ℕ × ℕ := Nat.unpair (F.findStage h)

theorem search_certified (h : ∃ s, F.stage s = true) :
    F.certified (F.search h).1 (F.search h).2 = true := Nat.find_spec h

theorem search_sound {x : (c : ℕ) → Fin (F.count c) → ℝ} (hx : F.NamesMargins x)
    (h : ∃ s, F.stage s = true) : ∀ i, 0 < x (F.search h).1 i :=
  F.certified_sound hx (F.search_certified h)

end CertificateFamily

/-- Executable bounded simulation of sequential finite stage tests. -/
def searchFuel (check : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, start => if check start then some start else searchFuel check fuel (start + 1)

theorem searchFuel_of_first {check : ℕ → Bool} {fuel start n : ℕ}
    (hstart : start ≤ n) (hbound : n < start + fuel) (hn : check n = true)
    (hmin : ∀ j, start ≤ j → j < n → check j = false) :
    searchFuel check fuel start = some n := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases heq : start = n
    · subst start
      simp [searchFuel, hn]
    · have hlt : start < n := by omega
      simp only [searchFuel, hmin start le_rfl hlt, Bool.false_eq_true, ↓reduceIte]
      exact ih (by omega) (by omega) (fun j hj hjn => hmin j (by omega) hjn)

/-- A nonempty decidable stage search halts after finitely many Boolean tests. -/
theorem searchFuel_find {check : ℕ → Bool} (h : ∃ n, check n = true) :
    searchFuel check (Nat.find h + 1) 0 = some (Nat.find h) := by
  apply searchFuel_of_first (Nat.zero_le _) (by omega) (Nat.find_spec h)
  intro j _ hj
  exact Bool.eq_false_iff.mpr (Nat.find_min h hj)

/-- The generic engine is partial-recursive computable whenever its stage predicate is.
This theorem does not assume that an arbitrary supplied rational oracle is computable. -/
theorem computable_first_stage {α : Type*} [Primcodable α] (check : α → ℕ → Bool)
    (hcheck : Computable (fun p : α × ℕ => check p.1 p.2))
    (hex : ∀ a, ∃ n, check a n = true) :
    Computable (fun a => Nat.find (hex a)) := by
  have hp : ComputablePred (fun p : α × ℕ => check p.1 p.2 = true) := by
    apply Computable.computablePred
    exact hcheck.of_eq fun p => by cases check p.1 p.2 <;> rfl
  exact Computable.find hp hex

end SymplecticPacking.Effective
