import SymplecticPacking.Effective.RationalCode
import Mathlib.Computability.RecursiveIn

/-!
# Oracle-relative recursion

An input name is an oracle, not a finitely encoded real number. The closure properties here
(composition, pairing, primitive recursion and least-stage search) use Mathlib's
oracle-recursion semantics. In particular, they do not require the supplied
name to be computable without its oracle. Geometric evaluation still needs its own
reduction to the input names.
-/

namespace SymplecticPacking.Effective.Oracle

abbrev Total (O : Set (ℕ →. ℕ)) (f : ℕ → ℕ) : Prop :=
  Nat.RecursiveIn O (fun n => Part.some (f n))

theorem of_computable {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Computable f) : Total O f :=
  RecursiveIn.iff_nat.mp hf.computableIn

theorem query {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ}
    (hq : (fun n => Part.some (q n)) ∈ O) : Total O q :=
  .oracle _ hq

theorem comp {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Total O f) (hg : Total O g) : Total O (fun n => f (g n)) := by
  exact (Nat.RecursiveIn.comp hf hg).of_eq fun n => by simp

theorem pair {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Total O f) (hg : Total O g) : Total O (fun n => Nat.pair (f n) (g n)) := by
  exact (Nat.RecursiveIn.pair hf hg).of_eq fun n => by
    simp only [← Part.pure_eq_some, map_pure, pure_seq]

/-- Primitive recursion makes finitely many oracle calls, without a continuity or
computability assumption on the oracle itself. -/
theorem prec {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Total O f) (hg : Total O g) :
    Total O (fun p => (Nat.unpair p).2.rec (f (Nat.unpair p).1)
      (fun y i => g (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) := by
  apply (Nat.RecursiveIn.prec hf hg).of_eq
  intro p
  obtain ⟨a, n, hp⟩ : ∃ a n, Nat.unpair p = (a, n) :=
    ⟨(Nat.unpair p).1, (Nat.unpair p).2, rfl⟩
  simp only [hp]
  clear hp p
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only
    rw [ih]
    simp only [Part.bind_eq_bind, Part.bind_some]

set_option backward.isDefEq.respectTransparency.types false in
/-- Least successful finite stage, in oracle-recursive semantics. A zero checker value
means acceptance. The existential assumption proves totality of this search. -/
theorem firstZero {O : Set (ℕ →. ℕ)} {check : ℕ → ℕ}
    (hcheck : Total O check) (hex : ∀ a, ∃ n, check (Nat.pair a n) = 0) :
    Total O (fun a => Nat.find (hex a)) := by
  apply (Nat.RecursiveIn.rfind hcheck).of_eq_tot
  intro a
  change Nat.find (hex a) ∈ Nat.rfind
    (fun n => Part.some (decide (check (Nat.pair a n) = 0)))
  apply Nat.mem_rfind.mpr
  constructor
  · exact Part.mem_some_iff.mpr (decide_eq_true (Nat.find_spec (hex a))).symm
  · intro m hm
    simp [Nat.find_min (hex a) hm]

end SymplecticPacking.Effective.Oracle
