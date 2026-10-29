import SymplecticPacking.Effective.NameArithmetic
import SymplecticPacking.Effective.SqrtName
import SymplecticPacking.Explicit

/-!
# Uniform rational-code name families

Uniform rational-code names: both the parameter and the requested digit are input.
-/

namespace SymplecticPacking.Effective.Family
open RationalCode

def slice (q : ℕ → ℕ) (c n : ℕ) : ℕ := q (Nat.pair c n)
def Names (q : ℕ → ℕ) (x : ℕ → ℝ) : Prop := ∀ c, CodeName.Names (slice q c) (x c)

def constant (q : ℕ → ℕ) (p : ℕ) : ℕ := q (Nat.unpair p).1

def add (q r : ℕ → ℕ) (p : ℕ) : ℕ :=
  CodeName.add (slice q (Nat.unpair p).1) (slice r (Nat.unpair p).1) (Nat.unpair p).2

def neg (q : ℕ → ℕ) (p : ℕ) : ℕ := CodeName.neg (slice q (Nat.unpair p).1) (Nat.unpair p).2

def half (q : ℕ → ℕ) (p : ℕ) : ℕ := CodeName.half (slice q (Nat.unpair p).1) (Nat.unpair p).2

def absolute (q : ℕ → ℕ) (p : ℕ) : ℕ :=
  CodeName.absolute (slice q (Nat.unpair p).1) (Nat.unpair p).2

def maximum (q r : ℕ → ℕ) (p : ℕ) : ℕ :=
  CodeName.maximum (slice q (Nat.unpair p).1) (slice r (Nat.unpair p).1) (Nat.unpair p).2

def mul (q r : ℕ → ℕ) (p : ℕ) : ℕ :=
  CodeName.mul (slice q (Nat.unpair p).1) (slice r (Nat.unpair p).1) (Nat.unpair p).2

lemma constant_spec (q : ℕ → ℕ) : Names (constant q) (fun c => value (q c)) := by
  intro c n
  simpa only [slice, constant, Nat.unpair_pair] using CodeName.constant_spec (q c) n

lemma add_spec {q r : ℕ → ℕ} {x y : ℕ → ℝ} (hq : Names q x) (hr : Names r y) :
    Names (add q r) (fun c => x c + y c) := by
  intro c n
  simpa only [slice, add, Nat.unpair_pair] using CodeName.add_spec (hq c) (hr c) n

lemma neg_spec {q : ℕ → ℕ} {x : ℕ → ℝ} (hq : Names q x) : Names (neg q) (fun c => -x c) := by
  intro c n
  simpa only [slice, neg, Nat.unpair_pair] using CodeName.neg_spec (hq c) n

lemma half_spec {q : ℕ → ℕ} {x : ℕ → ℝ} (hq : Names q x) : Names (half q) (fun c => x c/2) := by
  intro c n
  simpa only [slice, half, Nat.unpair_pair] using CodeName.half_spec (hq c) n

lemma abs_spec {q : ℕ → ℕ} {x : ℕ → ℝ} (hq : Names q x) : Names (absolute q) (fun c => |x c|) := by
  intro c n
  simpa only [slice, absolute, Nat.unpair_pair] using CodeName.abs_spec (hq c) n

lemma max_spec {q r : ℕ → ℕ} {x y : ℕ → ℝ} (hq : Names q x) (hr : Names r y) :
    Names (maximum q r) (fun c => Max.max (x c) (y c)) := by
  intro c n
  simpa only [slice, maximum, Nat.unpair_pair] using CodeName.max_spec (hq c) (hr c) n

lemma mul_spec {q r : ℕ → ℕ} {x y : ℕ → ℝ} (hq : Names q x) (hr : Names r y) :
    Names (mul q r) (fun c => x c * y c) := by
  intro c n
  simpa only [slice, mul, Nat.unpair_pair] using CodeName.mul_spec (hq c) (hr c) n

lemma constant_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (constant q) := by
  have hh := Oracle.comp hq (Oracle.left (O := O))
  exact hh.of_eq (fun _ => rfl)

lemma add_recursive {O : Set (ℕ →. ℕ)} {q r : ℕ → ℕ}
    (hq : Oracle.Total O q) (hr : Oracle.Total O r) : Oracle.Total O (add q r) := by
  have hshift : Oracle.Total O (fun p => Nat.pair (Nat.unpair p).1 ((Nat.unpair p).2+1)) :=
    Oracle.of_computable (Primrec.pair (Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))).to_comp
  have hf : Oracle.Total O (fun p => addCode (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_addCode.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  exact (Oracle.comp hf (Oracle.pair (Oracle.comp hq hshift) (Oracle.comp hr hshift))).of_eq
    (fun p => by simp only [add, CodeName.add, slice, Nat.unpair_pair])

lemma neg_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (neg q) :=
  (CodeName.neg_recursive hq).of_eq (fun p => by simp only [neg, CodeName.neg, slice, Nat.pair_unpair])

lemma half_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (half q) :=
  (CodeName.half_recursive hq).of_eq (fun p => by simp only [half, CodeName.half, slice, Nat.pair_unpair])

lemma abs_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (absolute q) :=
  (CodeName.abs_recursive hq).of_eq (fun p => by simp only [absolute, CodeName.absolute, slice, Nat.pair_unpair])

lemma max_recursive {O : Set (ℕ →. ℕ)} {q r : ℕ → ℕ}
    (hq : Oracle.Total O q) (hr : Oracle.Total O r) : Oracle.Total O (maximum q r) :=
  (CodeName.max_recursive hq hr).of_eq
    (fun p => by simp only [maximum, CodeName.maximum, slice, Nat.pair_unpair])

/-- The precision budget is queried at `(c,0)` separately for each parameter. -/
lemma mul_recursive {O : Set (ℕ →. ℕ)} {q r : ℕ → ℕ}
    (hq : Oracle.Total O q) (hr : Oracle.Total O r) : Oracle.Total O (mul q r) := by
  have hzero : Oracle.Total O (fun c => Nat.pair c 0) :=
    Oracle.pair (Oracle.of_computable Computable.id) (Oracle.of_computable (Computable.const 0))
  have hbudget : Oracle.Total O (fun p => CodeName.productBudget (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (CodeName.primitive_productBudget.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  have hK : Oracle.Total O (fun c => CodeName.productBudget (q (Nat.pair c 0)) (r (Nat.pair c 0))) :=
    (Oracle.comp hbudget (Oracle.pair (Oracle.comp hq hzero) (Oracle.comp hr hzero))).of_eq
      (fun c => by simp only [Nat.unpair_pair])
  have hsum : Oracle.Total O (fun p => (Nat.unpair p).1 + (Nat.unpair p).2) :=
    Oracle.of_computable (Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  have hprecision := Oracle.comp hsum (Oracle.pair Oracle.right (Oracle.comp hK Oracle.left))
  have hshift := Oracle.pair (Oracle.left (O := O)) hprecision
  have hf : Oracle.Total O (fun p => mulCode (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_mulCode.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  exact (Oracle.comp hf (Oracle.pair (Oracle.comp hq hshift) (Oracle.comp hr hshift))).of_eq
    (fun p => by simp only [Nat.unpair_pair, mul, CodeName.mul, slice])

/-- One oracle query at a fixed precision, followed by finite integer square root. -/
def sqrt (q : ℕ → ℕ) (p : ℕ) : ℕ :=
  SqrtName.code (slice q (Nat.unpair p).1) (Nat.unpair p).2

lemma sqrt_spec {q : ℕ → ℕ} {x : ℕ → ℝ} (hq : Names q x) (hx : ∀ c, 0 ≤ x c) :
    Names (sqrt q) (fun c => Real.sqrt (x c)) := by
  intro c n
  simpa only [slice, sqrt, Nat.unpair_pair] using SqrtName.code_names (hq c) (hx c) n

/-- The natural parameter remains part of the single oracle-query program. -/
lemma sqrt_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (sqrt q) := by
  have hp := Oracle.comp (Oracle.of_computable SqrtName.primitive_precision.to_comp)
    (Oracle.right (O:=O))
  have hi := Oracle.pair (Oracle.left (O:=O)) hp
  have hv := Oracle.comp hq hi
  have hd := Oracle.pair hv (Oracle.right (O:=O))
  have hf : Oracle.Total O (fun p=>SqrtName.output (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (SqrtName.primitive_output.comp Primrec.unpair).to_comp
  exact (Oracle.comp hf hd).of_eq (fun p=>by
    simp only [Nat.unpair_pair,sqrt,SqrtName.code,slice])

/-- A discrete branch condition is evaluated on the parameter, never on a real-order oracle. -/
def select (test q r : ℕ → ℕ) (p : ℕ) : ℕ :=
  if test (Nat.unpair p).1 = 0 then q p else r p

lemma select_spec {test q r : ℕ → ℕ} {x y : ℕ → ℝ} (hq : Names q x) (hr : Names r y) :
    Names (select test q r) (fun c => if test c = 0 then x c else y c) := by
  intro c n
  by_cases hc : test c = 0
  · simpa only [slice, select, Nat.unpair_pair, if_pos hc] using hq c n
  · simpa only [slice, select, Nat.unpair_pair, if_neg hc] using hr c n

lemma select_recursive {O : Set (ℕ →. ℕ)} {test q r : ℕ → ℕ}
    (ht : Oracle.Total O test) (hq : Oracle.Total O q) (hr : Oracle.Total O r) :
    Oracle.Total O (select test q r) := by
  have hc : PrimrecPred (fun p : ℕ => (Nat.unpair p).1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)
  have hf : Primrec (fun p : ℕ => if (Nat.unpair p).1 = 0 then
      (Nat.unpair (Nat.unpair p).2).1 else (Nat.unpair (Nat.unpair p).2).2) :=
    Primrec.ite hc (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hd := Oracle.pair (Oracle.comp ht (Oracle.left (O := O))) (Oracle.pair hq hr)
  exact (Oracle.comp (Oracle.of_computable hf.to_comp) hd).of_eq
    (fun p => by simp only [Nat.unpair_pair, select])

/-- An evaluator together with its correctness and uniform reduction to the
original input oracles. This wrapper introduces no new oracle. -/
structure Evaluator (O : Set (ℕ →. ℕ)) (x : ℕ → ℝ) where
  code : ℕ → ℕ
  names : Names code x
  recursive : Oracle.Total O code

namespace Evaluator
variable {O : Set (ℕ →. ℕ)} {x y : ℕ → ℝ}

def rational (q : ℕ → ℕ) (hq : Oracle.Total O q) : Evaluator O (fun c => value (q c)) :=
  ⟨constant q, constant_spec q, constant_recursive hq⟩

def congr (Q : Evaluator O x) (h : ∀ c, x c = y c) : Evaluator O y :=
  ⟨Q.code, by rw [← funext h]; exact Q.names, Q.recursive⟩

def add (Q : Evaluator O x) (R : Evaluator O y) : Evaluator O (fun c => x c+y c) :=
  ⟨Family.add Q.code R.code, add_spec Q.names R.names, add_recursive Q.recursive R.recursive⟩

def neg (Q : Evaluator O x) : Evaluator O (fun c => -x c) :=
  ⟨Family.neg Q.code, neg_spec Q.names, neg_recursive Q.recursive⟩

def half (Q : Evaluator O x) : Evaluator O (fun c => x c/2) :=
  ⟨Family.half Q.code, half_spec Q.names, half_recursive Q.recursive⟩

def mul (Q : Evaluator O x) (R : Evaluator O y) : Evaluator O (fun c => x c*y c) :=
  ⟨Family.mul Q.code R.code, mul_spec Q.names R.names, mul_recursive Q.recursive R.recursive⟩

def absolute (Q : Evaluator O x) : Evaluator O (fun c => |x c|) :=
  ⟨Family.absolute Q.code, abs_spec Q.names, abs_recursive Q.recursive⟩

def maximum (Q : Evaluator O x) (R : Evaluator O y) : Evaluator O (fun c => Max.max (x c) (y c)) :=
  ⟨Family.maximum Q.code R.code, max_spec Q.names R.names, max_recursive Q.recursive R.recursive⟩

def sqrt (Q : Evaluator O x) (hx : ∀ c, 0 ≤ x c) : Evaluator O (fun c => Real.sqrt (x c)) :=
  ⟨Family.sqrt Q.code, sqrt_spec Q.names hx, sqrt_recursive Q.recursive⟩

def select (test : ℕ → ℕ) (ht : Oracle.Total O test) (Q : Evaluator O x) (R : Evaluator O y) :
    Evaluator O (fun c => if test c = 0 then x c else y c) :=
  ⟨Family.select test Q.code R.code, select_spec Q.names R.names,
    select_recursive ht Q.recursive R.recursive⟩

end Evaluator

/-- A finite list of strict inequalities with uniform digit evaluators. -/
structure Margin (O : Set (ℕ →. ℕ)) where
  value : ℕ → ℝ
  evaluator : Evaluator O value

namespace Margin
variable {O : Set (ℕ →. ℕ)}

/-- The input is `((candidate, precision), inequality)`. The finite list is scanned
by its supplied order; there is no real comparison or enumeration of an abstract set. -/
def query : List (Margin O) → ℕ → ℕ
  | [], _ => zeroCode
  | M :: ms, p => if (Nat.unpair p).2 = 0 then M.evaluator.code (Nat.unpair p).1
      else query ms (Nat.pair (Nat.unpair p).1 ((Nat.unpair p).2-1))

def row : List (Margin O) → ℕ → ℕ → ℝ
  | [], _, _ => 0
  | M :: ms, c, i => if i=0 then M.value c else row ms c (i-1)

lemma query_spec (ms : List (Margin O)) (c i n : ℕ) :
    |(RationalCode.value (query ms (Nat.pair (Nat.pair c n) i)):ℝ)-row ms c i| ≤
      (radius n:ℝ) := by
  induction ms generalizing i with
  | nil => simp only [query, row, value_zeroCode, Rat.cast_zero, sub_zero, abs_zero]; exact_mod_cast (radius_pos n).le
  | cons M ms ih =>
      cases i with
      | zero => simpa only [query, row, Nat.unpair_pair, if_pos rfl, ite_true, slice] using M.evaluator.names c n
      | succ i =>
          simpa only [query, row, Nat.unpair_pair, Nat.succ_ne_zero, if_false,
            Nat.add_sub_cancel] using ih i

lemma row_pos_iff (ms : List (Margin O)) (c : ℕ) :
    (∀ i < ms.length, 0 < row ms c i) ↔ ∀ M ∈ ms, 0 < M.value c := by
  induction ms with
  | nil => simp
  | cons M ms ih =>
      constructor
      · intro h N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · simpa only [row, if_pos rfl, ite_true] using h 0 (by simp)
        · apply ih.mp (fun i hi => ?_) N hN
          simpa only [row, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using
            h (i+1) (by simpa using Nat.succ_lt_succ hi)
      · intro h i hi
        cases i with
        | zero => simpa only [row, if_pos rfl, ite_true] using h M (by simp)
        | succ i =>
            have hh := ih.mpr (fun N hN => h N (List.mem_cons_of_mem _ hN)) i
              (by simpa using hi)
            simpa only [row, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using hh

lemma namesMargins (ms : List (Margin O)) :
    (Oracle.family (fun _ => ms.length) (query ms)).NamesMargins
      (fun c i => row ms c i.val) := by
  intro c i n
  exact query_spec ms c i n

/-- A finite natural-arithmetic check of all strict margins at one candidate and precision. -/
def check (ms : List (Margin O)) : ℕ → ℕ := Oracle.stage (fun _ => ms.length) (query ms)

lemma check_sound (ms : List (Margin O)) {s : ℕ} (hs : check ms s=0) :
    ∀ i < ms.length, 0 < row ms (Nat.unpair s).1 i := by
  intro i hi
  have hcert := (Oracle.stage_family (fun _ => ms.length) (query ms) s).mp hs
  exact (Oracle.family (fun _ => ms.length) (query ms)).certified_sound
    (namesMargins ms) hcert ⟨i,hi⟩

lemma exists_check (ms : List (Margin O))
    (h : ∃ c, ∀ i < ms.length, 0 < row ms c i) : ∃ s, check ms s=0 := by
  apply Oracle.exists_stage_from_names (namesMargins ms)
  rcases h with ⟨c,hc⟩
  exact ⟨c,fun i => hc i i.isLt⟩

end Margin

#check_explicit Margin.query
#check_explicit Margin.check

#check_explicit add
#check_explicit mul
#check_explicit sqrt
#check_explicit select

end SymplecticPacking.Effective.Family
