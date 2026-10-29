import SymplecticPacking.Effective.PackingCertificateStateList
import SymplecticPacking.Effective.OracleCertificates

/-!
# Centre vectors from scalar name queries

Finite vectors are read from the original scalar centre-name queries.
-/

namespace SymplecticPacking.Effective.PackingSearchInput
open RationalCode PackingStateList
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Append one scalar name sample to an encoded finite list. -/
def appendCode (xs x : ℕ) : ℕ := Encodable.encode (decodeList xs ++ [x])

theorem primitive_appendCode : Primrec₂ appendCode := by
  exact Primrec.encode.comp (Primrec.list_append.comp
    (primitive_decodeList.comp Primrec.fst)
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

/-- This recursion reads precisely the first `d` scalar coordinates. -/
def queryVector (q : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => Encodable.encode ([] : List ℕ)
  | d+1 => appendCode (queryVector q a d) (q (Nat.pair a d))

theorem queryVector_eq (q : ℕ → ℕ) (a d : ℕ) :
    queryVector q a d=Encodable.encode ((List.range d).map (fun j => q (Nat.pair a j))) := by
  induction d with
  | zero => rfl
  | succ d ih => simp [queryVector,appendCode,ih,decodeList,List.range_succ]

theorem queryVector_decode (q : ℕ → ℕ) (a d : ℕ) :
    ODECode.decodeState d (queryVector q a d)=fun j => q (Nat.pair a j.val) := by
  have hl : (List.range d).map (fun j => q (Nat.pair a j))=
      List.ofFn (fun j : Fin d => q (Nat.pair a j.val)) := by
    apply List.ext_getElem <;> simp
  rw [queryVector_eq,hl,←encodeState_eq_list,ODECode.decodeState_encodeState]

/-- The dimension is an input of the same oracle machine. -/
theorem queryVector_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ}
    (hq : Oracle.Total O q) :
    Oracle.Total O (fun x => queryVector q (Nat.unpair x).1 (Nat.unpair x).2) := by
  have hquery := Oracle.comp hq (Oracle.pair (Oracle.left (O:=O))
    (Oracle.comp (Oracle.left (O:=O)) (Oracle.right (O:=O))))
  have happ := Oracle.of_computable (O:=O)
    (primitive_appendCode.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have hs := Oracle.comp happ (Oracle.pair
    (Oracle.comp (Oracle.right (O:=O)) (Oracle.right (O:=O))) hquery)
  have hr := Oracle.prec (Oracle.of_computable (O:=O)
    (Computable.const (Encodable.encode ([] : List ℕ)))) hs
  exact hr.of_eq fun x => by
    simp only [Nat.unpair_pair]
    have hh : (Nat.unpair x).2.rec (Encodable.encode ([] : List ℕ))
        (fun d acc => appendCode acc (q (Nat.pair (Nat.unpair x).1 d)))=
        queryVector q (Nat.unpair x).1 (Nat.unpair x).2 := by
      induction (Nat.unpair x).2 with
      | zero => rfl
      | succ d ih => simp only [Nat.rec_add_one,queryVector,ih]
    exact congrArg Part.some hh

def sourceState (q : ℕ → ℕ) (d i p : ℕ) : ℕ := queryVector q (Nat.pair i p) d

theorem sourceState_decode (q : ℕ → ℕ) (d i p : ℕ) :
    ODECode.decodeState d (sourceState q d i p)=fun j => q (Nat.pair (Nat.pair i p) j.val) :=
  queryVector_decode q (Nat.pair i p) d

theorem sourceState_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ}
    (hq : Oracle.Total O q) :
    Oracle.Total O (fun x => sourceState q (Nat.unpair x).1
      (Nat.unpair (Nat.unpair x).2).1 (Nat.unpair (Nat.unpair x).2).2) := by
  have h := Oracle.comp (queryVector_recursive hq)
    (Oracle.pair (Oracle.right (O:=O)) (Oracle.left (O:=O)))
  exact h.of_eq fun x => by simp only [Nat.unpair_pair,sourceState,Nat.pair_unpair]

#check_explicit queryVector
end SymplecticPacking.Effective.PackingSearchInput
