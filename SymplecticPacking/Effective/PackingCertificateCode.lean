import SymplecticPacking.Effective.PackingCertificateTarget
import SymplecticPacking.Effective.ODECode

/-!
# Natural-number code for the finite packing tests

Natural-number arithmetic implementation of the finite rational packing tests.
-/

namespace SymplecticPacking.Effective.PackingCertificateCode

open RationalCode
open PackingCertificate
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sumCodes (xs : List ℕ) : ℕ := xs.foldr addCode zeroCode

theorem sumCodes_value (xs : List ℕ) : value (sumCodes xs) = (xs.map value).sum := by
  induction xs with
  | nil => exact value_zeroCode
  | cons x xs ih => simp only [sumCodes, List.foldr_cons, value_addCode,
      List.map_cons, List.sum_cons] at *; rw [ih]

theorem primitive_sumCodes : Primrec sumCodes := by
  exact Primrec.list_foldr Primrec.id (Primrec.const zeroCode)
    (primitive_addCode.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

def squareNormCode (d state : ℕ) : ℕ := sumCodes
  (List.ofFn fun j : Fin d => mulCode (ODECode.decodeState d state j)
    (ODECode.decodeState d state j))

theorem squareNormCode_value (d state : ℕ) :
    value (squareNormCode d state) = sqNorm (ODECode.rationalState
      (ODECode.decodeState d state)) := by
  simp [squareNormCode, sumCodes_value, Fin.sum_ofFn, Function.comp_def, sqNorm, ODECode.rationalState,
    value_mulCode, pow_two]

/-- Codes for the squared distance from a rational source centre. -/
@[irreducible] def distanceCode (d state source : ℕ) : ℕ := sumCodes
  (List.ofFn fun j : Fin d =>
    let u := addCode (ODECode.decodeState d state j)
      (negCode (ODECode.decodeState d source j))
    mulCode u u)

theorem distanceCode_value (d state source : ℕ) :
    value (distanceCode d state source) = sqNorm
      (ODECode.rationalState (ODECode.decodeState d state)-
        ODECode.rationalState (ODECode.decodeState d source)) := by
  simp [distanceCode, sumCodes_value, Fin.sum_ofFn, Function.comp_def, sqNorm, ODECode.rationalState,
    value_mulCode, value_addCode, value_negCode, pow_two, sub_eq_add_neg]

def dimCode (d : ℕ) : ℕ := encode d 0 0

@[simp] theorem dimCode_value (d : ℕ) : value (dimCode d) = (d:ℚ) := by
  simp [dimCode, value_encode]

theorem primitive_dimCode : Primrec dimCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)

/-- The rational radius computed by the certifier, with exact field queries. -/
def errorCode (H N ρ : ℕ) : ℕ :=
  addCode
    (mulCode (addCode ρ (divideNatCode (dimCode (H+H*H)) (N-1))) (dimCode (4^H)))
    (divideNatCode (dimCode H) (N-1))

def plateauCode (B : ℕ) : ℕ := divideNatCode (dimCode B) 1

theorem errorCode_value (H N ρ : ℕ) (hN : 0<N) :
    value (errorCode H N ρ)=error H H H N (value ρ) 0 := by
  have hd : ((N-1:ℕ):ℚ)+1=N := by exact_mod_cast Nat.sub_add_cancel hN
  simp only [errorCode,value_addCode,value_mulCode,value_divideNatCode,dimCode_value,hd,error]
  push_cast
  ring

theorem plateauCode_value (B : ℕ) : value (plateauCode B)=(B:ℚ)/2 := by
  norm_num [plateauCode,value_divideNatCode]

theorem primitive_errorCode :
    Primrec (fun a : ℕ × (ℕ × ℕ) => errorCode a.1 a.2.1 a.2.2) := by
  have hH : Primrec (fun a : ℕ × (ℕ × ℕ) => a.1) := Primrec.fst
  have hN : Primrec (fun a : ℕ × (ℕ × ℕ) => a.2.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have hC := primitive_dimCode.comp (Primrec.nat_add.comp hH (Primrec.nat_mul.comp hH hH))
  have hp := primitive_dimCode.comp
    ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 4) hH)
  exact primitive_addCode.comp
    (primitive_mulCode.comp (primitive_addCode.comp (Primrec.snd.comp Primrec.snd)
      (primitive_divideNatCode.comp hC hN)) hp)
    (primitive_divideNatCode.comp (primitive_dimCode.comp hH) hN)

theorem primitive_plateauCode : Primrec plateauCode :=
  primitive_divideNatCode.comp primitive_dimCode (Primrec.const 1)

def targetMargin (d e R : ℕ) : ℕ := addCode R (negCode (mulCode (dimCode d) e))

theorem targetMargin_value (d e R : ℕ) :
    value (targetMargin d e R) = value R-(d:ℚ)*value e := by
  simp [targetMargin, value_addCode, value_negCode, value_mulCode, sub_eq_add_neg]

/-- Zero is acceptance. Every comparison is natural cross multiplication. -/
def targetFailure (d state e R : ℕ) : ℕ :=
  if Less zeroCode (targetMargin d e R) ∧
      Less (squareNormCode d state) (mulCode (targetMargin d e R) (targetMargin d e R))
  then 0 else 1

theorem targetFailure_zero (d state e R : ℕ) :
    targetFailure d state e R = 0 ↔
      targetCheck (ODECode.rationalState (ODECode.decodeState d state))
        (value e) (value R) = true := by
  simp [targetFailure, targetCheck, less_iff, value_zeroCode, targetMargin_value,
    squareNormCode_value, value_mulCode, pow_two]

@[irreducible] def coordinateFailure (d state e R : ℕ) : ℕ :=
  (List.ofFn fun j : Fin d =>
    if Less (addCode (absCode (ODECode.decodeState d state j)) e) R then 0 else 1).sum

theorem coordinateFailure_zero (d state e R : ℕ) :
    coordinateFailure d state e R = 0 ↔
      ∀ j, |ODECode.rationalState (ODECode.decodeState d state) j|+value e < value R := by
  simp only [coordinateFailure, List.sum_eq_zero_iff, List.mem_ofFn]
  constructor
  · intro h j
    have hh := h _ ⟨j, rfl⟩
    simpa only [ite_eq_left_iff, one_ne_zero, imp_false, not_not,
      less_iff, value_addCode, value_absCode, ODECode.rationalState] using hh
  · intro h a ha
    obtain ⟨j, rfl⟩ := ha
    have hh : Less (addCode (absCode (ODECode.decodeState d state j)) e) R := by
      simpa only [less_iff, value_addCode, value_absCode, ODECode.rationalState] using h j
    simp [hh]

def outsideFailure (d state source ρ r : ℕ) : ℕ :=
  let margin := addCode r (mulCode (dimCode d) ρ)
  if Less (mulCode margin margin) (distanceCode d state source) then 0 else 1

theorem outsideFailure_zero (d state source ρ r : ℕ) :
    outsideFailure d state source ρ r = 0 ↔
      outsideCheck (ODECode.rationalState (ODECode.decodeState d state))
        (ODECode.rationalState (ODECode.decodeState d source)) (value ρ) (value r) = true := by
  simp [outsideFailure, outsideCheck, less_iff, value_mulCode, value_addCode,
    distanceCode_value, pow_two]

/-- Exact Euler iteration with independently variable mesh and iteration count.
`a=pair (pair mesh precision) initial`; `b=pair a count`. -/
def iteration (d : ℕ) (field : ℕ → ℕ) (a i : ℕ) : ℕ :=
  ODECode.iterate d (Nat.unpair (Nat.unpair a).1).1
    (Nat.unpair (Nat.unpair a).1).2 field (Nat.unpair a).2 i

/-- A finite sum of natural test failures. It adds no oracle of its own. -/
def sumFailure (q : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => sumFailure q a i+q (Nat.pair a i)

theorem sumFailure_zero (q : ℕ → ℕ) (a n : ℕ) :
    sumFailure q a n = 0 ↔ ∀ i < n, q (Nat.pair a i) = 0 := by
  induction n with
  | zero => simp [sumFailure]
  | succ n ih =>
      simp only [sumFailure, Nat.add_eq_zero_iff, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h i hi
        · exact hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem sumFailure_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ}
    (hq : Oracle.Total O q) :
    Oracle.Total O (fun b => sumFailure q (Nat.unpair b).1 (Nat.unpair b).2) := by
  have hq' := Oracle.comp hq (Oracle.pair (Oracle.left (O := O))
    (Oracle.comp (Oracle.left (O := O)) (Oracle.right (O := O))))
  have hs := Oracle.comp (Oracle.addPair (O := O))
    (Oracle.pair (Oracle.comp (Oracle.right (O := O)) (Oracle.right (O := O))) hq')
  have hl := Oracle.prec (Oracle.of_computable (Computable.const 0)) hs
  exact hl.of_eq fun b => by
    simp only [Nat.unpair_pair]
    have heq : (Nat.unpair b).2.rec 0 (fun i acc => acc+q (Nat.pair (Nat.unpair b).1 i)) =
        sumFailure q (Nat.unpair b).1 (Nat.unpair b).2 := by
      induction (Nat.unpair b).2 with
      | zero => rfl
      | succ i ih => simp only [sumFailure, ih]
    exact congrArg Part.some heq

/-- One Euler-table row. Runtime data are `a=pair core (pair error plateau)`;
`core=pair (pair mesh precision) initial` and `b=pair a row`. -/
def rowFailure (d : ℕ) (field : ℕ → ℕ) (b : ℕ) : ℕ :=
  coordinateFailure d
    (iteration d field (Nat.unpair (Nat.unpair b).1).1 (Nat.unpair b).2)
    (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).1
    (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).2

/-- The finite all-time tube program. Its bound is the mesh plus one,
so both endpoints and every intermediate Euler step are checked. -/
def tubeFailure (d : ℕ) (field : ℕ → ℕ) (a : ℕ) : ℕ :=
  sumFailure (rowFailure d field) a
    ((Nat.unpair (Nat.unpair (Nat.unpair a).1).1).1+1)

theorem tubeFailure_zero (d N p initial e R : ℕ) (field : ℕ → ℕ) :
    tubeFailure d field (Nat.pair (Nat.pair (Nat.pair N p) initial) (Nat.pair e R))=0 ↔
      plateauCheck N (fun i => ODECode.rationalState (ODECode.decodeState d
        (ODECode.iterate d N p field initial i))) (value e) (value R)=true := by
  simp only [tubeFailure, Nat.unpair_pair, sumFailure_zero, rowFailure, iteration,
    coordinateFailure_zero, plateauCheck, decide_eq_true_eq]
  constructor
  · intro h i j
    exact h i.val i.isLt j
  · intro h i hi j
    exact h ⟨i,hi⟩ j

/-- One complete source-cell computation. The time step and candidate code are
runtime data, and the Euler table is computed before testing it. -/
def cellFailure (d : ℕ) (field : ℕ → ℕ)
    (N p initial source ρ r e plateau target : ℕ) : ℕ :=
  if outsideFailure d initial source ρ r=0 then 0 else
    tubeFailure d field (Nat.pair (Nat.pair (Nat.pair N p) initial) (Nat.pair e plateau))+
      targetFailure d (ODECode.iterate d N p field initial N) e target

theorem cellFailure_zero (d : ℕ) (field : ℕ → ℕ)
    (N p initial source ρ r e plateau target : ℕ) :
    cellFailure d field N p initial source ρ r e plateau target=0 ↔
      cellCheck N (fun i => ODECode.rationalState (ODECode.decodeState d
        (ODECode.iterate d N p field initial i)))
        (ODECode.rationalState (ODECode.decodeState d source))
        (value ρ) (value r) (value e) (value plateau) (value target)=true := by
  have hi : ODECode.iterate d N p field initial 0=initial := rfl
  simp only [cellFailure, cellCheck, hi, Bool.or_eq_true, Bool.and_eq_true,
    ← outsideFailure_zero, ← targetFailure_zero, ← tubeFailure_zero]
  by_cases ho : outsideFailure d initial source ρ r=0 <;> simp [ho]

end SymplecticPacking.Effective.PackingCertificateCode
