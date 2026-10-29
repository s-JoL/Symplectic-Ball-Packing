import SymplecticPacking.Effective.PackingCertificateProgramJoint
import SymplecticPacking.Effective.PackingCertificateFieldCode

/-!
# The polynomial field evaluator in a runtime dimension

The exact polynomial Hamiltonian evaluator, jointly primitive in the runtime dimension.
-/

namespace SymplecticPacking.Effective.PackingPolynomialJoint
open RationalCode
set_option maxHeartbeats 500000

abbrev FieldConfig := (ℕ × List ℕ) × (ℕ × ℕ)

def pointList (d B time state : ℕ) : List ℕ :=
  PackingPolynomialCode.clipCode zeroCode PackingPolynomialCode.oneCode time ::
    (PackingStateList.stateList d state).map (PackingPolynomialCode.spatialClipCode B)

def pointCode (d B time state : ℕ) : ℕ := Encodable.encode (pointList d B time state)

theorem pointList_eq (d B time state : ℕ) :
    pointList d B time state=List.ofFn (PackingPolynomialCode.pointState d B time state) := by
  simp only [pointList,PackingPolynomialCode.pointState,List.ofFn_cons,
    ←PackingStateList.decodeState_eq_list,List.map_ofFn,Function.comp_def]

theorem pointCode_eq (d B time state : ℕ) :
    pointCode d B time state=PackingPolynomialCode.pointCode d B time state := by
  rw [pointCode,PackingPolynomialCode.pointCode,PackingStateList.encodeState_eq_list,pointList_eq]

theorem primitive_pointList :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => pointList a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hd : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.1) := Primrec.fst
  have hB : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htime := PackingPolynomialCode.primitive_clipCode.comp
    ((Primrec.const zeroCode).pair ((Primrec.const PackingPolynomialCode.oneCode).pair ht))
  have hsource := PackingStateList.primitive_stateList.comp (hd.pair hs)
  have hmap : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) =>
      (PackingStateList.stateList a.1 a.2.2.2).map (PackingPolynomialCode.spatialClipCode a.2.1)) := by
    apply Primrec.list_map hsource
    exact (PackingPolynomialCode.primitive_spatialClipCode.comp
      (hB.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp htime hmap

theorem primitive_pointCode :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => pointCode a.1 a.2.1 a.2.2.1 a.2.2.2) :=
  Primrec.encode.comp primitive_pointList

def component (n : ℕ) (program : List ℕ) (B input j : ℕ) : ℕ :=
  let point := pointCode (2*n) B (Nat.unpair input).1 (Nat.unpair (Nat.unpair input).2).1
  if j<n then derivativeEvaluate (2*n+1) (j+n+1) program point
  else negCode (derivativeEvaluate (2*n+1) (j-n+1) program point)

def fieldList (n : ℕ) (program : List ℕ) (B input : ℕ) : List ℕ :=
  (List.range (2*n)).map (component n program B input)

def fieldCode (n : ℕ) (program : List ℕ) (B input : ℕ) : ℕ :=
  Encodable.encode (fieldList n program B input)

theorem component_eq (n B input : ℕ) (program : List ℕ) (j : Fin (2*n)) :
    component n program B input j.val=PackingPolynomialCode.fieldState n program B input j := by
  by_cases h : j.val<n
  · simp only [component,PackingPolynomialCode.fieldState,if_pos h,dif_pos h,
      derivativeEvaluate_eq,pointCode_eq]
  · simp only [component,PackingPolynomialCode.fieldState,if_neg h,dif_neg h,
      derivativeEvaluate_eq,pointCode_eq]

theorem map_range_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f=List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem <;> simp

theorem fieldList_eq (n B input : ℕ) (program : List ℕ) :
    fieldList n program B input=List.ofFn (PackingPolynomialCode.fieldState n program B input) := by
  rw [fieldList,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  exact component_eq n B input program j

theorem fieldCode_eq (n B input : ℕ) (program : List ℕ) :
    fieldCode n program B input=PackingPolynomialCode.fieldCode n program B input := by
  rw [fieldCode,PackingPolynomialCode.fieldCode,PackingStateList.encodeState_eq_list,fieldList_eq]

theorem primitive_component :
    Primrec (fun a : FieldConfig × ℕ => component a.1.1.1 a.1.1.2 a.1.2.1 a.1.2.2 a.2) := by
  have hn : Primrec (fun a : FieldConfig × ℕ => a.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hp : Primrec (fun a : FieldConfig × ℕ => a.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hB : Primrec (fun a : FieldConfig × ℕ => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun a : FieldConfig × ℕ => a.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hj : Primrec (fun a : FieldConfig × ℕ => a.2) := Primrec.snd
  have hd := Primrec.nat_mul.comp (Primrec.const 2) hn
  have ht := Primrec.fst.comp (Primrec.unpair.comp hi)
  have hs := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hi)))
  have hpoint := primitive_pointCode.comp (hd.pair (hB.pair (ht.pair hs)))
  have hdim := Primrec.succ.comp hd
  have hq := Primrec.succ.comp (Primrec.nat_add.comp hj hn)
  have hq' := Primrec.succ.comp (Primrec.nat_sub.comp hj hn)
  have hgrad := primitive_derivativeEvaluate.comp ((hdim.pair hq).pair (hp.pair hpoint))
  have hgrad' := primitive_derivativeEvaluate.comp ((hdim.pair hq').pair (hp.pair hpoint))
  exact Primrec.ite (Primrec.nat_lt.comp hj hn) hgrad (primitive_negCode.comp hgrad')

theorem primitive_fieldList :
    Primrec (fun a : FieldConfig => fieldList a.1.1 a.1.2 a.2.1 a.2.2) := by
  have hlength : Primrec (fun a : FieldConfig => 2*a.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp hlength) primitive_component.to₂

theorem primitive_fieldCode :
    Primrec (fun a : FieldConfig => fieldCode a.1.1 a.1.2 a.2.1 a.2.2) :=
  Primrec.encode.comp primitive_fieldList

def universalField (n input : ℕ) : ℕ :=
  let candidate := (Nat.unpair (Nat.unpair input).2).2
  fieldCode n (PackingStateList.decodeList (Nat.unpair candidate).2) (Nat.unpair candidate).1 input

theorem universalField_eq (n input : ℕ) :
    universalField n input=PackingPolynomialCode.universalField n input := by
  simp only [universalField,PackingPolynomialCode.universalField,fieldCode_eq,
    PackingStateList.decodeList,PackingPolynomialCode.decodeProgram]

theorem primitive_universalField :
    Primrec (fun a : ℕ × ℕ => universalField a.1 a.2) := by
  have hn : Primrec (fun a : ℕ × ℕ => a.1) := Primrec.fst
  have hi : Primrec (fun a : ℕ × ℕ => a.2) := Primrec.snd
  have hc : Primrec (fun a : ℕ × ℕ => (Nat.unpair (Nat.unpair a.2).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hi)))
  have hB := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hp := PackingStateList.primitive_decodeList.comp (Primrec.snd.comp (Primrec.unpair.comp hc))
  exact primitive_fieldCode.comp ((hn.pair hp).pair (hB.pair hi))

/-- The runtime-dimension machine evaluates the clipped Hamiltonian
field exactly; the candidate remains the fixed third query argument. -/
theorem universalField_real (n B time state : ℕ) (program : List ℕ) :
    ODECode.realState (ODECode.decodeState (2*n)
      (universalField n (Nat.pair time (Nat.pair state (Nat.pair B (Encodable.encode program)))))) =
      PackingPolynomial.field n B (PackingPolynomial.programExpression program) (value time:ℝ)
        (ODECode.realState (ODECode.decodeState (2*n) state)) := by
  rw [universalField_eq]
  exact PackingPolynomialCode.universalField_real n B time state program

end SymplecticPacking.Effective.PackingPolynomialJoint
