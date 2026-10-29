import SymplecticPacking.Effective.PackingCertificatePolynomial
import SymplecticPacking.Effective.ODECode

/-!
# Evaluation of finite polynomial programs

Primitive-recursive finite polynomial program evaluation.
-/

namespace SymplecticPacking.Effective.PackingPolynomialCode

open RationalCode PackingPolynomial
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def coordinateCode (d state i : ℕ) : ℕ :=
  (List.ofFn fun j : Fin d => ODECode.decodeState d state j).getD i zeroCode

theorem coordinateCode_value (d state i : ℕ) :
    value (coordinateCode d state i) =
      coordinates (ODECode.rationalState (ODECode.decodeState d state)) i := by
  by_cases h : i<d
  · simp [coordinateCode, coordinates, h, ODECode.rationalState]
  · have hz : (List.ofFn fun j : Fin d => ODECode.decodeState d state j).length ≤ i := by
      simpa only [List.length_ofFn] using Nat.le_of_not_gt h
    rw [coordinateCode, List.getD_eq_default _ zeroCode hz, value_zeroCode]
    simp [coordinates, h]

def oneCode : ℕ := encode 1 0 0

def dualStep (d j cmd state : ℕ) (stack : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let tag := (Nat.unpair cmd).1
  let payload := (Nat.unpair cmd).2
  let a := stack.getD 0 (zeroCode,zeroCode)
  let b := stack.getD 1 (zeroCode,zeroCode)
  if tag=0 then (payload,zeroCode) :: stack
  else if tag=1 then (coordinateCode d state payload,
    if payload=j then oneCode else zeroCode) :: stack
  else if tag=2 then (addCode a.1 b.1,addCode a.2 b.2) :: stack.drop 2
  else (mulCode a.1 b.1,addCode (mulCode a.2 b.1) (mulCode a.1 b.2)) :: stack.drop 2

def dualStack (d j state : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | cmd :: program => dualStep d j cmd state (dualStack d j state program)

/-- First partial derivative by exact automatic differentiation of the finite
program. This is an arithmetic program, not a derivative-value oracle. -/
def derivativeEvaluate (d j : ℕ) (program : List ℕ) (state : ℕ) : ℕ :=
  ((dualStack d j state program).getD 0 (zeroCode,zeroCode)).2

theorem mapped_getD {α β γ : Type*} (f : α → γ) (g : β → γ)
    (da : α) (db : β) {as : List α} {bs : List β}
    (hd : f da=g db) (h : as.map f=bs.map g) (i : ℕ) :
    f (as.getD i da)=g (bs.getD i db) := by
  calc
    _ = (as.map f).getD i (f da) := (List.getD_map as da f).symm
    _ = (bs.map g).getD i (g db) := by rw [h, hd]
    _ = _ := List.getD_map bs db g

def jetValue (p : ℕ × ℕ) : ℚ × ℚ := (value p.1,value p.2)
def jetExpression (d state j : ℕ) (e : Expr) : ℚ × ℚ :=
  (rationalEval d e (ODECode.rationalState (ODECode.decodeState d state)),
    rationalEval d (derivative j e) (ODECode.rationalState (ODECode.decodeState d state)))

theorem dualStep_value (d state cmd : ℕ) (j : Fin d)
    (es : List Expr) (cs : List (ℕ × ℕ))
    (h : cs.map jetValue=es.map (jetExpression d state j.val)) :
    (dualStep d j.val cmd state cs).map jetValue=
      (expressionStep cmd es).map (jetExpression d state j.val) := by
  have hzero : jetValue (zeroCode,zeroCode)=jetExpression d state j.val zero := by
    simp [jetValue, jetExpression, rationalEval, eval, derivative, zero, value_zeroCode]
  have h0 := mapped_getD jetValue (jetExpression d state j.val)
    (zeroCode,zeroCode) zero hzero h 0
  have h1 := mapped_getD jetValue (jetExpression d state j.val)
    (zeroCode,zeroCode) zero hzero h 1
  have h00 := congrArg Prod.fst h0
  have h01 := congrArg Prod.snd h0
  have h10 := congrArg Prod.fst h1
  have h11 := congrArg Prod.snd h1
  have hd : (cs.drop 2).map jetValue=(es.drop 2).map (jetExpression d state j.val) := by
    simpa only [List.map_drop] using congrArg (List.drop 2) h
  simp only [jetValue, jetExpression] at h00 h01 h10 h11
  simp only [dualStep, expressionStep]
  split_ifs <;> simp_all [jetValue, jetExpression, rationalEval, eval, derivative,
    zero, one, oneCode, value_encode, value_zeroCode, value_addCode, value_mulCode,
    coordinateCode_value]

theorem dualStack_value (d state : ℕ) (j : Fin d) (program : List ℕ) :
    (dualStack d j.val state program).map jetValue=
      (expressionStack program).map (jetExpression d state j.val) := by
  induction program with
  | nil => rfl
  | cons cmd program ih => exact dualStep_value d state cmd j _ _ ih

theorem derivativeEvaluate_value (d state : ℕ) (j : Fin d) (program : List ℕ) :
    value (derivativeEvaluate d j.val program state)=
      rationalEval d (derivative j.val (programExpression program))
        (ODECode.rationalState (ODECode.decodeState d state)) := by
  have hzero : jetValue (zeroCode,zeroCode)=jetExpression d state j.val zero := by
    simp [jetValue, jetExpression, rationalEval, eval, derivative, zero, value_zeroCode]
  have hh := mapped_getD jetValue (jetExpression d state j.val)
    (zeroCode,zeroCode) zero hzero (dualStack_value d state j program) 0
  exact congrArg Prod.snd hh

def budgetStep (R cmd : ℕ) (stack : List ℕ) : List ℕ :=
  let tag := (Nat.unpair cmd).1
  let payload := (Nat.unpair cmd).2
  if tag=0 then (constantBound payload+1) :: stack
  else if tag=1 then (R+2) :: stack
  else if tag=2 then (stack.getD 0 2+stack.getD 1 2) :: stack.drop 2
  else (4*stack.getD 0 2*stack.getD 1 2) :: stack.drop 2

def budgetStack (R : ℕ) : List ℕ → List ℕ
  | [] => []
  | cmd :: program => budgetStep R cmd (budgetStack R program)

def programBudget (R : ℕ) (program : List ℕ) : ℕ := (budgetStack R program).getD 0 2

theorem primitive_budgetStep :
    Primrec (fun a : ℕ × (ℕ × List ℕ) => budgetStep a.1 a.2.1 a.2.2) := by
  have ht : Primrec (fun a : ℕ × (ℕ × List ℕ) => (Nat.unpair a.2.1).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hv : Primrec (fun a : ℕ × (ℕ × List ℕ) => (Nat.unpair a.2.1).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hs : Primrec (fun a : ℕ × (ℕ × List ℕ) => a.2.2) := Primrec.snd.comp Primrec.snd
  have ha := (Primrec.list_getD 2).comp hs (Primrec.const 0)
  have hb := (Primrec.list_getD 2).comp hs (Primrec.const 1)
  have hd := Primrec.list_drop.comp (Primrec.const 2) hs
  have hc := Primrec.list_cons.comp
    (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_add.comp
      (primitive_positiveNumerator.comp hv) (primitive_negativeNumerator.comp hv)))) hs
  have hx := Primrec.list_cons.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)) hs
  have hp := Primrec.list_cons.comp (Primrec.nat_add.comp ha hb) hd
  have hm := Primrec.list_cons.comp
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) ha) hb) hd
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) hc
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hx
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) hp hm))

theorem primitive_budgetStack : Primrec (fun a : ℕ × List ℕ => budgetStack a.1 a.2) := by
  have hs : Primrec (fun a : (ℕ × List ℕ) × (ℕ × (List ℕ × List ℕ)) =>
      budgetStep a.1.1 a.2.1 a.2.2.2) :=
    primitive_budgetStep.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.list_rec Primrec.snd (Primrec.const []) hs.to₂).of_eq fun a => by
    induction a.2 with
    | nil => rfl
    | cons cmd p ih => exact congrArg (budgetStep a.1 cmd) ih

theorem primitive_programBudget : Primrec₂ programBudget :=
  (Primrec.list_getD 2).comp primitive_budgetStack (Primrec.const 0)

theorem budgetStack_correct (R : ℕ) (program : List ℕ) :
    budgetStack R program=(expressionStack program).map (budget R) := by
  induction program with
  | nil => rfl
  | cons cmd program ih =>
      have hz : budget R zero=2 := by
        simp [budget, zero, constantBound, zeroCode, positiveNumerator, negativeNumerator, encode]
      have hmap : (budgetStack R program).map id=(expressionStack program).map (budget R) := by
        simpa only [List.map_id] using ih
      have h0 := mapped_getD id (budget R) 2 zero hz.symm hmap 0
      have h1 := mapped_getD id (budget R) 2 zero hz.symm hmap 1
      have hd : (budgetStack R program).drop 2=
          ((expressionStack program).drop 2).map (budget R) := by
        simpa only [List.map_drop] using congrArg (List.drop 2) ih
      simp only [budgetStack, expressionStack, budgetStep, expressionStep]
      split_ifs <;> simp_all [budget]

theorem programBudget_correct (R : ℕ) (program : List ℕ) :
    programBudget R program=budget R (programExpression program) := by
  have hz : budget R zero=2 := by
    simp [budget, zero, constantBound, zeroCode, positiveNumerator, negativeNumerator, encode]
  exact mapped_getD id (budget R) 2 zero hz.symm
    (by simpa only [List.map_id] using budgetStack_correct R program) 0

end SymplecticPacking.Effective.PackingPolynomialCode
