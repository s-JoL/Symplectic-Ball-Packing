import SymplecticPacking.Effective.PackingCertificateStateList
import SymplecticPacking.Effective.PackingCertificatePolynomialCode

/-!
# Automatic differentiation in a runtime dimension

One primitive program for automatic differentiation in a runtime dimension.
-/

namespace SymplecticPacking.Effective.PackingPolynomialJoint
open RationalCode
set_option maxHeartbeats 500000

abbrev Config := ℕ × (ℕ × ℕ)

/-- `Config=(dimension,(derivative coordinate,state code))`; no finite type
occurs in this executable interpreter. -/
def dualStep (d j cmd state : ℕ) (stack : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let tag := (Nat.unpair cmd).1
  let payload := (Nat.unpair cmd).2
  let a := stack.getD 0 (zeroCode,zeroCode)
  let b := stack.getD 1 (zeroCode,zeroCode)
  if tag=0 then (payload,zeroCode) :: stack
  else if tag=1 then (PackingStateList.coordinate d state payload,
    if payload=j then PackingPolynomialCode.oneCode else zeroCode) :: stack
  else if tag=2 then (addCode a.1 b.1,addCode a.2 b.2) :: stack.drop 2
  else (mulCode a.1 b.1,addCode (mulCode a.2 b.1) (mulCode a.1 b.2)) :: stack.drop 2

def dualStack (d j state : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | cmd :: program => dualStep d j cmd state (dualStack d j state program)

def derivativeEvaluate (d j : ℕ) (program : List ℕ) (state : ℕ) : ℕ :=
  ((dualStack d j state program).getD 0 (zeroCode,zeroCode)).2

theorem dualStep_eq (d j cmd state : ℕ) (stack : List (ℕ × ℕ)) :
    dualStep d j cmd state stack=PackingPolynomialCode.dualStep d j cmd state stack := by
  simp only [dualStep,PackingPolynomialCode.dualStep,PackingStateList.coordinate_eq_decode,
    PackingPolynomialCode.coordinateCode]

theorem dualStack_eq (d j state : ℕ) (program : List ℕ) :
    dualStack d j state program=PackingPolynomialCode.dualStack d j state program := by
  induction program with
  | nil => rfl
  | cons cmd p ih => simp only [dualStack,PackingPolynomialCode.dualStack,dualStep_eq,ih]

theorem derivativeEvaluate_eq (d j : ℕ) (program : List ℕ) (state : ℕ) :
    derivativeEvaluate d j program state=PackingPolynomialCode.derivativeEvaluate d j program state := by
  rw [derivativeEvaluate,PackingPolynomialCode.derivativeEvaluate,dualStack_eq]

theorem primitive_dualStep :
    Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) =>
      dualStep a.1.1 a.1.2.1 a.2.1 a.1.2.2 a.2.2) := by
  have ht : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => (Nat.unpair a.2.1).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hv : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => (Nat.unpair a.2.1).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hs : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => a.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hd : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => a.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun a : Config × (ℕ × List (ℕ × ℕ)) => a.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ha := (Primrec.list_getD (zeroCode,zeroCode)).comp hs (Primrec.const 0)
  have hb := (Primrec.list_getD (zeroCode,zeroCode)).comp hs (Primrec.const 1)
  have ha0 := Primrec.fst.comp ha
  have ha1 := Primrec.snd.comp ha
  have hb0 := Primrec.fst.comp hb
  have hb1 := Primrec.snd.comp hb
  have hdrop := Primrec.list_drop.comp (Primrec.const 2) hs
  have hc := Primrec.list_cons.comp (hv.pair (Primrec.const zeroCode)) hs
  have hcoord := PackingStateList.primitive_coordinate.comp (hd.pair (hx.pair hv))
  have hvar := Primrec.list_cons.comp (hcoord.pair
    (Primrec.ite (Primrec.eq.comp hv hj) (Primrec.const PackingPolynomialCode.oneCode)
      (Primrec.const zeroCode))) hs
  have hplus := Primrec.list_cons.comp ((primitive_addCode.comp ha0 hb0).pair
    (primitive_addCode.comp ha1 hb1)) hdrop
  have hmul := Primrec.list_cons.comp ((primitive_mulCode.comp ha0 hb0).pair
    (primitive_addCode.comp (primitive_mulCode.comp ha1 hb0)
      (primitive_mulCode.comp ha0 hb1))) hdrop
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) hc
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hvar
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) hplus hmul))

theorem primitive_dualStack :
    Primrec (fun a : Config × List ℕ => dualStack a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  have hs : Primrec (fun a : (Config × List ℕ) × (ℕ × List (ℕ × ℕ)) =>
      dualStep a.1.1.1 a.1.1.2.1 a.2.1 a.1.1.2.2 a.2.2) :=
    primitive_dualStep.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const []) hs.to₂).of_eq fun a => by
    induction a.2 with
    | nil => rfl
    | cons cmd p ih => exact congrArg (dualStep a.1.1 a.1.2.1 cmd a.1.2.2) ih

theorem primitive_derivativeEvaluate :
    Primrec (fun a : (ℕ × ℕ) × (List ℕ × ℕ) =>
      derivativeEvaluate a.1.1 a.1.2 a.2.1 a.2.2) := by
  have hp : Primrec (fun a : (ℕ × ℕ) × (List ℕ × ℕ) =>
      ((a.1.1,(a.1.2,a.2.2)),a.2.1)) :=
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.fst.comp Primrec.snd)
  have hs := primitive_dualStack.comp hp
  exact Primrec.snd.comp ((Primrec.list_getD (zeroCode,zeroCode)).comp hs (Primrec.const 0))

end SymplecticPacking.Effective.PackingPolynomialJoint
