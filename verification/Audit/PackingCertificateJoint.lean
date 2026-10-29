import SymplecticPacking.Effective.PackingCertificateFieldJoint
import SymplecticPacking.Explicit

/-!
# The uniform field program

Axioms and explicitness of the field program that takes the dimension as input, with sample
evaluations in several dimensions.
-/

open SymplecticPacking.Effective
open RationalCode PackingPolynomial

#print axioms PackingPolynomialJoint.derivativeEvaluate_eq
#print axioms PackingPolynomialJoint.primitive_derivativeEvaluate
#print axioms PackingPolynomialJoint.pointCode_eq
#print axioms PackingPolynomialJoint.fieldCode_eq
#print axioms PackingPolynomialJoint.universalField_eq
#print axioms PackingPolynomialJoint.primitive_universalField
#print axioms PackingPolynomialJoint.universalField_real

#check_explicit PackingPolynomialJoint.derivativeEvaluate
#check_explicit PackingPolynomialJoint.pointCode
#check_explicit PackingPolynomialJoint.fieldCode
#check_explicit PackingPolynomialJoint.universalField

-- Dimension and derivative coordinate are ordinary input naturals.
#eval (List.range 4).map fun d =>
  let state := Encodable.encode (List.replicate d (PackingPolynomialCode.natCode 3))
  value (PackingPolynomialJoint.derivativeEvaluate d 0
    (expressionProgram (.mul (.var 0) (.var 0))) state)

-- One field program runs in several symplectic dimensions, including zero.
#eval (List.range 4).map fun n =>
  let initial := Encodable.encode (List.replicate (2*n) zeroCode)
  let candidate := Nat.pair 4 (Encodable.encode (expressionProgram (.var (n+1))))
  let result := PackingPolynomialJoint.universalField n
    (Nat.pair zeroCode (Nat.pair initial candidate))
  (PackingStateList.stateList (2*n) result).map value
