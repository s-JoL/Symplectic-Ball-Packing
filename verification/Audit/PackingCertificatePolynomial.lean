import SymplecticPacking.Effective.PackingCertificateFieldCode
import SymplecticPacking.Effective.PackingCertificateFieldJoint
import SymplecticPacking.Effective.PackingCertificateInput
import SymplecticPacking.Effective.PackingCertificateOutput
import SymplecticPacking.Effective.PackingCertificateSoundness
import SymplecticPacking.Explicit

/-!
# Polynomial programs and their fields

Axioms and explicitness of the straight-line polynomial programs, their exact derivatives and
the Hamiltonian field, with sample evaluations.
-/

open SymplecticPacking.Effective
open PackingPolynomial PackingPolynomialCode RationalCode

#print axioms derivative_correct
#print axioms eval_lipschitz
#print axioms budget_bounds
#print axioms toPolynomial_surjective
#print axioms programExpression_expressionProgram
-- Primitive recursion is proved for the runtime-dimension evaluator; the equality
-- theorems connect it to the evaluator audited and evaluated in this file.
#print axioms PackingPolynomialJoint.derivativeEvaluate_eq
#print axioms PackingPolynomialJoint.primitive_derivativeEvaluate
#print axioms derivativeEvaluate_value
#print axioms primitive_programBudget
#print axioms programBudget_correct
#print axioms exists_curve_bounds
#print axioms PackingPolynomialJoint.universalField_eq
#print axioms PackingPolynomialJoint.primitive_universalField
#print axioms universalField_real
#print axioms PackingCertificate.outerBall_contains
#print axioms output_exists_global
#print axioms field_eq_output_of_plateau
#print axioms PackingCertificate.finite_cover_sound

#check_explicit expressionProgram
#check_explicit derivativeEvaluate
#check_explicit programBudget
#check_explicit universalField
#check_explicit output
#check_explicit PackingCertificate.outerRadiusCode
#check_explicit PackingCertificate.innerRadiusCode
#check_explicit PackingCertificate.capacityRadiusEvaluator

-- Exact automatic differentiation: d(x^2)/dx at x=3 is 6.
#eval value (derivativeEvaluate 1 0
  (expressionProgram (.mul (.var 0) (.var 0)))
  (ODECode.encodeState 1 (fun _ => natCode 3)))
#eval programBudget 2 (expressionProgram (.mul (.var 0) (.var 0)))

-- Universal Hamiltonian field: H(t,q,p)=p gives (qdot,pdot)=(1,0).
#eval
  let initial := ODECode.encodeState 2 (fun _ => zeroCode)
  let candidate := Nat.pair 4 (Encodable.encode (expressionProgram (.var 2)))
  let result := ODECode.decodeState 2 (universalField 1 (Nat.pair zeroCode (Nat.pair initial candidate)))
  List.ofFn (fun j : Fin 2 => value (result j))
