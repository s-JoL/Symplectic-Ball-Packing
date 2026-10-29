import SymplecticPacking.Effective.Family
import verification.AxiomCheck
import SymplecticPacking.Explicit

/-!
# Square-root names

Axioms and explicitness of the square root of a named real by one oracle query and an integer
square root, with sample evaluations.
-/

#assert_publication_axioms SymplecticPacking.Effective.SqrtName.output_error
#assert_publication_axioms SymplecticPacking.Effective.SqrtName.code_names
#assert_publication_axioms SymplecticPacking.Effective.SqrtName.primitive_output
#assert_publication_axioms SymplecticPacking.Effective.SqrtName.code_recursive
#assert_publication_axioms SymplecticPacking.Effective.Family.sqrt_spec
#assert_publication_axioms SymplecticPacking.Effective.Family.sqrt_recursive
#check_explicit SymplecticPacking.Effective.SqrtName.output
#check_explicit SymplecticPacking.Effective.SqrtName.code
#check_explicit SymplecticPacking.Effective.Family.sqrt

open SymplecticPacking.Effective
open RationalCode
#eval ([0,1,2,4,10,16,100]:List ℕ).map fun k=>
  (k,value (SqrtName.code (fun _=>ofRat k) 0),value (SqrtName.code (fun _=>ofRat k) 3))
