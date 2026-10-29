import SymplecticPacking.HighDim.Handle.QuadricCollarBounds
import SymplecticPacking.BranchLarge3.CubicCollarBounds
import SymplecticPacking.Effective.RationalArithmetic
import SymplecticPacking.Explicit
import verification.AxiomCheck

/-!
# Collar bounds and the rational reciprocal

Axiom gates for the collar-loss bounds of the quadric and cubic collars and for the rational
reciprocal `invCode`; explicitness of `invCode` and of the cubic collar level, with sample
evaluations of `invCode`.
-/

#assert_publication_axioms SymplecticPacking.HighDim.ToricPackingStages.quadric_collar_level_two
#assert_publication_axioms SymplecticPacking.HighDim.ToricPackingStages.quadric_exhaustion_inner_radius
#assert_publication_axioms SymplecticPacking.HighDim.ToricPackingStages.quadric_collar_numeric_bound
#assert_publication_axioms SymplecticPacking.HighDim.ToricPackingStages.quadric_collar_inner_defect
#assert_publication_axioms SymplecticPacking.Effective.RationalCode.value_invCode
#assert_publication_axioms SymplecticPacking.Effective.RationalCode.primitive_invCode
#check_explicit SymplecticPacking.Effective.RationalCode.invCode

open SymplecticPacking.Effective.RationalCode in
#eval [value (invCode (ofRat (3/2))), value (invCode (ofRat (-3/2))), value (invCode zeroCode)]
#assert_publication_axioms SymplecticPacking.BranchLarge3.cubicCollarMass_lt
#check_explicit SymplecticPacking.BranchLarge3.cubicCollarLevel
