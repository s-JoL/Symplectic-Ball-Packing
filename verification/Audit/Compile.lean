import SymplecticPacking.General.CompileOutput
import verification.AxiomCheck
import SymplecticPacking.Explicit

/-!
# The finite compilation

The general finite-output theorem `General.Compile.main_finite` (stated independently of the
geometric branches) and explicitness of its output `compileOutput`.
-/

#assert_publication_axioms SymplecticPacking.General.Compile.main_finite
#check_explicit SymplecticPacking.General.Compile.compileOutput
