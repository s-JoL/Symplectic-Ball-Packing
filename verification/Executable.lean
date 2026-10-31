import SymplecticPacking.Effective.ExecutablePacking
import verification.AxiomCheck
import SymplecticPacking.Explicit

/-!
The compiled reference algorithm returns a finite rational radius and polynomial
code together with the full `EpochSpecR` proof. These gates check its transitive
axioms and its erased runtime dependency closure, including decidable searches.
-/

#assert_publication_axioms NativePacking.solveRational
#assert_publication_axioms NativePacking.solveName
#assert_publication_axioms NativePacking.checkStage_iff
#assert_publication_axioms NativePacking.stage_epoch_spec
#check_constructive NativePacking.solveRational
#check_constructive NativePacking.solveName
