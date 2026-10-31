import verification.Statement
import verification.Computability
import verification.EpochComputability
import verification.Executable
import verification.Audit.PaperTags

/-!
# One entry point for kernel replay

`lake env leanchecker --fresh verification.Kernel` replays this module's complete
declaration closure, including imported proofs, into a fresh Lean kernel environment.
The human-readable specification remains `verification/Problem.lean`.
-/
