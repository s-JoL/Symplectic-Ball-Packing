import SymplecticPacking.General.Main
import SymplecticPacking.General.MainSupport
import SymplecticPacking.General.MainFlow
import SymplecticPacking.General.MainRadius
import SymplecticPacking.General.Corollaries
import SymplecticPacking.General.Criterion
import SymplecticPacking.General.EpochQuarter
import SymplecticPacking.General.EpochStability
import SymplecticPacking.General.CompileOutput
import SymplecticPacking.Effective.PackingCertificateAlgorithm
import SymplecticPacking.Effective.PackingCertificateEpochAlgorithm
import SymplecticPacking.Explicit

/-!
# The construction

Root of the library: the modules whose declarations the entry files in `verification/` use.

* `General.Main`, `General.MainSupport`, `General.MainFlow`, `General.MainRadius`: the explicit
  Hamiltonian `packingHamiltonian n k C c s`, Theorem C, its time support, support radius and
  time-one flow;
* `General.EpochQuarter`, `General.EpochStability`: Theorem A and Proposition B;
* `General.Corollaries`, `General.Criterion`: Corollaries D, E and G;
* `General.CompileOutput`: the finite rational output `β_B · P`;
* `Effective.PackingCertificateAlgorithm`, `Effective.PackingCertificateEpochAlgorithm`: the
  machines of `verification/Computability.lean` and `verification/EpochComputability.lean`;
* `Explicit`: the `#check_explicit` and `#check_constructive` commands.

The statements themselves are in `verification/Statement.lean`.
-/
