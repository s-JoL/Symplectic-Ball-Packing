import SymplecticPacking.Effective.PackingCertificateGridJointCore
import SymplecticPacking.Effective.PackingCertificateStateList

/-!
# The runtime grid program

The runtime grid program agrees exactly with the verified fixed-dimension grid.
-/

namespace SymplecticPacking.Effective.PackingGridJoint
theorem boxNodeCode_eq (d Q m i : ℕ) :
    boxNodeCode d Q m i=PackingCertificate.boxNodeCode d Q m i := by
  rw [PackingCertificate.boxNodeCode,PackingStateList.encodeState_eq_list,
    boxNodeCode,boxNodeCodes_eq]

end SymplecticPacking.Effective.PackingGridJoint
