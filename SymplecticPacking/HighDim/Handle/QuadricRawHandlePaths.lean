import SymplecticPacking.HighDim.Handle.RawHandlePaths
import SymplecticPacking.HighDim.Handle.QuadricRawModelSpec

/-!
# Path agreement for the quadric handle

The quadric handle satisfies the proof-only path agreement.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold

theorem quadricRawHandle_agreement (m : ℕ) {b : ℝ}
    (hb : 0<b) (hbw : b<(quadricRawHandle m).width) :
    (quadricRawHandle m).Agreement (Subtype.val : Surface m → Affine (m+2))
      (BranchSmall.quadricHandleData m) b where
  target_eq := quadricRawHandle_target m
  forward_eq := quadricRawHandle_forward m
  inverse_eq := quadricRawHandle_inverse m
  dual_eq := quadricRawHandle_dual m
  radial_eq := quadricRawHandle_radial m hb hbw

end SymplecticPacking.HighDim.ToricPackingStages
