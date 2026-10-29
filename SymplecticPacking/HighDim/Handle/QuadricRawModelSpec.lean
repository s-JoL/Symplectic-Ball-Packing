import SymplecticPacking.HighDim.Handle.QuadricRawModel
import SymplecticPacking.HighDim.Handle.QuadricCutMass

/-!
# Semantic identification of the scalar quadric raw models

Semantic identifications of the scalar raw models; these are proof-only bridges.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quadricRawHandle_width (m : ℕ) :
    (quadricRawHandle m).width=(BranchSmall.quadricHandleData m).width := by
  change (1:ℝ)/8=BranchSmall.explicitCylinderWidth m/2
  norm_num [BranchSmall.explicitCylinderWidth]

theorem quadricRawHandle_target (m : ℕ) :
    (quadricRawHandle m).target=(BranchSmall.quadricHandleData m).chart.target := by
  ext x
  exact QuadricRawDensity.nativeSheet_iff m x

theorem quadricRawHandle_forward (m : ℕ) :
    (quadricRawHandle m).forward=(BranchSmall.quadricHandleData m).chart := rfl

theorem quadricRawHandle_inverse (m : ℕ) :
    (quadricRawHandle m).inverse=(BranchSmall.quadricHandleData m).chart.symm := by
  funext x
  exact (transverseCylinder_symm_apply m x).symm

theorem quadricRawHandle_dual (m : ℕ) :
    semanticOneForm (Subtype.val : Surface m → Affine (m+2)) (quadricRawHandle m).dual=
      (BranchSmall.quadricHandleData m).dual := by
  funext x
  exact (QuadricRawDual.correctedDual_pullback m x).symm

theorem quadricRawHandle_radial (m : ℕ) {b : ℝ} (hb : 0<b) (hbw : b<(quadricRawHandle m).width) :
    semanticOneForm (Subtype.val : Surface m → Affine (m+2)) ((quadricRawHandle m).radial b)=
      (BranchSmall.quadricHandleData m).radial b := by
  funext x
  exact (QuadricRawDensity.radial_pullback m hb (hbw.trans_eq (quadricRawHandle_width m)) x).symm

theorem quadricScalarRawModel_physicalPrimitive (m n q ℓ : ℕ) (Δ : Polytope n q)
    (κ : Moments n → ℝ) (floor : ℝ) (p : Moments n) :
    semanticOneForm (Subtype.val : Surface m → Affine (m+2))
      ((quadricScalarRawModel m n q ℓ Δ κ floor).physicalPrimitive p)=
      κ p • curveFSPrimitive (parameters m) (1/Real.pi) := by
  funext x
  exact (SymplecticPacking.BranchSmall.RawQuadric.scaledPrimitive_eq_raw (parameters m) (1/Real.pi) κ p x).symm

end SymplecticPacking.HighDim.ToricPackingStages
