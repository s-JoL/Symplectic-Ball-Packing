import SymplecticPacking.HighDim.Handle.NativeModelAgreement
import SymplecticPacking.HighDim.Handle.QuadricRawHandlePaths
import SymplecticPacking.HighDim.Handle.SmallRawProvider
import SymplecticPacking.HighDim.Handle.MixedRawProvider

/-!
# Agreement of scalar raw data with the toric models

Scalar raw data agree with the corresponding geometric toric models.
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
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix

/-- A geometric reference used only in the specification and agreement proofs. -/
def quadricScalarSemanticModel (m n q ℓ : ℕ) (Δ : Polytope n q) (κ : Moments n → ℝ) :
    ToricModel (Surface m) n q where
  Δ := Δ
  base := projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)
  Λ := curveFSForm (parameters m) (1/Real.pi)
  dens z := κ z.1
  Γ p := κ p • curveFSPrimitive (parameters m) (1/Real.pi)
  handle := BranchSmall.quadricHandleData m
  hb := (BranchSmall.quadricHandleData m).width/2
  hδ := 1/4

theorem quadricScalarRawModel_agreement (m n q ℓ : ℕ) (Δ : Polytope n q) (κ : Moments n → ℝ)
    (floor : ℝ) : RawModelAgreement (quadricScalarRawModel m n q ℓ Δ κ floor)
      (quadricScalarSemanticModel m n q ℓ Δ κ) where
  polytope_eq := rfl
  base_eq := rfl
  primitive_eq p := by
    rw [show (quadricScalarRawModel m n q ℓ Δ κ floor).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion m ℓ]
    exact quadricScalarRawModel_physicalPrimitive m n q ℓ Δ κ floor p
  reference_eq := by
    rw [show (quadricScalarRawModel m n q ℓ Δ κ floor).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion m ℓ]
    exact quadricReferenceForm_semantic m
  handle := by
    rw [show (quadricScalarRawModel m n q ℓ Δ κ floor).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion m ℓ]
    exact quadricRawHandle_agreement m (b := (1:ℝ)/16) (by norm_num) (by change 1/16<(1:ℝ)/8; norm_num)
  hb_eq := by
    change (1:ℝ)/16=(BranchSmall.quadricHandleData m).width/2
    change (1:ℝ)/16=(BranchSmall.explicitCylinderWidth m/2)/2
    norm_num [BranchSmall.explicitCylinderWidth]
  hδ_eq := rfl

theorem smallRawModel_agreement {k : ℕ} (m : ℕ) (ρ : Fin k → ℝ) :
    RawModelAgreement (smallRawModel m ρ) (BranchSmall.quadricModel m ρ) :=
  quadricScalarRawModel_agreement m (m+2) 1 (BranchSmall.baseLevel m ρ)
    (Polytope.simplex (m+2) (BranchSmall.hgt (m+3) ρ)) (equalNormalCoefficient (m+2) 2)
    (1-2*BranchSmall.hgt (m+3) ρ)

/-- This reference is definitionally the mixed model at `mixedRawLevel`; no import of the consumer is needed. -/
theorem mixedRawModel_agreement {k : ℕ} (q : ℕ) (a : ℝ) (r : Fin k → ℝ) :
    RawModelAgreement (mixedRawModel q a r)
      (quadricScalarSemanticModel q (q+3) 2 (mixedRawLevel q a r)
        (BranchLargeHigh.Mixed.polytope (q+2) a r) (largeNormalCoefficient (q+2))) :=
  quadricScalarRawModel_agreement q (q+3) 2 (mixedRawLevel q a r)
    (BranchLargeHigh.Mixed.polytope (q+2) a r) (largeNormalCoefficient (q+2))
    ((1-BranchLargeHigh.Mixed.h1 (q+2) a r)*(1-2*BranchLargeHigh.Mixed.h2 (q+2) a r))

theorem quadricScalarSemanticModel_area_eq (m n q ℓ : ℕ) (Δ : Polytope n q) (κ : Moments n → ℝ)
    (hS : (quadricScalarSemanticModel m n q ℓ Δ κ).Spec) :
    quadricScalarOuterArea m n ℓ κ=(quadricScalarSemanticModel m n q ℓ Δ κ).baseArea hS := by
  funext p
  unfold quadricScalarOuterArea
  rw [quadricScalar_semantic]
  rfl

end SymplecticPacking.HighDim.ToricPackingStages
