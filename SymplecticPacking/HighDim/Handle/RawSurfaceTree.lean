import SymplecticPacking.HighDim.Handle.RawSurfacePresentation
import SymplecticPacking.HighDim.Handle.RawAmbientDifference

/-!
# Correctness of the raw mass-transfer tree

Correctness of the finite raw-coordinate mass-transfer tree.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)

/-- Local smooth compatibility and strictly positive transition Jacobians on each edge.
These assertions verify coordinate data; none specifies a primitive. -/
structure Geometry : Prop where
  box_smooth : ∀ i, (D.boxes i).box.Smooth
  box_inverse : ∀ i, ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target
  overlap_smooth : ∀ i, (D.overlap i).box.Smooth
  overlap_inverse : ∀ i, ContDiffOn ℝ ∞ (D.overlap i).inverseAmbient (D.overlap i).box.chart.target
  child_positive : ∀ i z, z ∈ (D.overlap i).box.chart '' (D.overlap i).unitSupport →
    0 < (fderiv ℝ ((D.boxes i.succ).transition (D.overlap i)) z).det
  parent_positive : ∀ i z, z ∈ (D.overlap i).box.chart '' (D.overlap i).unitSupport →
    0 < (fderiv ℝ ((D.boxes (D.parentIndex i)).transition (D.overlap i)) z).det

theorem edgePrimitive_isPrimitive (hG : D.Geometry) (i : Fin D.size) :
    RawIsPrimitive D.inclusion
      ((D.boxes i.succ).unitBump-(D.boxes (D.parentIndex i)).unitBump) (D.edgePrimitive i) := by
  let B := D.boxes i.succ
  let C := D.boxes (D.parentIndex i)
  let O := D.overlap i
  have hOB : O.unitSupport ⊆ B.box.carrier :=
    O.unitSupport_subset.trans (O.box.carrier_subset_compactCarrier.trans (D.overlap_child i))
  have hOC : O.unitSupport ⊆ C.box.carrier :=
    O.unitSupport_subset.trans (O.box.carrier_subset_compactCarrier.trans (D.overlap_parent i))
  have hBm : B.mass O.unitBump = 1 := O.unitBump_mass_in B
    ((D.box_inclusion i.succ).trans (D.overlap_inclusion i).symm)
    (hG.overlap_inverse i) (hG.box_inverse i.succ)
    (fun x hx => (hOB hx).1) (hG.child_positive i)
  have hCm : C.mass O.unitBump = 1 := O.unitBump_mass_in C
    ((D.box_inclusion (D.parentIndex i)).trans (D.overlap_inclusion i).symm)
    (hG.overlap_inverse i) (hG.box_inverse (D.parentIndex i))
    (fun x hx => (hOC hx).1) (hG.parent_positive i)
  have hleft := B.difference_isPrimitive (hG.box_smooth i.succ) (hG.box_inverse i.succ)
    (B.unitBump_smooth (hG.box_smooth i.succ)) (O.unitBump_smooth (hG.overlap_smooth i))
    (B.supportedForm_skew B.unitBumpCoefficient) (O.supportedForm_skew O.unitBumpCoefficient)
    B.unitSupport_compact O.unitSupport_compact B.unitSupport_subset hOB
    (fun x hx => B.unitBump_zero hx) (fun x hx => O.unitBump_zero hx)
    ((B.unitBump_mass (hG.box_inverse i.succ)).trans hBm.symm)
  have hright := C.difference_isPrimitive (hG.box_smooth (D.parentIndex i))
    (hG.box_inverse (D.parentIndex i))
    (O.unitBump_smooth (hG.overlap_smooth i)) (C.unitBump_smooth (hG.box_smooth (D.parentIndex i)))
    (O.supportedForm_skew O.unitBumpCoefficient) (C.supportedForm_skew C.unitBumpCoefficient)
    O.unitSupport_compact C.unitSupport_compact hOC C.unitSupport_subset
    (fun x hx => O.unitBump_zero hx) (fun x hx => C.unitBump_zero hx)
    (hCm.trans (C.unitBump_mass (hG.box_inverse (D.parentIndex i))).symm)
  change RawIsPrimitive (D.boxes i.succ).inclusion _ _ at hleft
  rw [D.box_inclusion i.succ] at hleft
  change RawIsPrimitive (D.boxes (D.parentIndex i)).inclusion _ _ at hright
  rw [D.box_inclusion (D.parentIndex i)] at hright
  have he : (B.unitBump-O.unitBump)+(O.unitBump-C.unitBump) = B.unitBump-C.unitBump := by abel
  exact he ▸ hleft.add hright

theorem treePrimitive_isPrimitive (hG : D.Geometry) (i : Fin (D.size+1)) :
    RawIsPrimitive D.inclusion ((D.boxes i).unitBump-(D.boxes D.root).unitBump)
      (D.treePrimitive i) := by
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hz : i.val = 0
    · have he : i = D.root := Fin.ext hz
      subst i
      rw [treePrimitive, dif_pos (show D.root.val = 0 from rfl)]
      have hf : (D.boxes D.root).unitBump-(D.boxes D.root).unitBump = 0 := by
        funext x
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        change (D.boxes D.root).unitBump x u v-(D.boxes D.root).unitBump x u v = 0
        ring
      rw [hf]
      exact RawIsPrimitive.zero _
    · let j : Fin D.size := ⟨i.val-1, by have := i.isLt; omega⟩
      have hsucc : j.succ = i := Fin.ext (by dsimp [j]; omega)
      have hp : (D.parentIndex j).val < n := by
        rw [← hi]
        exact (D.parentIndex_lt j).trans_eq (congrArg Fin.val hsucc)
      have hparent := ih (D.parentIndex j).val hp (D.parentIndex j) rfl
      have hh := (D.edgePrimitive_isPrimitive hG j).add hparent
      have he : ((D.boxes j.succ).unitBump-(D.boxes (D.parentIndex j)).unitBump)+
          ((D.boxes (D.parentIndex j)).unitBump-(D.boxes D.root).unitBump) =
          (D.boxes i).unitBump-(D.boxes D.root).unitBump := by
        rw [hsucc]
        abel
      rw [treePrimitive, dif_neg hz]
      exact he ▸ hh

end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
