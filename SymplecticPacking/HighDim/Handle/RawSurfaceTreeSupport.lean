import SymplecticPacking.HighDim.Handle.RawSurfaceTree
import SymplecticPacking.HighDim.Handle.RawAmbientSupport

/-!
# Compact support of the raw tree transfers

Compact support of all finite raw tree transfers.
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

theorem edgePrimitive_zero (hG : D.Geometry) (i : Fin D.size)
    (x : M) (hx : x ∉ D.support) : D.edgePrimitive i x = 0 := by
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
  have hxB : x ∉ B.box.compactCarrier := fun hh => hx (mem_iUnion.mpr ⟨i.succ,hh⟩)
  have hxC : x ∉ C.box.compactCarrier := fun hh => hx (mem_iUnion.mpr ⟨D.parentIndex i,hh⟩)
  have hleft := B.difference_zero (hG.box_smooth i.succ) (hG.box_inverse i.succ)
    (B.unitBump_smooth (hG.box_smooth i.succ)) (O.unitBump_smooth (hG.overlap_smooth i))
    B.unitSupport_compact O.unitSupport_compact B.unitSupport_subset hOB
    (fun x hx => B.unitBump_zero hx) (fun x hx => O.unitBump_zero hx)
    ((B.unitBump_mass (hG.box_inverse i.succ)).trans hBm.symm) x hxB
  have hright := C.difference_zero (hG.box_smooth (D.parentIndex i))
    (hG.box_inverse (D.parentIndex i))
    (O.unitBump_smooth (hG.overlap_smooth i)) (C.unitBump_smooth (hG.box_smooth (D.parentIndex i)))
    O.unitSupport_compact C.unitSupport_compact hOC C.unitSupport_subset
    (fun x hx => O.unitBump_zero hx) (fun x hx => C.unitBump_zero hx)
    (hCm.trans (C.unitBump_mass (hG.box_inverse (D.parentIndex i))).symm) x hxC
  change B.formPrimitive _ x+C.formPrimitive _ x=0
  rw [hleft,hright]
  exact add_zero _

theorem treePrimitive_zero (hG : D.Geometry) (i : Fin (D.size+1))
    (x : M) (hx : x ∉ D.support) : D.treePrimitive i x = 0 := by
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hz : i.val = 0
    · rw [treePrimitive,dif_pos hz]
      rfl
    · let j : Fin D.size := ⟨i.val-1, by have := i.isLt; omega⟩
      have hsucc : j.succ = i := Fin.ext (by dsimp [j];omega)
      have hp : (D.parentIndex j).val < n := by
        rw [← hi]
        exact (D.parentIndex_lt j).trans_eq (congrArg Fin.val hsucc)
      rw [treePrimitive,dif_neg hz]
      change D.edgePrimitive j x+D.treePrimitive (D.parentIndex j) x=0
      rw [D.edgePrimitive_zero hG j x hx,ih _ hp _ rfl]
      exact add_zero _

end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
