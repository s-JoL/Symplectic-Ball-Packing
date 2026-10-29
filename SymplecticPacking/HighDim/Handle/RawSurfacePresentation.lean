import SymplecticPacking.HighDim.Handle.RawAmbientBoxPrimitive
import SymplecticPacking.HighDim.Handle.RawFinitePartition

/-!
# Raw surface presentations on an overlap tree

Finite coordinate-integral algorithms on a raw overlap tree.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

/-- Only finite coordinate and overlap data are inputs. Every analytic operation below
is a fixed formula; neither a primitive nor a flow is a field of this structure. -/
structure RawSurfacePresentation (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (U : Set M) where
  size : ℕ
  inclusion : M → E
  boxes : Fin (size+1) → RawAmbientBox E M
  box_inclusion : ∀ i, (boxes i).inclusion = inclusion
  inside : ∀ i, (boxes i).box.compactCarrier ⊆ U
  parent : (i : Fin size) → Fin (i.val+1)
  overlap : Fin size → RawAmbientBox E M
  overlap_inclusion : ∀ i, (overlap i).inclusion = inclusion
  overlap_child : ∀ i, (overlap i).box.compactCarrier ⊆ (boxes i.succ).box.carrier
  overlap_parent : ∀ i, (overlap i).box.compactCarrier ⊆
    (boxes ⟨(parent i).val, by have := (parent i).isLt; have := i.isLt; omega⟩).box.carrier

namespace RawSurfacePresentation
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] {U : Set M} (D : RawSurfacePresentation E M U)

def root : Fin (D.size+1) := 0

def parentIndex (i : Fin D.size) : Fin (D.size+1) :=
  ⟨(D.parent i).val, by have := (D.parent i).isLt; have := i.isLt; omega⟩

omit [T2Space M] in
theorem parentIndex_lt (i : Fin D.size) : (D.parentIndex i).val < i.succ.val :=
  (D.parent i).isLt

/-- The two explicit coordinate integrals transferring a child bump through an overlap. -/
def edgePrimitive (i : Fin D.size) : M → E →L[ℝ] ℝ :=
  (D.boxes i.succ).formPrimitive
    ((D.boxes i.succ).unitBump - (D.overlap i).unitBump) +
  (D.boxes (D.parentIndex i)).formPrimitive
    ((D.overlap i).unitBump - (D.boxes (D.parentIndex i)).unitBump)

def treePrimitive (i : Fin (D.size+1)) : M → E →L[ℝ] ℝ :=
  if h : i.val = 0 then 0 else
    let j : Fin D.size := ⟨i.val-1, by have := i.isLt; omega⟩
    D.edgePrimitive j + treePrimitive (D.parentIndex j)
termination_by i.val
decreasing_by
  have hp := D.parentIndex_lt (⟨i.val-1, by have := i.isLt; omega⟩ : Fin D.size)
  dsimp only [Fin.val_succ] at hp
  omega

def support : Set M := ⋃ i, (D.boxes i).box.compactCarrier

theorem support_compact : IsCompact D.support :=
  isCompact_iUnion fun i => (D.boxes i).box.compactCarrier_compact

theorem support_inside : D.support ⊆ U := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact D.inside i hi

def partitionWeight (i : Fin (D.size+1)) : M → ℝ :=
  RawBoxFamily.partitionWeight (fun j => (D.boxes j).box) i

def weightedForm (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (i : Fin (D.size+1))
    (x : M) : E →L[ℝ] E →L[ℝ] ℝ := D.partitionWeight i x • Ω x

def weightedMass (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (i : Fin (D.size+1)) : ℝ :=
  (D.boxes i).mass (D.weightedForm Ω i)

/-- A finite sum of the displayed box primitives and the displayed tree transfers. -/
def primitiveOperator (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] ℝ :=
  ∑ i, ((D.boxes i).formPrimitive
    (D.weightedForm Ω i - D.weightedMass Ω i • (D.boxes i).unitBump) +
    D.weightedMass Ω i • D.treePrimitive i)

end RawSurfacePresentation
#check_explicit RawSurfacePresentation.edgePrimitive
#check_explicit RawSurfacePresentation.treePrimitive
#check_explicit RawSurfacePresentation.primitiveOperator
end SymplecticPacking.HighDim.ToricPackingStages
