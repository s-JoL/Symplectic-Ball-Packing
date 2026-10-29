import SymplecticPacking.HighDim.Handle.FiniteOverlapTree
import SymplecticPacking.HighDim.Handle.QuadricRawPresentationGeometry
import SymplecticPacking.HighDim.Handle.QuadricTightAmbientBoxes

/-!
# The finite raw presentation of the quadric

The finite scalar-certificate tree supplies a raw surface presentation.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j,(a j:ℂ)≠0)]
variable {R : ℚ} (hR : 0<R)
  (hsep₀ : ∀ i,1≤‖(a i:ℂ)‖)
  (hsep : ∀ i j,j≠i → 1≤‖(a i:ℂ)-(a j:ℂ)‖)
  (hbranch : ∀ i,‖(a i:ℂ)‖<(R:ℝ)^2)

abbrev quadricPresentationSize : ℕ := (quadricTreeOrder a hR hsep₀ hsep hbranch).length-1

def quadricPresentationBox (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch+1)) :
    RawAmbientBox (Affine m) (locus (fun j => (a j:ℂ))) :=
  (quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch i.val)).ambientBox
    (quadricTightFiniteBox a hR.le hsep₀ hsep (quadricTreeAt a hR hsep₀ hsep hbranch i.val))
    (quadricTightRootChart_chart a hR.le hsep₀ hsep _)

def quadricPresentationOverlap (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch)) :
    RawAmbientBox (Affine m) (locus (fun j => (a j:ℂ))) :=
  (quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))).ambientBox
    (quadricTreeOverlap a hR hsep₀ hsep hbranch i)
    (quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i)

include hbranch in
theorem quadricTightFiniteBox_inside_core (idx : QuadricTightFiniteIndex a R) :
    (quadricTightFiniteBox a hR.le hsep₀ hsep idx).compactCarrier ⊆
      interior (projectionDomain (fun j => (a j:ℂ)) ((R:ℝ)+1)) := by
  have hbr (i) : ‖(a i:ℂ)‖+1/16<((R:ℝ)+1)^2 := by
    have hp : (0:ℝ)<R := by exact_mod_cast hR
    nlinarith [hbranch i]
  cases idx with
  | inl i => exact quadricFiniteBox_inside a hR.le hsep₀ hsep hbr (.inl i.val)
  | inr i => exact quadricFiniteBox_inside a hR.le hsep₀ hsep hbr (.inr i)

def quadricFinitePresentation : RawSurfacePresentation (Affine m) (locus (fun j => (a j:ℂ)))
    (interior (projectionDomain (fun j => (a j:ℂ)) ((R:ℝ)+1))) where
  size := quadricPresentationSize a hR hsep₀ hsep hbranch
  inclusion := Subtype.val
  boxes := quadricPresentationBox a hR hsep₀ hsep hbranch
  box_inclusion _ := rfl
  inside i := by
    dsimp only [quadricPresentationBox,QuadricRootChart.ambientBox]
    exact quadricTightFiniteBox_inside_core a hR hsep₀ hsep hbranch
      (quadricTreeAt a hR hsep₀ hsep hbranch i.val)
  parent := quadricTreeParent a hR hsep₀ hsep hbranch
  overlap := quadricPresentationOverlap a hR hsep₀ hsep hbranch
  overlap_inclusion _ := rfl
  overlap_child i := by
    dsimp only [quadricPresentationOverlap,quadricPresentationBox,QuadricRootChart.ambientBox]
    exact fun x hx => (quadricTreeOverlap_subset a hR hsep₀ hsep hbranch i hx).1
  overlap_parent i := by
    dsimp only [quadricPresentationOverlap,quadricPresentationBox,QuadricRootChart.ambientBox]
    exact fun x hx => (quadricTreeOverlap_subset a hR hsep₀ hsep hbranch i hx).2

theorem quadricFinitePresentation_cover :
    projectionDomain (fun j => (a j:ℂ)) R ⊆
      ⋃ i, ((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.inner := by
  intro x hx
  dsimp only [quadricFinitePresentation,quadricPresentationBox,QuadricRootChart.ambientBox]
  obtain ⟨i,hi⟩ := quadricTree_inner_cover a hR hsep₀ hsep hbranch x hx
  exact mem_iUnion.mpr ⟨i,(RawCoordinateBox.innerOpen_subset_inner _ hi)⟩

namespace QuadricRootChart
variable {a}
theorem ambient_transition_positive (C E : QuadricRootChart (fun j => (a j:ℂ)))
    (B A : RawCoordinateBox (locus (fun j => (a j:ℂ))))
    (hB : B.chart=C.chart) (hA : A.chart=E.chart)
    (hBA : B.compactCarrier⊆A.carrier)
    {z : Plane} (hz : z∈B.chart '' (C.ambientBox B hB).unitSupport) :
    0<(fderiv ℝ ((E.ambientBox A hA).transition (C.ambientBox B hB)) z).det := by
  obtain ⟨x,hx,rfl⟩ := hz
  have hxB := (C.ambientBox B hB).unitSupport_subset hx
  have hxA := hBA (B.carrier_subset_compactCarrier hxB)
  have hzB := B.chart.map_source hxB.1
  have he : B.chart.symm (B.chart x)=x := B.chart.left_inv hxB.1
  have hsource : B.chart x∈(C.chart.symm.trans E.chart).source := by
    change B.chart x∈C.chart.target ∧ C.chart.symm (B.chart x)∈E.chart.source
    rw [← hB,← hA]
    exact ⟨hzB,he.symm ▸ hxA.1⟩
  change 0<(fderiv ℝ (A.chart ∘ B.chart.symm) (B.chart x)).det
  rw [hB,hA]
  rw [hB] at hsource
  exact C.transition_positive E hsource

theorem inverse_val_smooth (C : QuadricRootChart (fun j => (a j:ℂ))) :
    ContDiffOn ℝ ∞ (fun z => (C.chart.symm z).val) C.chart.target := by
  rcases C with ⟨c,tag,hc⟩
  cases tag with
  | none =>
    exact ((ordinaryLocalLift_smooth c hc).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hz => hz.2)
  | some i =>
    exact ((branchLocalLift_smooth c i hc).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hz => hz.2)
end QuadricRootChart

theorem quadricPresentationBox_smooth (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch+1)) :
    (quadricPresentationBox a hR hsep₀ hsep hbranch i).box.Smooth := by
  dsimp only [quadricPresentationBox,QuadricRootChart.ambientBox]
  exact quadricTightFiniteBox_smooth a hR.le hsep₀ hsep (quadricTreeAt a hR hsep₀ hsep hbranch i.val)

theorem quadricPresentationBox_inverse (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch+1)) :
    ContDiffOn ℝ ∞ (quadricPresentationBox a hR hsep₀ hsep hbranch i).inverseAmbient
      (quadricPresentationBox a hR hsep₀ hsep hbranch i).box.chart.target := by
  let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch i.val)
  have hchart : (quadricPresentationBox a hR hsep₀ hsep hbranch i).box.chart=C.chart :=
    quadricTightRootChart_chart a hR.le hsep₀ hsep _
  have hf : (quadricPresentationBox a hR hsep₀ hsep hbranch i).inverseAmbient =
      fun z => (C.chart.symm z).val := by
    funext z
    change ((quadricTightFiniteBox a hR.le hsep₀ hsep
      (quadricTreeAt a hR hsep₀ hsep hbranch i.val)).chart.symm z).val=(C.chart.symm z).val
    rw [quadricTightRootChart_chart a hR.le hsep₀ hsep _]
  rw [hf,hchart]
  exact C.inverse_val_smooth

theorem quadricPresentationOverlap_smooth (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch)) :
    (quadricPresentationOverlap a hR hsep₀ hsep hbranch i).box.Smooth := by
  dsimp only [quadricPresentationOverlap,QuadricRootChart.ambientBox]
  exact (quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))).box_smooth
    (quadricTreeOverlap a hR hsep₀ hsep hbranch i) (quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i)

theorem quadricPresentationOverlap_inverse (i : Fin (quadricPresentationSize a hR hsep₀ hsep hbranch)) :
    ContDiffOn ℝ ∞ (quadricPresentationOverlap a hR hsep₀ hsep hbranch i).inverseAmbient
      (quadricPresentationOverlap a hR hsep₀ hsep hbranch i).box.chart.target := by
  let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
  have hchart : (quadricPresentationOverlap a hR hsep₀ hsep hbranch i).box.chart=C.chart :=
    quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i
  have hf : (quadricPresentationOverlap a hR hsep₀ hsep hbranch i).inverseAmbient =
      fun z => (C.chart.symm z).val := by
    funext z
    change ((quadricTreeOverlap a hR hsep₀ hsep hbranch i).chart.symm z).val=(C.chart.symm z).val
    rw [quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i]
  rw [hf,hchart]
  exact C.inverse_val_smooth

theorem quadricFinitePresentation_geometry :
    (quadricFinitePresentation a hR hsep₀ hsep hbranch).Geometry := by
  constructor
  · dsimp only [quadricFinitePresentation]
    exact quadricPresentationBox_smooth a hR hsep₀ hsep hbranch
  · dsimp only [quadricFinitePresentation]
    exact quadricPresentationBox_inverse a hR hsep₀ hsep hbranch
  · dsimp only [quadricFinitePresentation]
    exact quadricPresentationOverlap_smooth a hR hsep₀ hsep hbranch
  · dsimp only [quadricFinitePresentation]
    exact quadricPresentationOverlap_inverse a hR hsep₀ hsep hbranch
  · intro i z hz
    let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
    exact QuadricRootChart.ambient_transition_positive C C
      (quadricTreeOverlap a hR hsep₀ hsep hbranch i)
      (quadricTightFiniteBox a hR.le hsep₀ hsep (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1)))
      (quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i)
      (quadricTightRootChart_chart a hR.le hsep₀ hsep _)
      (fun x hx => (quadricTreeOverlap_subset a hR hsep₀ hsep hbranch i hx).1) hz
  · intro i z hz
    let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
    let E := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch
      (quadricTreeParent a hR hsep₀ hsep hbranch i).val)
    exact QuadricRootChart.ambient_transition_positive C E
      (quadricTreeOverlap a hR hsep₀ hsep hbranch i)
      (quadricTightFiniteBox a hR.le hsep₀ hsep (quadricTreeAt a hR hsep₀ hsep hbranch
        (quadricTreeParent a hR hsep₀ hsep hbranch i).val))
      (quadricTreeOverlap_chart a hR hsep₀ hsep hbranch i)
      (quadricTightRootChart_chart a hR.le hsep₀ hsep _)
      (fun x hx => (quadricTreeOverlap_subset a hR hsep₀ hsep hbranch i hx).2) hz

#check_explicit quadricFinitePresentation
end SymplecticPacking.HighDim.ToricPackingStages
