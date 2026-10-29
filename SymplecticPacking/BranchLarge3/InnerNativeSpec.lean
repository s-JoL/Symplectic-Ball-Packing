import SymplecticPacking.BranchLarge3.InnerNativeProvider
import SymplecticPacking.HighDim.Handle.NativePackingSpec

/-!
# Specification of the six-dimensional inner maps

The native six-dimensional inner maps satisfy the physical packing theorem.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.NativeInner
open Set Manifold
open HighDim HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem spec {N : ℕ} (Q : ℕ) {r r' : Fin N → ℝ} {a : ℚ} (H : CmpHyp r a)
    (hr' : ∀ i,0 ≤ r' i) (hra : ∀ i,r' i<r i) :
    (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
      (globalHorizontalCoupling phaseArea
        (physicalPrimitive (A:=(weights Q r a).A) (B:=(weights Q r a).B)
          (weights Q r a).D (weights Q r a).S (coefficient Q r a) (weights Q r a).L ∘ planeMoments))
      (maps Q r r' a i)) ∧
    (∀ i,MapsTo (maps Q r r' a i) (closedBall 3 (r' i))
      (interior (cubicExhaustion (level Q r a) ×ˢ
        planeRegion sixModelBounds ![((cmpData r a).h₁:ℝ),(cmpData r a).h₂]))) ∧
    Pairwise (fun i j => Disjoint (maps Q r r' a i '' closedBall 3 (r' i))
      (maps Q r r' a j '' closedBall 3 (r' j))) := by
  have hp := providerSpec Q H
  have hτ := (cmpData_spec H).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hf,hm,hd⟩ := hp.agreement.native_packing_spec hp.model hp.atlas hp.cover
    hp.comparison hp.normalization hr' hra hτ hp.caps hp.profile
  have hf' : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i))
      (fun _ => successorStandardForm 2) (semanticModel Q r a).form (maps Q r r' a i) := by
    simpa only [maps] using hf
  have hm' : ∀ i,MapsTo (maps Q r r' a i) (closedBall 3 (r' i)) (interior (semanticModel Q r a).region) := by
    simpa only [maps,hp.agreement.region_eq] using hm
  refine ⟨?_,hm',?_⟩
  · intro i
    exact (hf' i).congr_target_near (fun x hx => interior_subset (hm' i hx)) hp.physical_near
  · simpa only [maps] using hd

end SymplecticPacking.BranchLarge3.NativeInner
