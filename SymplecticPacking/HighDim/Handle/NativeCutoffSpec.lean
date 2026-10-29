import SymplecticPacking.HighDim.Handle.RawPathCutoff

/-!
# Properties of the native finite-atlas cutoff

All support and nondegeneracy properties of the native finite-atlas cutoff.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.NativePathCutoff
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {U : Set M} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure Spec (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (bv : Module.Basis κ ℝ V) (α : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V)) : Prop where
  smooth : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (transferCut D b bv α K)
  nondegenerate : ∀ p∈tsupport (transferCut D b bv α K),
    (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible
  cover : ∀ p∈tsupport (transferCut D b bv α K),∃ i,p.2.1∈(D.boxes i).box.chart.source
  one : ∀ᶠ p in 𝓝ˢ (Icc (0:ℝ) 1 ×ˢ K),transferCut D b bv α K p=1
  fibre_compact : ∃ C : Set V,IsCompact C ∧ ∀ t x,x.2∉C → transferCut D b bv α K (t,x)=0
  spatial_compact : ∃ C : Set (M × V),IsCompact C ∧ ∀ t x,x∉C → transferCut D b bv α K (t,x)=0
  level_pos : 0<gramLevel D b α K

theorem transferCut_spec (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (hi : ∀ i,ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    {K : Set (M × V)} (hK : IsCompact K)
    (hcover : ∀ x∈K,∃ i,x.1∈(D.boxes i).box.inner)
    (hinv : ∀ t∈Icc (0:ℝ) 1,∀ x∈K,
      (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α t)) x).IsInvertible) :
    Spec D b bv α K := by
  have hg := gramSum_semantic_smooth D b hι hB hi hα
  have hμ : 0<gramLevel D b α K := gramLevel_pos D b hK hg.continuous (by
    intro p hp
    exact gramSum_pos_of_cover D b hι hB α hα (hcover p.2 hp.2) (hinv p.1 hp.1 p.2 hp.2))
  refine ⟨transferCut_semantic_smooth D b bv hι hB hi hα K,?_,?_,
    transferCut_one_near D b bv α hK hg.continuous hμ,
    transferCut_fibreCompact D b bv α K,?_,hμ⟩
  · intro p hp
    exact (transferCut_tsupport_good D b bv hι hB α hα K hg.continuous hμ hp).2
  · intro p hp
    exact (transferCut_tsupport_good D b bv hι hB α hα K hg.continuous hμ hp).1
  · exact ⟨spatialCarrier D bv K,spatialCarrier_compact D bv K,
      transferCut_zero_off_carrier D b bv α K⟩
end SymplecticPacking.HighDim.ToricPackingStages.NativePathCutoff
