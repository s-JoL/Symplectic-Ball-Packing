import SymplecticPacking.HighDim.Handle.NativeToricStages
import SymplecticPacking.HighDim.Handle.RawNormalizationSpec
import SymplecticPacking.HighDim.Handle.RawManifoldFamily
import OAI.Geometry.BallPacking.Models.SurfaceComparison

/-!
# Agreement of native and geometric model inputs

Proof-only correspondence between native model inputs and the geometric model.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [NormalSpace M] [SigmaCompactSpace M] {m q : ℕ}

structure RawModelAgreement (T : RawToricModel E M m q) (S : ToricModel M m q) : Prop where
  polytope_eq : T.polytope=S.Δ
  base_eq : T.base=S.base
  primitive_eq : ∀ p,semanticOneForm T.presentation.inclusion (T.physicalPrimitive p)=S.Γ p
  reference_eq : semanticTwoForm T.presentation.inclusion T.referenceForm=S.Λ
  handle : T.handle.Agreement T.presentation.inclusion S.handle T.hb
  hb_eq : T.hb=S.hb
  hδ_eq : T.hδ=S.hδ


/-- Geometric facts about the larger flow atlas; this record is used only in proofs. -/
structure RawFlowAtlasSpec (T : RawToricModel E M m q) {U : Set M}
    (F : RawSurfacePresentation E M U) : Prop where
  inclusion_eq : F.inclusion=T.presentation.inclusion
  inclusion_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ F.inclusion
  immersion : ∀ x,Injective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) F.inclusion x)
  regularity : AmbientRegularity (K:=Plane × Fibre m) (F.productInclusion (V:=Fibre m))
  box_smooth : ∀ i,(F.boxes i).box.Smooth
  box_inverse : ∀ i,ContDiffOn ℝ ∞ (F.boxes i).inverseAmbient (F.boxes i).box.chart.target
  base_cover : ∀ x∈T.base,∃ i,x∈(F.boxes i).box.inner

namespace RawModelAgreement
variable {T : RawToricModel E M m q} {S : ToricModel M m q} (h : RawModelAgreement T S)

include h

theorem region_eq : T.region=S.region := by
  simp only [RawToricModel.region,ToricModel.region,h.base_eq,h.polytope_eq,Polytope.set,planeRegion]

/-- This target predicate is derived from the native normalization output. -/
theorem normalization_target (hS : S.Spec)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion)
    {reserve : ℝ} (hN : RawNormalizationSpec T reserve (S.baseArea hS)) :
    TargetPrimitive S (fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p)) := by
  let Γ := fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p)
  have hΓ : SmoothOneFormFamily Γ := semanticOneForm_family_smooth hι hN.primitive_smooth
  refine ⟨hΓ,?_,?_⟩
  · obtain ⟨K,hK,hKi,hstat⟩ := hN.compact_difference
    refine ⟨K,hK,?_,?_⟩
    · simpa only [h.base_eq] using hKi
    · intro x hx p
      exact (hstat p x hx).trans (congrFun (h.primitive_eq p) x)
  · let κ := fun z : Moments m × M => surfaceFormRatio S.Λ (manifoldExteriorOneForm (Γ z.1)) z.2
    have hsk : ∀ p x u v,manifoldExteriorOneForm (Γ p) x u v=
        -manifoldExteriorOneForm (Γ p) x v u := fun p x u v => manifoldExteriorOneForm_skew _ _ _ _
    have hΩ : SmoothTwoFormFamily (fun p : Moments m => manifoldExteriorOneForm (Γ p)) :=
      manifoldExteriorOneForm_family_smooth hΓ
    have hκ : ContMDiff ((𝓘(ℝ,Moments m)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ κ :=
      surfaceFormRatio_smooth (P:=Moments m) (M:=M) (Λ:=S.Λ)
        (Ω:=fun p => manifoldExteriorOneForm (Γ p)) hS.Λ_smooth hS.Λ_skew hS.Λ_pos hΩ hsk
    refine ⟨κ,hκ,?_,?_⟩
    · intro p x
      exact surface_form_scalar (hsk p) hS.Λ_skew hS.Λ_pos x
    · intro p hp x hx
      have hp' : p∈T.polytope.set := h.polytope_eq.symm ▸ hp
      have hx' : x∈T.base := h.base_eq.symm ▸ hx
      exact div_pos
        (hN.positive p hp' x _ (mem_extChartAt_target x) (by simpa using hx'))
        (hS.Λ_pos x _ (mem_extChartAt_target x))
end RawModelAgreement
end SymplecticPacking.HighDim
