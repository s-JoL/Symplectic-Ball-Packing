import SymplecticPacking.HighDim.Handle.NativePathAgreement
import SymplecticPacking.HighDim.Handle.NativeCutoffSpec

/-!
# Native flow endpoints and geometric Moser maps

Native coordinate endpoints and inverse endpoints equal the geometric Moser maps.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [NormalSpace M] [SigmaCompactSpace M] {m q : ℕ} {U : Set M}
  {T : RawToricModel E M m q} {F : RawSurfacePresentation E M U}

namespace RawFlowAtlasSpec
variable (hF : RawFlowAtlasSpec T F)
  {P : ℝ → Fibre m → M → E →L[ℝ] ℝ}
  {Q : ℝ × Fibre m → ManifoldOneForm Plane M}
  (hPQ : ∀ t v,semanticOneForm T.presentation.inclusion (P t v)=Q (t,v))
include hF hPQ
attribute [local irreducible] semanticOneForm semanticFullOneForm productCouplingPrimitive horizontalPath horizontalMoserMap

theorem path_covector_semantic (t : ℝ) :
    semanticFullOneForm F.inclusion (nativeCouplingPrimitive phaseArea (P t))=
      horizontalPath phaseArea Q t := by
  rw [nativeCouplingPrimitive_semantic]
  unfold horizontalPath
  apply congrArg (fun G : Fibre m → ManifoldOneForm Plane M =>
    productCouplingPrimitive (E:=Plane) (M:=M) phaseArea G)
  funext v
  rw [hF.inclusion_eq]
  exact hPQ t v

theorem pathCutoff_spec (hQ : SmoothOneFormFamily Q) (hK : IsCompact T.region)
    (hinv : ∀ t∈Icc (0:ℝ) 1,∀ x∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q t) x).IsInvertible) :
    MoserCutoff Q (T.pathCutoff F P) T.region := by
  let α : ℝ → M × Fibre m → (E × Fibre m) →L[ℝ] ℝ :=
    fun t => nativeCouplingPrimitive phaseArea (P t)
  have hsem : ∀ t,semanticFullOneForm F.inclusion (α t)=horizontalPath phaseArea Q t :=
    hF.path_covector_semantic hPQ
  have hα : SmoothOneFormFamily (fun t => semanticFullOneForm F.inclusion (α t)) := by
    rw [show (fun t => semanticFullOneForm F.inclusion (α t))=horizontalPath phaseArea Q from funext hsem]
    rw [show horizontalPath phaseArea Q=(fun t =>
      productCouplingPrimitive (E:=Plane) (M:=M) phaseArea (fun v => Q (t,v))) from by unfold horizontalPath; rfl]
    simpa +instances only [TopCat.of.chartedSpace,flatProduct_chartedSpace] using
      (productCouplingPrimitive_smooth (E:=Plane) (M:=M) phaseArea hQ)
  have hc : NativePathCutoff.Spec F (RawToricModel.productBasis m) (RawToricModel.fibreBasis m) α T.region :=
    NativePathCutoff.transferCut_spec F _ _ hF.inclusion_smooth hF.box_smooth hF.box_inverse α hα hK
      (fun x hx => hF.base_cover x.1 hx.1) (by
        intro t ht x hx
        rw [hsem t]
        exact hinv t ht x hx)
  change MoserCutoff Q (NativePathCutoff.transferCut F (RawToricModel.productBasis m)
    (RawToricModel.fibreBasis m) α T.region) T.region
  refine ⟨hc.smooth,?_,hc.one,hc.fibre_compact⟩
  intro p hp
  have he := congrArg (fun θ : ManifoldOneForm (Plane × Fibre m) (M × Fibre m) =>
    (manifoldExteriorOneForm θ p.2).IsInvertible) (hsem p.1)
  exact he.mp (hc.nondegenerate p hp)

theorem pathFlow_eq_horizontalMoserMap (hQ : SmoothOneFormFamily Q) (hK : IsCompact T.region)
    (hinv : ∀ t∈Icc (0:ℝ) 1,∀ x∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q t) x).IsInvertible) :
    T.pathFlow F P 1=⇑(horizontalMoserMap phaseArea Q (T.pathCutoff F P)) := by
  let α : ℝ → M × Fibre m → (E × Fibre m) →L[ℝ] ℝ :=
    fun t => nativeCouplingPrimitive phaseArea (P t)
  let χ := T.pathCutoff F P
  have hsem : ∀ t,semanticFullOneForm F.inclusion (α t)=horizontalPath phaseArea Q t :=
    hF.path_covector_semantic hPQ
  have hα : SmoothOneFormFamily (fun t => semanticFullOneForm F.inclusion (α t)) := by
    rw [show (fun t => semanticFullOneForm F.inclusion (α t))=horizontalPath phaseArea Q from funext hsem]
    rw [show horizontalPath phaseArea Q=(fun t =>
      productCouplingPrimitive (E:=Plane) (M:=M) phaseArea (fun v => Q (t,v))) from by unfold horizontalPath; rfl]
    simpa +instances only [TopCat.of.chartedSpace,flatProduct_chartedSpace] using
      (productCouplingPrimitive_smooth (E:=Plane) (M:=M) phaseArea hQ)
  have hg := NativePathCutoff.gramSum_semantic_smooth F (RawToricModel.productBasis m)
    hF.inclusion_smooth hF.box_smooth hF.box_inverse hα
  have hμ : 0<NativePathCutoff.gramLevel F (RawToricModel.productBasis m) α T.region :=
    NativePathCutoff.gramLevel_pos F _ hK hg.continuous (by
      intro p hp
      apply NativePathCutoff.gramSum_pos_of_cover F _ hF.inclusion_smooth hF.box_smooth α hα
        (hF.base_cover p.2.1 hp.2.1)
      simpa only [hsem] using hinv p.1 hp.1 p.2 hp.2)
  have hsupp : tsupport χ⊆{p | 0<NativePathCutoff.gramSum F (RawToricModel.productBasis m) α p} :=
    NativePathCutoff.transferCut_tsupport_gram F _ _ α T.region hg.continuous hμ
  have hG : IsOpen {p : ℝ × (M × Fibre m) |
      0<NativePathCutoff.gramSum F (RawToricModel.productBasis m) α p} :=
    isOpen_lt continuous_const hg.continuous
  have hInv : ∀ p∈{p | 0<NativePathCutoff.gramSum F (RawToricModel.productBasis m) α p},
      (manifoldExteriorOneForm (semanticFullOneForm F.inclusion (α p.1)) p.2).IsInvertible :=
    fun p hp => NativePathCutoff.gramSum_nondegenerate F _ hF.inclusion_smooth hF.box_smooth α hα hp
  have hcover : ∀ p∈tsupport χ,∃ i,p.2.1∈(F.boxes i).box.chart.source :=
    fun p hp => NativePathCutoff.gramSum_source F _ α (hsupp hp)
  have hχ := NativePathCutoff.transferCut_semantic_smooth F (RawToricModel.productBasis m)
    (RawToricModel.fibreBasis m)
    hF.inclusion_smooth hF.box_smooth hF.box_inverse hα T.region
  have hsp : ∃ K : Set (M × Fibre m),IsCompact K ∧ ∀ t x,x∉K → χ (t,x)=0 :=
    ⟨NativePathCutoff.spatialCarrier F (RawToricModel.fibreBasis m) T.region,
      NativePathCutoff.spatialCarrier_compact F _ _,NativePathCutoff.transferCut_zero_off_carrier F _ _ α T.region⟩
  obtain ⟨C,hC,hχC⟩ := hsp
  obtain ⟨e,heMap⟩ := F.fullMoserFlow_diffeomorph hF.inclusion_smooth hF.immersion hF.box_smooth
    hF.regularity α hα χ hχ hG hInv hsupp hcover hC hχC
  have hdata : T.pathFlow F P 1=fieldFlow
      (cutField χ (fun t => manifoldExteriorOneForm (horizontalPath phaseArea Q t))
        (manifoldTimePrimitive (horizontalPath phaseArea Q))) 1 := by
    funext x
    have hh := F.fullMoserFlow_eq_fieldFlow hF.inclusion_smooth hF.immersion hF.box_smooth
      hF.regularity α hα χ
      (fun p hp => hcover p (subset_closure hp))
      (fun p hp => hInv p (hsupp (subset_closure hp))) 1 x
    change F.fullMoserFlow α χ 1 x=fieldFlow
      (cutField χ (fun t => manifoldExteriorOneForm (horizontalPath phaseArea Q t))
        (manifoldTimePrimitive (fun t => horizontalPath phaseArea Q t))) 1 x
    simpa only [hsem] using hh
  have hde := diffeoOf_eq e heMap
  unfold horizontalMoserMap
  rw [←hdata]
  change (F.fullMoserFlow α χ 1)=⇑(diffeoOf (E:=Plane × Fibre m) (F.fullMoserFlow α χ 1))
  rw [hde,heMap]

theorem inverse_pathFlow_eq (hQ : SmoothOneFormFamily Q) (hK : IsCompact T.region)
    (hinv : ∀ t∈Icc (0:ℝ) 1,∀ x∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q t) x).IsInvertible) :
    nativeInverse (T.pathFlow F P 1)=⇑(horizontalMoserMap phaseArea Q (T.pathCutoff F P)).symm :=
  nativeInverse_eq_symm (horizontalMoserMap phaseArea Q (T.pathCutoff F P)).toEquiv
    (hF.pathFlow_eq_horizontalMoserMap hPQ hQ hK hinv).symm
end RawFlowAtlasSpec
end SymplecticPacking.HighDim
