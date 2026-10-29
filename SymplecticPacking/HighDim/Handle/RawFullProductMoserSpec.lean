import SymplecticPacking.HighDim.Handle.RawFullProductMoser

/-!
# Naturality of the full ambient covector

Naturality of the full native covector and its Moser field.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

/-- Semantic comparison only; no construction calls this representation. -/
def semanticFullOneForm (ι : M → E) (α : M × V → (E × V) →L[ℝ] ℝ) :
    ManifoldOneForm (Plane × V) (M × V) := fun x =>
  (α x).comp ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι x.1).prodMap (ContinuousLinearMap.id ℝ V))

namespace RawAmbientBox
variable (B : RawAmbientBox E M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullCovector_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (α : M × V → (E × V) →L[ℝ] ℝ) {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    euclideanPullbackOneForm (fun _ => semanticFullOneForm ι α)
      (flatProductMap B.box.chart.symm) (0,y) = B.fullCovector α y := by
  have hg := (hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)
  unfold euclideanPullbackOneForm
  rw [flatProductMap_derivative hg]
  apply ContinuousLinearMap.ext
  intro u
  change α (B.box.chart.symm y.1,y.2)
    (((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y.1)).prodMap
      (ContinuousLinearMap.id ℝ V))
      (((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
        (ContinuousLinearMap.id ℝ V)) u)) =
    α (B.box.chart.symm y.1,y.2) (((B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V)) u)
  rw [B.frame_eq_mfderiv_comp hι hinc hB hy]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullForm_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t))) (t : ℝ)
    {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    B.fullForm (α t) y =
      (manifoldExteriorOneForm (semanticFullOneForm ι (α t)) (flatProductMap B.box.chart.symm y)).bilinearComp
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap (ContinuousLinearMap.id ℝ V)) := by
  have hg := flatProductMap_smoothAt ((hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy))
  have hh := euclidean_manifold_pullback_exterior_at hg
    (hα.spatial_smooth t _ (mem_extChartAt_target _))
  have he : (fun z => euclideanPullbackOneForm (fun _ => semanticFullOneForm ι (α t))
      (flatProductMap B.box.chart.symm) (0,z)) =ᶠ[𝓝 y] B.fullCovector (α t) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (B.box.chart.open_target.mem_nhds hy)] with z hz
    exact B.fullCovector_pullback hι hinc hB (α t) hz
  unfold fullForm euclideanExteriorOneForm
  rw [← he.fderiv_eq]
  simpa only [euclideanExteriorOneForm,manifoldMapDifferential,flatProductMap_derivative
    ((hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy))] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullTimePrimitive_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t))) (t : ℝ)
    {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    B.fullTimePrimitive α t y =
      (manifoldTimePrimitive (fun s => semanticFullOneForm ι (α s)) t
        (flatProductMap B.box.chart.symm y)).comp
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap (ContinuousLinearMap.id ℝ V)) := by
  let J : (Plane × V) →L[ℝ] (Plane × V) :=
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap (ContinuousLinearMap.id ℝ V)
  let F : ℝ → (Plane × V) →L[ℝ] ℝ := fun s => semanticFullOneForm ι (α s) (flatProductMap B.box.chart.symm y)
  have hg := (hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)
  have he (s : ℝ) : (F s).comp J = B.fullCovector (α s) y := by
    have hh := B.fullCovector_pullback hι hinc hB (α s) hy
    unfold euclideanPullbackOneForm at hh
    rw [flatProductMap_derivative hg] at hh
    exact hh
  have hf : DifferentiableAt ℝ F t :=
    (hα.parameter_contDiffAt t (flatProductMap B.box.chart.symm y)).differentiableAt (by simp)
  have hd := hf.hasDerivAt.clm_comp (hasDerivAt_const t J)
  have hefun : (fun s => (F s).comp J) = fun s => B.fullCovector (α s) y := funext he
  rw [hefun] at hd
  simpa only [fullTimePrimitive,manifoldTimePrimitive,ContinuousLinearMap.comp_zero,add_zero] using hd.deriv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullMoserField_eq_manifoldMoserField {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t))) (t : ℝ)
    {y : Plane × V} (hy : y.1 ∈ B.box.chart.target)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm ι (α t))
      (flatProductMap B.box.chart.symm y)).IsInvertible) :
    B.fullMoserField α t (flatProductMap B.box.chart.symm y) =
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y.1)).prodMap (ContinuousLinearMap.id ℝ V))
        (manifoldMoserField (fun s => manifoldExteriorOneForm (semanticFullOneForm ι (α s)))
          (manifoldTimePrimitive (fun s => semanticFullOneForm ι (α s)))
          (t,flatProductMap B.box.chart.symm y)) := by
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) M Plane ∞ :=
    { toPartialEquiv := B.box.chart.toPartialEquiv
      open_source := B.box.chart.open_source
      open_target := B.box.chart.open_target
      contMDiffOn_toFun := hB.forward
      contMDiffOn_invFun := hB.inverse }
  let cb : Plane ≃L[ℝ] Plane :=
    (PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ e.symm hy).mfderivToContinuousLinearEquiv (by simp)
  have hcb : (cb : Plane →L[ℝ] Plane) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1 := rfl
  let c := cb.prodCongr (ContinuousLinearEquiv.refl ℝ V)
  have hc : (c : (Plane × V) →L[ℝ] (Plane × V)) =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
        (ContinuousLinearMap.id ℝ V) := by
    change (cb : Plane →L[ℝ] Plane).prodMap (ContinuousLinearMap.id ℝ V) = _
    rw [hcb]
  let A : (Plane × V) →L[ℝ] (E × V) :=
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y.1)).prodMap (ContinuousLinearMap.id ℝ V)
  have hframe : (B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V) =
      A.comp (c : (Plane × V) →L[ℝ] (Plane × V)) := by
    rw [B.frame_eq_mfderiv_comp hι hinc hB hy,hc]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  unfold fullMoserField
  simp only [flatProductMap,Prod.map_fst,Prod.map_snd,id_eq,B.box.chart.right_inv hy]
  rw [hframe,B.fullForm_pullback hι hinc hB α hα t hy,
    B.fullTimePrimitive_pullback hι hinc hB α hα t hy,← hc]
  exact congrArg A (rawLinearMoser_natural c _ _ hinv)

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
