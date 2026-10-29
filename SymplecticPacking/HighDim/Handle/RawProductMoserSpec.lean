import SymplecticPacking.HighDim.Handle.RawProductMoser

/-!
# Naturality of the native product Moser field

The native full product field is the ambient image of the Moser field.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawAmbientBox

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productMoserField_eq_manifoldMoserField (B : RawAmbientBox E M)
    {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (W : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ → V → M → E →L[ℝ] ℝ)
    (hΓ : SmoothOneFormFamily (fun q : ℝ × V => semanticOneForm ι (Γ q.1 q.2)))
    (t : ℝ) {y : Plane × V} (hy : y.1 ∈ B.box.chart.target)
    (hinv : (globalHorizontalCoupling W (fun v => semanticOneForm ι (Γ t v))
      (flatProductMap B.box.chart.symm y)).IsInvertible) :
    B.productMoserField W Γ t (flatProductMap B.box.chart.symm y) =
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y.1)).prodMap
        (ContinuousLinearMap.id ℝ V))
        (manifoldMoserField
          (fun s => globalHorizontalCoupling W (fun v => semanticOneForm ι (Γ s v)))
          (manifoldTimePrimitive (fun s => productCouplingPrimitive W
            (fun v => semanticOneForm ι (Γ s v))))
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
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y.1)).prodMap
      (ContinuousLinearMap.id ℝ V)
  have hframe : (B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V) =
      A.comp (c : (Plane × V) →L[ℝ] (Plane × V)) := by
    rw [B.frame_eq_mfderiv_comp hι hinc hB hy,hc]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hΓt : SmoothOneFormFamily (fun v => semanticOneForm ι (Γ t v)) :=
    hΓ.comp (contDiff_const.prodMk contDiff_id)
  unfold productMoserField
  simp only [flatProductMap,Prod.map_fst,Prod.map_snd,id_eq,B.box.chart.right_inv hy]
  rw [hframe,B.productForm_pullback hι hinc hB W (Γ t) hΓt hy,
    B.productTimePrimitive_pullback hι hinc hB W Γ hΓ t hy,← hc]
  exact congrArg A (rawLinearMoser_natural c _ _ hinv)

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
