import SymplecticPacking.HighDim.Handle.RawMoser

/-!
# Local product-coupling formulas in raw charts

Local product-coupling formulas in the supplied finite raw charts.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]

/-- Inverting this finite-dimensional bilinear matrix is a unique linear operation. -/
def rawLinearMoser {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : K →L[ℝ] K →L[ℝ] ℝ) (a : K →L[ℝ] ℝ) : K := -(W.inverse a)

theorem rawLinearMoser_spec {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : K →L[ℝ] K →L[ℝ] ℝ) (a : K →L[ℝ] ℝ) (hW : W.IsInvertible) :
    W (rawLinearMoser W a) = -a := by
  simp only [rawLinearMoser,map_neg,hW.self_apply_inverse]

theorem rawLinearMoser_natural {K L : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    (c : K ≃L[ℝ] L) (W : L →L[ℝ] L →L[ℝ] ℝ) (a : L →L[ℝ] ℝ)
    (hW : W.IsInvertible) :
    c (rawLinearMoser (W.bilinearComp (c : K →L[ℝ] L) (c : K →L[ℝ] L)) (a.comp (c : K →L[ℝ] L))) = rawLinearMoser W a := by
  have hlocal := rawLinearMoser_spec (W.bilinearComp (c : K →L[ℝ] L) (c : K →L[ℝ] L)) (a.comp (c : K →L[ℝ] L))
    (bilinearComp_equiv_isInvertible c hW)
  have he : W (c (rawLinearMoser (W.bilinearComp (c : K →L[ℝ] L) (c : K →L[ℝ] L)) (a.comp (c : K →L[ℝ] L)))) = -a := by
    apply ContinuousLinearMap.ext
    intro v
    have hh := congrArg (fun b : K →L[ℝ] ℝ => b (c.symm v)) hlocal
    simpa only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply,neg_apply] using hh
  obtain ⟨e,heW⟩ := hW
  apply e.injective
  change (e : L →L[ℝ] L →L[ℝ] ℝ) _ = (e : L →L[ℝ] L →L[ℝ] ℝ) _
  rw [heW,he,rawLinearMoser_spec W a ⟨e,heW⟩]

namespace RawAmbientBox
variable (B : RawAmbientBox E M)

/-- The horizontal covector in the displayed base chart and the unchanged fibre. -/
def productHorizontal (Γ : V → M → E →L[ℝ] ℝ) (y : Plane × V) :
    (Plane × V) →L[ℝ] ℝ :=
  (B.coordinatePullback (Γ y.2) y.1).comp (ContinuousLinearMap.fst ℝ Plane V)

/-- The vertical form plus the full derivative of the displayed horizontal covector.
It includes the parameter/base mixed terms and is smooth across the fibre axes. -/
def productForm (W : V →L[ℝ] V →L[ℝ] ℝ) (Γ : V → M → E →L[ℝ] ℝ)
    (y : Plane × V) : (Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ :=
  W.bilinearComp (ContinuousLinearMap.snd ℝ Plane V) (ContinuousLinearMap.snd ℝ Plane V) +
    euclideanExteriorOneForm (B.productHorizontal Γ) y

def productTimePrimitive (Γ : ℝ → V → M → E →L[ℝ] ℝ) (t : ℝ) (y : Plane × V) :
    (Plane × V) →L[ℝ] ℝ := deriv (fun s => B.productHorizontal (Γ s) y) t

/-- Both the base motion and its fibre correction are obtained by one displayed matrix
inverse. In particular no polar angle is evaluated at a zero fibre coordinate. -/
def productMoserField (W : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : ℝ → V → M → E →L[ℝ] ℝ) (t : ℝ) (x : M × V) : E × V :=
  let y := (B.box.chart x.1,x.2)
  ((B.frame y.1).prodMap (ContinuousLinearMap.id ℝ V))
    (rawLinearMoser (B.productForm W (Γ t) y) (B.productTimePrimitive Γ t y))

section semantic
variable [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productHorizontal_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (Γ : V → M → E →L[ℝ] ℝ) {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift
      (fun v => semanticOneForm ι (Γ v))) (flatProductMap B.box.chart.symm) (0,y) =
      B.productHorizontal Γ y := by
  have hg := (hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)
  apply ContinuousLinearMap.ext
  intro w
  rw [productHorizontalLift_pullback_apply _ hg]
  have he := semanticOneForm_pullback B hι hinc hB (Γ y.2) hy
  exact congrArg (fun a : Plane →L[ℝ] ℝ => a w.1) he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productForm_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (W : V →L[ℝ] V →L[ℝ] ℝ) (Γ : V → M → E →L[ℝ] ℝ)
    (hΓ : SmoothOneFormFamily (fun v => semanticOneForm ι (Γ v)))
    {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    B.productForm W Γ y =
      (globalHorizontalCoupling W (fun v => semanticOneForm ι (Γ v))
        (flatProductMap B.box.chart.symm y)).bilinearComp
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
          (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
          (ContinuousLinearMap.id ℝ V)) := by
  have hg := (hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)
  rw [globalHorizontalCoupling_pullback hΓ hg]
  have he : (fun z => euclideanPullbackOneForm (fun _ => productHorizontalLift
      (fun v => semanticOneForm ι (Γ v))) (flatProductMap B.box.chart.symm) (0,z))
      =ᶠ[𝓝 y] B.productHorizontal Γ := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (B.box.chart.open_target.mem_nhds hy)] with z hz
    exact B.productHorizontal_pullback hι hinc hB Γ hz
  unfold productForm euclideanExteriorOneForm
  rw [he.fderiv_eq]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productTimePrimitive_pullback {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (W : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ → V → M → E →L[ℝ] ℝ)
    (hΓ : SmoothOneFormFamily (fun q : ℝ × V => semanticOneForm ι (Γ q.1 q.2)))
    (t : ℝ) {y : Plane × V} (hy : y.1 ∈ B.box.chart.target) :
    B.productTimePrimitive Γ t y =
      (manifoldTimePrimitive (fun s => productCouplingPrimitive W
        (fun v => semanticOneForm ι (Γ s v))) t
        (flatProductMap B.box.chart.symm y)).comp
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
          (ContinuousLinearMap.id ℝ V)) := by
  let J : (Plane × V) →L[ℝ] (Plane × V) := (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
    (ContinuousLinearMap.id ℝ V)
  let F : ℝ → (Plane × V) →L[ℝ] ℝ := fun s => productCouplingPrimitive W
    (fun v => semanticOneForm ι (Γ s v)) (flatProductMap B.box.chart.symm y)
  let c : (Plane × V) →L[ℝ] ℝ := ((1/2:ℝ) • W y.2).comp (ContinuousLinearMap.snd ℝ Plane V)
  have hg := (hB.inverse y.1 hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)
  have he (s : ℝ) : (F s).comp J = c+B.productHorizontal (Γ s) y := by
    have hh := B.productHorizontal_pullback hι hinc hB (Γ s) hy
    change (productHorizontalLift (fun v => semanticOneForm ι (Γ s v))
      (flatProductMap B.box.chart.symm y)).comp
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) (flatProductMap B.box.chart.symm) y) = _ at hh
    rw [flatProductMap_derivative hg] at hh
    apply ContinuousLinearMap.ext
    intro u
    change productVerticalLiouville W (flatProductMap B.box.chart.symm y) (J u) +
      productHorizontalLift (fun v => semanticOneForm ι (Γ s v))
        (flatProductMap B.box.chart.symm y) (J u) = c u + B.productHorizontal (Γ s) y u
    rw [productVerticalLiouville_apply]
    exact congrArg (fun b : (Plane × V) →L[ℝ] ℝ => c u+b u) hh
  have hs := productCouplingPrimitive_smooth W hΓ
  have hf : DifferentiableAt ℝ F t :=
    (hs.parameter_contDiffAt t (flatProductMap B.box.chart.symm y)).differentiableAt (by simp)
  have hd := hf.hasDerivAt.clm_comp (hasDerivAt_const t J)
  have hefun : (fun s => (F s).comp J) = fun s => c+B.productHorizontal (Γ s) y := funext he
  rw [hefun] at hd
  have hh := hd.sub (hasDerivAt_const t c)
  have hcancel : ((fun s => c+B.productHorizontal (Γ s) y) - fun _ => c) =
      (fun s => B.productHorizontal (Γ s) y) := by
    funext s
    exact add_sub_cancel_left c (B.productHorizontal (Γ s) y)
  rw [hcancel] at hh
  have hd' : HasDerivAt (fun s => B.productHorizontal (Γ s) y) ((deriv F t).comp J) t := by
    simpa only [Pi.sub_apply,add_sub_cancel_left,add_zero,sub_zero,
      ContinuousLinearMap.comp_zero] using hh
  exact hd'.deriv

end semantic
end RawAmbientBox

#check_explicit rawLinearMoser
#check_explicit RawAmbientBox.productHorizontal
#check_explicit RawAmbientBox.productForm
#check_explicit RawAmbientBox.productTimePrimitive
#check_explicit RawAmbientBox.productMoserField
end SymplecticPacking.HighDim.ToricPackingStages
