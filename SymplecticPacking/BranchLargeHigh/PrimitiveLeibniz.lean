import OAI.Geometry.BallPacking.Forms.ManifoldExteriorAlgebra
import OAI.Geometry.BallPacking.Normal.QuadricMovingCone

/-!
# Exterior differentiation of a scalar multiple
-/

noncomputable section
namespace SymplecticPacking.BranchLargeHigh.Two

open Set Filter Topology Manifold ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exterior_variable_smul {f : M → ℝ} {α : ManifoldOneForm E M}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (x : M) (v w : E) :
    manifoldExteriorOneForm (fun y => f y • α y) x v w =
      f x * manifoldExteriorOneForm α x v w +
        manifoldScalarDifferential f x v * α x w -
        manifoldScalarDifferential f x w * α x v := by
  let e := extChartAt 𝓘(ℝ,E) x
  let y := e x
  let C := chartDifferential (E := E) x x
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hy : y ∈ e.target := e.map_source hx
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hy
  have hC : C.IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hx using 1
  have hF := (manifoldScalar_chart_smooth hf x).contDiffAt hn
  have hA := (hα x).contDiffAt hn
  have he : chartOneForm (fun y => f y • α y) x =
      fun z => (f ∘ e.symm) z • chartOneForm α x z := by
    funext z
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hval : (f ∘ e.symm) y = f x := by rw [Function.comp_apply, e.left_inv hx]
  have hLin (β : ManifoldOneForm E M) (u : E) : chartOneForm β x y (C u) = β x u := by
    change β (e.symm y) ((chartDifferential (E := E) x (e.symm y)).inverse (C u)) = _
    rw [e.left_inv hx]
    exact congrArg (β x) (hC.inverse_apply_self u)
  have hFv (u : E) : fderiv ℝ (f ∘ e.symm) y (C u) = manifoldScalarDifferential f x u := by
    rw [← manifoldScalarDifferential_chart hf hy]
    exact hLin (manifoldScalarDifferential f) u
  dsimp only [e] at hval hFv
  change fderiv ℝ (chartOneForm (fun y => f y • α y) x) y (C v) (C w) -
    fderiv ℝ (chartOneForm (fun y => f y • α y) x) y (C w) (C v) = _
  rw [he, (hF.differentiableAt (by simp) |>.hasFDerivAt.fun_smul
    (hA.differentiableAt (by simp)).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smulRight_apply, hval, hLin, hFv, smul_eq_mul]
  change _ = f x * (fderiv ℝ (chartOneForm α x) y (C v) (C w) -
    fderiv ℝ (chartOneForm α x) y (C w) (C v)) + _ - _
  ring

/-- Exterior derivative of the line coupling primitive, including its mixed term. -/
theorem firstLine_exterior {α : ManifoldOneForm E M}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α)) (x : M × Plane) (v w : E × Plane) :
    manifoldExteriorOneForm (firstLinePrimitive α) x v w =
      planarArea v.2 w.2 + (1 - radialArea x.2) * manifoldExteriorOneForm α x.1 v.1 w.1 -
        fderiv ℝ radialArea x.2 v.2 * α x.1 w.1 +
        fderiv ℝ radialArea x.2 w.2 * α x.1 v.1 := by
  let A : ManifoldOneForm (E × Plane) (M × Plane) :=
    productHorizontalLift (fun _ : Plane => α)
  let f : M × Plane → ℝ := fun x => 1 - radialArea x.2
  have hf : ContMDiff 𝓘(ℝ,E × Plane) 𝓘(ℝ,ℝ) ∞ f :=
    contMDiff_const.sub (radialArea_smooth.contMDiff.comp flatProduct_snd_smooth)
  have hA : SmoothOneFormFamily (fun _ : ℝ => A) :=
    productHorizontalLift_smooth (hα.comp contDiff_fst)
  have hΓ : SmoothOneFormFamily (fun p : ℝ × Plane => (1 - radialArea p.2) • α) :=
    (hα.comp contDiff_fst).smul (contDiff_const.sub (radialArea_smooth.comp contDiff_snd))
  have hW : SmoothOneFormFamily (fun _ : ℝ => fun y => f y • A y) := by
    convert! productHorizontalLift_smooth hΓ using 1
  have he : firstLinePrimitive α = productVerticalLiouville planarArea + fun y => f y • A y := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    simp only [firstLinePrimitive_apply, Pi.add_apply, add_apply,
      productVerticalLiouville_apply, smul_apply, A, f, productHorizontalLift_apply,
      linearLiouville, smul_eq_mul]
  have hAx (u : E × Plane) : A x u = α x.1 u.1 := rfl
  have hAd : manifoldExteriorOneForm A x v w = manifoldExteriorOneForm α x.1 v.1 w.1 := by
    have hd := manifold_pullback_exterior (fun c y hy => (hα.spatial_smooth 0 c hy).contDiffWithinAt)
      flatProduct_fst_smooth x
    have heA : manifoldPullbackOneForm (fun _ => α) (Prod.fst : M × Plane → M) 0 = A := by
      funext y
      simp only [manifoldPullbackOneForm, manifoldMapDifferential, flatProduct_fst_derivative]
      rfl
    rw [heA] at hd
    have hd' := congrArg (fun L => L v w) hd
    simpa only [manifoldPullbackTwoForm, ContinuousLinearMap.bilinearComp_apply,
      manifoldMapDifferential, flatProduct_fst_derivative, ContinuousLinearMap.coe_fst'] using hd' 
  have hfd (u : E × Plane) : manifoldScalarDifferential f x u = -fderiv ℝ radialArea x.2 u.2 := by
    have hs := (radialArea_hasFDerivAt x.2).const_sub 1
    have hd := mfderiv_comp x hs.differentiableAt.mdifferentiableAt
      ((flatProduct_snd_smooth (E := E) (M := M)).mdifferentiable (by simp) x)
    change mfderiv 𝓘(ℝ,E × Plane) 𝓘(ℝ,ℝ) f x = _ at hd
    have hd' := congrArg (fun L : (E × Plane) →L[ℝ] ℝ => L u) hd
    convert! hd' using 1 <;>
      simp only [manifoldScalarDifferential, mfderiv_eq_fderiv,
        flatProduct_snd_derivative, hs.fderiv, ContinuousLinearMap.comp_apply, neg_apply,
        (radialArea_hasFDerivAt x.2).fderiv, ContinuousLinearMap.coe_snd'] <;> rfl

  rw [he, manifoldExteriorOneForm_add_at
    ((productVerticalLiouville_smooth planarArea).spatial_smooth 0 x (mem_extChartAt_target _))
    (hW.spatial_smooth 0 x (mem_extChartAt_target _)), productVerticalLiouville_exterior planarArea (fun u v => by simp only [planarArea_apply]; ring)]
  simp only [add_apply, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.coe_snd']
  rw [exterior_variable_smul hf (fun c y hy => (hA.spatial_smooth 0 c hy).contDiffWithinAt), hAd]
  simp only [hfd, hAx, f]
  ring

end SymplecticPacking.BranchLargeHigh.Two
