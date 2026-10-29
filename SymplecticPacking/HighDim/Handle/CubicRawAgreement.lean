import SymplecticPacking.HighDim.Handle.NativeModelAgreement
import SymplecticPacking.HighDim.Handle.QuadricRawHandlePaths
import SymplecticPacking.HighDim.Handle.CubicRawProvider

/-!
# Semantic model of the cubic raw provider

The cubic raw provider has its own geometric reference at the certified level and fixed native handle.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] primitiveExt RawCubic.physicalExtension quadricTreeAt quadricTreeOrder quadricTreePrefix
local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _

/-- This semantic model is used only in proof statements; native maps evaluate `cubicRawModel`. -/
def cubicRawSemanticModel (A B D S : ℕ) (c L : ℝ) (q ℓ : ℕ) (Δ : Polytope 2 q) : ToricModel BaseCurve 2 q where
  Δ := Δ
  base := cubicExhaustion ℓ
  Λ := curveFSForm (parameters 0) (1/Real.pi)
  dens z := surfaceFormRatio (curveFSForm (parameters 0) (1/Real.pi))
    (manifoldExteriorOneForm (primitiveExt A B D S c L Δ.set ℓ z.1)) z.2
  Γ := primitiveExt A B D S c L Δ.set ℓ
  handle := BranchSmall.quadricHandleData 0
  hb := (BranchSmall.quadricHandleData 0).width/2
  hδ := 1/4

variable {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ) (c L : ℝ) (q ℓ : ℕ)
  (Δ : Polytope 2 q) (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
  (hm : 0<PrimExt.margin A B L Δ.set) (hmA : PrimExt.margin A B L Δ.set≤A)

theorem cubicRawModel_agreement : RawModelAgreement
    (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA)
    (cubicRawSemanticModel A B D S c L q ℓ Δ) where
  polytope_eq := rfl
  base_eq := rfl
  primitive_eq p := by
    rw [show (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion 0 ℓ]
    funext x
    exact (RawCubic.physicalExtension_eq A B D S c L Δ.set ℓ p x).symm
  reference_eq := by
    rw [show (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion 0 ℓ]
    exact quadricReferenceForm_semantic 0
  handle := by
    rw [show (cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA).presentation.inclusion=Subtype.val from
      quadricModelRawPresentation_inclusion 0 ℓ]
    exact quadricRawHandle_agreement 0 (b := (1:ℝ)/16) (by norm_num) (by change 1/16<(1:ℝ)/8; norm_num)
  hb_eq := by
    change (1:ℝ)/16=(BranchSmall.explicitCylinderWidth 0/2)/2
    norm_num [BranchSmall.explicitCylinderWidth]
  hδ_eq := rfl

include hA hAB hΔc in
theorem cubicRawSemanticModel_spec (hΔ : Δ.Spec) (hc : 0<c) (hB : 3*B<D) (hS : 3*S<D)
    (hPS : MapsTo (physicalParameter L) Δ.set (Radial.lowerTrapezoid A B)) :
    (cubicRawSemanticModel A B D S c L q ℓ Δ).Spec := by
  let Γ := primitiveExt A B D S c L Δ.set ℓ
  let Λ := curveFSForm (parameters 0) (1/Real.pi)
  have hΓ : SmoothOneFormFamily Γ := (primitiveExt_spec hA hAB D S c L hΔc hPS ℓ).1
  have hΛ : SmoothTwoForm Λ := curveFSForm_smooth (parameters 0) (1/Real.pi)
  have hsΛ : ∀ x u v,Λ x u v = -Λ x v u := curveFSForm_skew (parameters 0) (1/Real.pi)
  have hpΛ : ∀ b y,y∈(extChartAt 𝓘(ℝ,Plane) b).target → 0<chartTwoForm Λ b y (1,0) (0,1) :=
    fun b y hy => curveFSForm_positive (parameters 0) (one_div_pos.mpr Real.pi_pos) b hy
  have hcurv (p : Moments 2) (hp : p∈Δ.set) (b : BaseCurve) (y : Plane)
      (hy : y∈(extChartAt 𝓘(ℝ,Plane) b).target) (hx : (extChartAt 𝓘(ℝ,Plane) b).symm y∈cubicExhaustion ℓ) :
      0<chartTwoForm (manifoldExteriorOneForm (Γ p)) b y (1,0) (0,1) := by
    dsimp only [chartTwoForm]
    rw [physicalPrimitive_extension_curvature (primitiveExt_spec hA hAB D S c L hΔc hPS ℓ).2 hp (hPS hp) hx]
    exact radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy
  have hΩ : SmoothTwoFormFamily (fun p : Moments 2 => manifoldExteriorOneForm (Γ p)) :=
    manifoldExteriorOneForm_family_smooth hΓ
  have hΩsk : ∀ p x u v,manifoldExteriorOneForm (Γ p) x u v= -manifoldExteriorOneForm (Γ p) x v u :=
    fun p x u v => manifoldExteriorOneForm_skew _ _ _ _
  have hκ : ContMDiff ((𝓘(ℝ,Moments 2)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun z : Moments 2 × BaseCurve => surfaceFormRatio Λ (manifoldExteriorOneForm (Γ z.1)) z.2) :=
    surfaceFormRatio_smooth (P:=Moments 2) (M:=BaseCurve) (Λ:=Λ)
      (Ω:=fun p => manifoldExteriorOneForm (Γ p)) hΛ hsΛ hpΛ hΩ hΩsk
  have hK := projectionDomain_interior_connected (exhaustionRadius_pos (parameters 0) ℓ)
    (exhaustionRadius_branch (parameters 0) ℓ)
  have hin := BranchSmall.quadricHandleData_in_exhaustion 0 ℓ
  refine { Δ_spec := hΔ
           base_compact := cubicExhaustion_compact ℓ
           base_conn := hK.isPreconnected
           base_ne := hK.nonempty
           base_boundary := projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters 0) ℓ)
             (exhaustionRadius_branch (parameters 0) ℓ)
           orient := positivePlaneTransitions (parameters 0)
           hb_pos := half_pos (BranchSmall.quadricHandleData 0).width_pos
           hb_lt := by dsimp [cubicRawSemanticModel]; linarith [(BranchSmall.quadricHandleData 0).width_pos]
           hδ_pos := by change (0:ℝ)<1/4; norm_num
           hδ_lt := by change (1:ℝ)/4<1/2; norm_num
           handle_in_base := (subset_union_left).trans hin
           dual_in_base := (subset_union_right).trans hin
           handle_orient := BranchSmall.quadricHandleData_positive 0
           clock := BranchSmall.quadricHandleData_clock 0
           Λ_smooth := hΛ
           Λ_skew := hsΛ
           Λ_pos := hpΛ
           dens_smooth := ?_
           dens_pos := ?_
           Γ_smooth := hΓ
           dΓ := ?_ }
  · exact hκ
  · intro p hp x hx
    change x∈cubicExhaustion ℓ at hx
    exact div_pos (hcurv p hp x _ (mem_extChartAt_target x) (by simpa using hx))
      (hpΛ x _ (mem_extChartAt_target x))
  · intro p x
    exact surface_form_scalar (Ω:=manifoldExteriorOneForm (Γ p)) (hΩsk p) hsΛ hpΛ x

include hA hAB hΔc hm hmA in
theorem cubicRawSemanticModel_area_eq (hmodel : (cubicRawSemanticModel A B D S c L q ℓ Δ).Spec) :
    cubicRawOuterArea A B D S c L Δ.set ℓ=(cubicRawSemanticModel A B D S c L q ℓ Δ).baseArea hmodel := by
  funext p
  apply compactSurfaceFormIntegral_congr (cubicExhaustion_compact ℓ)
  intro x _
  have he := congrArg (fun A => A x) (CubicRawPhysical.form_semantic hA hAB D S c L Δ.set ℓ hm hmA p)
  exact he.symm.trans (hmodel.dΓ p x)

end SymplecticPacking.HighDim.ToricPackingStages
