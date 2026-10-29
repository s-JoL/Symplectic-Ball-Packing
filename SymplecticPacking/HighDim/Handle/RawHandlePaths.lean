import SymplecticPacking.HighDim.Handle.RawLayerMaps
import SymplecticPacking.HighDim.Handle.RawFullProductFlowSpec

/-!
# The two handle paths as ambient covector formulas

The two handle paths as ambient covector formulas.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
namespace RawAnnularHandle
variable (A : RawAnnularHandle E M) {W : V →L[ℝ] V →L[ℝ] ℝ}

def firstCorrection (b : ℝ) (Φ : CompactHamiltonianIsotopy W) (H : V → ℝ)
    (p : ℝ × V) (x : M) : E →L[ℝ] ℝ :=
  surfaceSuspensionCoefficient Φ (intervalClock (-b) b) (p,(A.inverse x).1) • A.radial b x +
    surfaceFirstCorrectionCoefficient Φ (intervalClock (-b) b) H (p,(A.inverse x).1) • A.dual x

def firstPath (b : ℝ) (Φ : CompactHamiltonianIsotopy W) (H : V → ℝ)
    (Γ : V → M → E →L[ℝ] ℝ) (p : ℝ × V) (x : M) : E →L[ℝ] ℝ := by
  classical
  exact Γ p.2 x + if x∈A.target then A.firstCorrection b Φ H p x else 0

def secondPath {κ : Type*} [Fintype κ] (b : ℝ) (Φ : CompactHamiltonianIsotopy W)
    (K H : V → ℝ) (h : κ → V → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → M → E →L[ℝ] ℝ) (p : ℝ × V) (x : M) : E →L[ℝ] ℝ := by
  classical
  exact A.firstPath b Φ H Γ (1,p.2) x+(p.1*(K p.2-H p.2)) • A.dual x+
    if x∈A.target then
      surfaceSecondExtraCoefficient Φ (intervalClock (-b) b) K H h ρ ρ₀
        (p,(A.inverse x).1) • A.dual x else 0

section comparison
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

/-- These equalities are used in proofs only. They are not construction inputs. -/
structure Agreement (ι : M → E) (D : AnnularHandleData Plane M) (b : ℝ) : Prop where
  target_eq : A.target=D.chart.target
  forward_eq : A.forward=D.chart
  inverse_eq : A.inverse=D.chart.symm
  dual_eq : semanticOneForm ι A.dual=D.dual
  radial_eq : semanticOneForm ι (A.radial b)=D.radial b

variable {A}
theorem firstPath_semantic {ι : M → E} {D : AnnularHandleData Plane M} {b : ℝ}
    (ha : A.Agreement ι D b) (Φ : CompactHamiltonianIsotopy W) (H : V → ℝ)
    (Γ : V → M → E →L[ℝ] ℝ) (p : ℝ × V) :
    semanticOneForm ι (A.firstPath b Φ H Γ p)=D.globalSurfaceFirstPrimitive b Φ H
      (fun v => semanticOneForm ι (Γ v)) p := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hd := congrArg (fun f : ManifoldOneForm Plane M => f x v) ha.dual_eq
  have hr := congrArg (fun f : ManifoldOneForm Plane M => f x v) ha.radial_eq
  by_cases hx : x∈A.target
  · have hxs : x∈D.chart.target := ha.target_eq ▸ hx
    simp only [semanticOneForm,firstPath,firstCorrection,if_pos hx,
      AnnularHandleData.globalSurfaceFirstPrimitive,Pi.add_apply,
      extendManifoldOneForm_inside hxs,AnnularHandleData.handleFirstCorrection,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ha.inverse_eq] at hd hr ⊢
    rw [hd,hr]
  · have hxs : x∉D.chart.target := ha.target_eq ▸ hx
    simp only [semanticOneForm,firstPath,if_neg hx,
      AnnularHandleData.globalSurfaceFirstPrimitive,Pi.add_apply,
      extendManifoldOneForm_outside hxs,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,add_zero]

theorem secondPath_semantic {ι : M → E} {D : AnnularHandleData Plane M} {b : ℝ}
    (ha : A.Agreement ι D b) {κ : Type*} [Fintype κ]
    (Φ : CompactHamiltonianIsotopy W) (K H : V → ℝ)
    (h : κ → V → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → M → E →L[ℝ] ℝ) (p : ℝ × V) :
    semanticOneForm ι (A.secondPath b Φ K H h ρ ρ₀ Γ p)=
      D.globalSurfaceSecondPrimitive b Φ K H h ρ ρ₀
        (fun v => semanticOneForm ι (Γ v)) p := by
  classical
  have hfirst := firstPath_semantic ha Φ H Γ (1,p.2)
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hd := congrArg (fun f : ManifoldOneForm Plane M => f x v) ha.dual_eq
  have hf := congrArg (fun f : ManifoldOneForm Plane M => f x v) hfirst
  by_cases hx : x∈A.target
  · have hxs : x∈D.chart.target := ha.target_eq ▸ hx
    simp only [semanticOneForm,secondPath,if_pos hx,
      AnnularHandleData.globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_inside hxs,AnnularHandleData.handleSecondExtra,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ha.inverse_eq] at hd hf ⊢
    rw [hf,hd]
  · have hxs : x∉D.chart.target := ha.target_eq ▸ hx
    simp only [semanticOneForm,secondPath,if_neg hx,
      AnnularHandleData.globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_outside hxs,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      ContinuousLinearMap.zero_apply,add_zero] at hd hf ⊢
    rw [hf,hd]

theorem unshear_eq {ι : M → E} {D : AnnularHandleData Plane M} {b : ℝ}
    (ha : A.Agreement ι D b) (Φ : CompactHamiltonianIsotopy W) :
    A.unshear b Φ=D.annularUnshearMap b Φ := by
  funext p
  rw [AnnularHandleData.annularUnshearMap_apply]
  simp only [unshear,cover,ha.forward_eq]
  rfl

end comparison
end RawAnnularHandle

namespace ToricPackingStages
/-- Add the fixed vertical Liouville covector to an ambient horizontal primitive. -/
def nativeCouplingPrimitive (W : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : V → M → E →L[ℝ] ℝ) (x : M × V) : (E × V) →L[ℝ] ℝ :=
  ((1/2:ℝ) • W x.2).comp (ContinuousLinearMap.snd ℝ E V)+
    (Γ x.2 x.1).comp (ContinuousLinearMap.fst ℝ E V)

section comparison
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
theorem nativeCouplingPrimitive_semantic (ι : M → E)
    (W : V →L[ℝ] V →L[ℝ] ℝ) (Γ : V → M → E →L[ℝ] ℝ) :
    semanticFullOneForm ι (nativeCouplingPrimitive W Γ)=
      productCouplingPrimitive W (fun v => semanticOneForm ι (Γ v)) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [productCouplingPrimitive,Pi.add_apply,ContinuousLinearMap.add_apply,productVerticalLiouville_apply,
    productHorizontalLift_apply]
  rfl

end comparison

end ToricPackingStages
#check_explicit RawAnnularHandle.firstPath
#check_explicit RawAnnularHandle.secondPath
#check_explicit ToricPackingStages.nativeCouplingPrimitive
end SymplecticPacking.HighDim
