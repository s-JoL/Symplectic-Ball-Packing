import SymplecticPacking.HighDim.Handle.NativeModelAgreement
import SymplecticPacking.HighDim.Handle.HandleMapSpec

/-!
# Native covector paths and geometric Moser deformations

The native covector paths represent the same geometric Moser deformations.
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
  [NormalSpace M] [SigmaCompactSpace M] {m q k : ℕ}
namespace RawModelAgreement
variable {T : RawToricModel E M m q} {S : ToricModel M m q} (h : RawModelAgreement T S)
include h

theorem relativePath_semantic (reserve : ℝ) (t : ℝ) (v : Fibre m) :
    semanticOneForm T.presentation.inclusion (T.relativePath reserve t v)=
      toricInterp S.Γ (fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p)) (t,v) := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  have hp := congrArg (fun f : ManifoldOneForm Plane M => f x u) (h.primitive_eq (planeMoments v))
  simp only [semanticOneForm,RawToricModel.relativePath,toricInterp,toricPrimitiveInterpolation,
    Pi.add_apply,Pi.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at hp ⊢
  rw [hp]

theorem firstPath_semantic (D : ComparisonDatum m) (p : ℝ × Fibre m) :
    semanticOneForm T.presentation.inclusion (T.firstHandlePath D p)=
      handleFirstPath S.handle S.hb (fibreIsotopy D) (T.handleMass D.reserve)
        (fun r => semanticOneForm T.presentation.inclusion (T.normalPrimitive D.reserve r)) p := by
  have hh := RawAnnularHandle.firstPath_semantic h.handle (fibreIsotopy D)
    (T.handleMass D.reserve ∘ planeMoments) (T.normalPrimitive D.reserve ∘ planeMoments) p
  simpa only [RawToricModel.firstHandlePath,handleFirstPath,h.hb_eq,Function.comp_def] using hh

theorem secondPath_semantic (D : ComparisonDatum m) (a r : Fin k → ℝ) (p : ℝ × Fibre m) :
    semanticOneForm T.presentation.inclusion (T.secondHandlePath D a r p)=
      handleSecondPath S.handle S.hb (fibreIsotopy D) D.K (T.handleMass D.reserve)
        (fun i => smoothCap a r i ∘ planeMoments)
        (fun i => layerClock (k+1) (-S.hb) S.hb i.castSucc)
        (layerClock (k+1) (-S.hb) S.hb (Fin.last k))
        (fun z => semanticOneForm T.presentation.inclusion (T.normalPrimitive D.reserve z)) p := by
  have hh := RawAnnularHandle.secondPath_semantic h.handle (fibreIsotopy D)
    (D.K ∘ planeMoments) (T.handleMass D.reserve ∘ planeMoments)
    (fun i => smoothCap a r i ∘ planeMoments)
    (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
    (layerClock (k+1) (-T.hb) T.hb (Fin.last k))
    (T.normalPrimitive D.reserve ∘ planeMoments) p
  simpa only [RawToricModel.secondHandlePath,handleSecondPath,h.hb_eq,Function.comp_def] using hh
end RawModelAgreement
end SymplecticPacking.HighDim
