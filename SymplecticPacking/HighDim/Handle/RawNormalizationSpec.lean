import SymplecticPacking.HighDim.Handle.RawNormalPrimitive
import SymplecticPacking.HighDim.Handle.RawManifoldBridge

/-!
# Specification of the native normalization

Proof interface for the native normalization algorithm. None of these outputs is model data.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {m q : ℕ}

structure RawNormalizationSpec (T : RawToricModel E M m q) (reserve : ℝ) (outer : Moments m → ℝ) : Prop where
  primitive_smooth : ContMDiff ((𝓘(ℝ,Moments m)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
    (fun z : Moments m × M => T.normalPrimitive reserve z.1 z.2)
  primitive_exterior : ∀ p,manifoldExteriorOneForm (semanticOneForm T.presentation.inclusion
    (T.normalPrimitive reserve p))=semanticTwoForm T.presentation.inclusion
      (T.physicalForm p+T.presentation.calibratedDefect T.handleDensity (T.removedForm reserve p))
  annular_exterior : ∀ p x,x∈T.handle.target →
    manifoldExteriorOneForm (semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p)) x=
      T.backgroundCoefficient reserve • semanticTwoForm T.presentation.inclusion T.referenceForm x+
        T.handleMass reserve p • semanticTwoForm T.presentation.inclusion T.handleDensity x
  compact_difference : ∃ K : Set M,IsCompact K ∧ K⊆interior T.base ∧
    ∀ p x,x∉K → semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p) x=
      semanticOneForm T.presentation.inclusion (T.physicalPrimitive p) x
  positive : ∀ p∈T.polytope.set,∀ b y,y∈(extChartAt 𝓘(ℝ,Plane) b).target →
    (extChartAt 𝓘(ℝ,Plane) b).symm y∈T.base →
    0<chartTwoForm (manifoldExteriorOneForm (semanticOneForm T.presentation.inclusion
      (T.normalPrimitive reserve p))) b y (1,0) (0,1)
  reference_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ T.referencePrimitive
  reference_exterior : manifoldExteriorOneForm (semanticOneForm T.presentation.inclusion T.referencePrimitive)=
    semanticTwoForm T.presentation.inclusion T.referenceForm
  background_pos : 0<T.backgroundCoefficient reserve
  normal_region : ∃ W : Set M,IsOpen W ∧ T.handle.forward '' AnnularHandleData.band T.hb⊆W ∧
    W⊆T.handle.target ∧ ∀ p x,x∈W →
      semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p) x=
        T.backgroundCoefficient reserve • semanticOneForm T.presentation.inclusion T.referencePrimitive x+
          (intervalClock (-T.hb) T.hb (T.handle.inverse x).1*T.handleMass reserve p) •
            semanticOneForm T.presentation.inclusion T.handle.dual x
  mass_smooth : ContDiff ℝ ∞ (T.handleMass reserve)
  mass_nonneg : ∀ p∈T.polytope.set,0≤T.handleMass reserve p
  mass_lower : ∀ p∈T.polytope.set,outer p-reserve/16≤T.handleMass reserve p

end SymplecticPacking.HighDim
