import SymplecticPacking.HighDim.Handle.RawNormalPrimitive
import SymplecticPacking.HighDim.Handle.RawHandlePaths
import SymplecticPacking.HighDim.Handle.RawPathCutoff
import SymplecticPacking.HighDim.Comparator.Datum

/-!
# The native three-stage packing formula

The native three-stage packing formula. Every map is evaluated from the raw records.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] {m q k : ℕ}

namespace RawToricModel
variable (T : RawToricModel E M m q)

def region : Set (M × Fibre m) := T.base ×ˢ (planeMoments ⁻¹' T.polytope.set)

def productBasis (m : ℕ) :
    Module.Basis (Fin 2 ⊕ (Σ _ : Fin m,Fin 2)) ℝ (Plane × Fibre m) :=
  (Module.Basis.finTwoProd ℝ).prod (Pi.basis fun _ : Fin m => Module.Basis.finTwoProd ℝ)

def fibreBasis (m : ℕ) : Module.Basis (Σ _ : Fin m,Fin 2) ℝ (Fibre m) :=
  Pi.basis fun _ : Fin m => Module.Basis.finTwoProd ℝ

def relativePath (reserve : ℝ) (t : ℝ) (v : Fibre m) (x : M) : E →L[ℝ] ℝ :=
  (1-t) • T.physicalPrimitive (planeMoments v) x+t • T.normalPrimitive reserve (planeMoments v) x

def firstHandlePath (D : ComparisonDatum m) (p : ℝ × Fibre m) : M → E →L[ℝ] ℝ :=
  T.handle.firstPath T.hb (fibreIsotopy D) (T.handleMass D.reserve ∘ planeMoments)
    (T.normalPrimitive D.reserve ∘ planeMoments) p

def secondHandlePath (D : ComparisonDatum m) (a r : Fin k → ℝ) (p : ℝ × Fibre m) :
    M → E →L[ℝ] ℝ :=
  T.handle.secondPath T.hb (fibreIsotopy D) (D.K ∘ planeMoments) (T.handleMass D.reserve ∘ planeMoments)
    (fun i => smoothCap a r i ∘ planeMoments)
    (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
    (layerClock (k+1) (-T.hb) T.hb (Fin.last k))
    (T.normalPrimitive D.reserve ∘ planeMoments) p

/-- A larger finite atlas is supplied separately from the correction atlas. Its inner boxes
cover the whole compact model, including its boundary. -/
def pathCutoff {U : Set M} (F : RawSurfacePresentation E M U)
    (P : ℝ → Fibre m → M → E →L[ℝ] ℝ) : ℝ × (M × Fibre m) → ℝ :=
  NativePathCutoff.transferCut F (productBasis m) (fibreBasis m)
    (fun t => nativeCouplingPrimitive phaseArea (P t)) T.region

def pathFlow {U : Set M} (F : RawSurfacePresentation E M U)
    (P : ℝ → Fibre m → M → E →L[ℝ] ℝ) (t : ℝ) (x : M × Fibre m) : M × Fibre m :=
  F.fullMoserFlow (fun s => nativeCouplingPrimitive phaseArea (P s)) (T.pathCutoff F P) t x

def layerMaps (D : ComparisonDatum m) (a r : Fin k → ℝ) : Fin k → Ambient (m+1) → M × Fibre m :=
  T.layerMapsOf (fibreIsotopy D) D.K (T.handleMass D.reserve) (T.normalPrimitive D.reserve) a r

def packingSource (a r : Fin k → ℝ) (i : Fin k) : ℝ := (3*a i+r i)/4

/-- Relative normalization, first handle path, second handle path, and the native layer map. -/
def packing {U : Set M} (F : RawSurfacePresentation E M U)
    (D : ComparisonDatum m) (a r : Fin k → ℝ) (i : Fin k) : Ambient (m+1) → M × Fibre m :=
  let rr := packingSource a r
  nativeInverse (T.pathFlow F (T.relativePath D.reserve) 1) ∘
    nativeInverse (T.pathFlow F (fun t v => T.firstHandlePath D (t,v)) 1) ∘
      nativeInverse (T.pathFlow F (fun t v => T.secondHandlePath D a rr (t,v)) 1) ∘
        T.layerMaps D a rr i

end RawToricModel
#check_explicit RawToricModel.pathCutoff
#check_explicit RawToricModel.pathFlow
#check_explicit RawToricModel.packing
end SymplecticPacking.HighDim
