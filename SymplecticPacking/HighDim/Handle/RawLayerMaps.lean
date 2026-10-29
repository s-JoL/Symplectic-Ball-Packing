import SymplecticPacking.HighDim.Handle.RawToricModel
import SymplecticPacking.HighDim.Handle.LayerMapsDef

/-!
# Layer coordinates and layer maps from native handle data

Layer coordinates and maps computed directly from native handle data.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

namespace RawAnnularHandle
variable (H : RawAnnularHandle E M)

def cover (y : Plane) : M := H.forward (cylinderCover y)

def coverCovector (γ : M → E →L[ℝ] ℝ) (y : Plane) : Plane →L[ℝ] ℝ :=
  (γ (H.cover y)).comp (fderiv ℝ H.ambientCover y)

def coverA (γ : M → E →L[ℝ] ℝ) (y : Plane) : ℝ := H.coverCovector γ y (1,0)
def coverB (γ : M → E →L[ℝ] ℝ) (y : Plane) : ℝ := H.coverCovector γ y (0,1)

/-- The clock expression on the native annular sheet, extended by zero elsewhere. -/
def clockPrimitive (b : ℝ) (x : M) : E →L[ℝ] ℝ := by
  classical
  exact if x ∈ H.target then intervalClock (-b) b (H.inverse x).1 • H.dual x else 0

def unshear {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : V →L[ℝ] V →L[ℝ] ℝ} (b : ℝ) (Φ : CompactHamiltonianIsotopy W)
    (p : Plane × V) : M × V :=
  (H.cover p.1,(Φ.map (intervalClock (-b) b p.1.1)).symm p.2)

end RawAnnularHandle

namespace RawToricModel
variable {m q k : ℕ} (T : RawToricModel E M m q)

def handleBackground (Γ : Moments m → M → E →L[ℝ] ℝ) (H : Moments m → ℝ) :
    M → E →L[ℝ] ℝ := Γ 0-H 0 • T.handle.clockPrimitive T.hb

def layerDensity (γ : M → E →L[ℝ] ℝ) : Plane → ℝ :=
  normalizedAreaDensity (T.handle.coverA γ) (T.handle.coverB γ) (circleClockInv T.hδ)

def ballLayerLo (i : Fin k) : ℝ := layerLo (k+1) (-T.hb) T.hb i.castSucc
def ballLayerHi (i : Fin k) : ℝ := layerHi (k+1) (-T.hb) T.hb i.castSucc

def layerCoord (γ : M → E →L[ℝ] ℝ) (a r : Fin k → ℝ) (i : Fin k) :
    Plane × Fibre m → ℝ :=
  areaLayerCoordinate (T.layerDensity γ) (T.ballLayerLo i)
    (layerClock (k+1) (-T.hb) T.hb i.castSucc) (smoothCap a r i)

def layerMomentDomain : Set (Moments m) :=
  {p | (∀ j, 0≤p j) ∧ ∀ ν, ∑ j, T.polytope.b ν j*p j < T.polytope.ℓ ν}

def layerBallMap (K H : Moments m → ℝ) (γ : M → E →L[ℝ] ℝ)
    (a r : Fin k → ℝ) (i : Fin k) : Ambient (m+1) → Plane × Fibre m :=
  layerChartInv (layerBelow K H a r i) (T.layerCoord γ a r i) (T.ballLayerLo i)
    (T.ballLayerHi i) T.layerMomentDomain ∘ thinProduct ((a i-r i)/4) ∘ complexSplitPhase m

def layerMapsOf (Φ : CompactHamiltonianIsotopy (phaseArea (ι:=Fin m)))
    (K H : Moments m → ℝ) (Γ : Moments m → M → E →L[ℝ] ℝ)
    (a r : Fin k → ℝ) (i : Fin k) : Ambient (m+1) → M × Fibre m :=
  T.handle.unshear T.hb Φ ∘ angularReparam (circleClockInv T.hδ) ∘
    T.layerBallMap K H (T.handleBackground Γ H) a r i

end RawToricModel
#check_explicit RawAnnularHandle.coverCovector
#check_explicit RawAnnularHandle.unshear
#check_explicit RawToricModel.layerDensity
#check_explicit RawToricModel.layerMapsOf
end SymplecticPacking.HighDim
