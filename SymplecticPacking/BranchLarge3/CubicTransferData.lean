import SymplecticPacking.BranchLarge3.RawTransferPrimitive
import SymplecticPacking.BranchLarge3.RawTransferCutoff
import SymplecticPacking.BranchLarge3.CubicTransferAtlas
import SymplecticPacking.HighDim.Handle.RawFullProductFlow

/-!
# Guards and complete field of the cubic transfer

Finite scalar guards and a native complete field for the cubic transfer.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold
open HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology

def fibreBasis : Module.Basis (Σ _ : Fin 2,Fin 2) ℝ (PlanePhase (Fin 2)) :=
  Pi.basis fun _ => Module.Basis.finTwoProd ℝ

def physicalBasis : Module.Basis (Fin 2 ⊕ (Σ _ : Fin 2,Fin 2)) ℝ CubicPhysicalModel :=
  (Module.Basis.finTwoProd ℝ).prod fibreBasis

def compactBase (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : Set BaseCurve :=
  Prod.fst '' (bridgeMap A B D S L K '' K)

def compactFibre (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : Set DiskPair :=
  Prod.snd '' (bridgeMap A B D S L K '' K)

def primitiveAmbient (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ℝ × Ambient → Ambient →L[ℝ] ℝ :=
  ambientCovector A B D S (1/(L*Real.pi)) L (CubicBridge.delta A B L K)
    (compactBase A B D S L K) (compactFibre A B D S L K)

def primitiveNative (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (t : ℝ) (x : CubicPhysicalSpace) : Ambient →L[ℝ] ℝ :=
  primitiveAmbient A B D S L K (t,((atlas K).inclusion x.1,x.2))

def cutoff (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ℝ × CubicPhysicalSpace → ℝ :=
  transferCut (atlas K) physicalBasis fibreBasis (primitiveAmbient A B D S L K) K


def sourceDomain (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : Set CubicPhysicalSpace :=
  bridgeDomain A B D S L K ∩ bridgeMap A B D S L K ⁻¹'
    famDomain A B D S (1/(L*Real.pi)) (compactBase A B D S L K) (compactFibre A B D S L K)

def familyTarget (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (p : ℝ × CubicPhysicalSpace) : CubicAmbient :=
  famMap A B D S (1/(L*Real.pi)) (compactBase A B D S L K) (compactFibre A B D S L K)
    (p.1,bridgeMap A B D S L K p.2)

/-- Nine displayed scalar guards: the three cutoff plateaux, the two bridge margins, the
two normal-flow domain inequalities, and the two deleted cubic coordinates. -/
def guards (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (p : ℝ × CubicPhysicalSpace) : Fin 9 → ℝ :=
  let KB := compactBase A B D S L K
  let KH := compactFibre A B D S L K
  let Ξ := bridgeMap A B D S L K p.2
  let y : CubicFamily.Y := (inclusion Ξ.1,Ξ.2.2)
  let z := famMap A B D S (1/(L*Real.pi)) KB KH (p.1,Ξ)
  ![4*gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K-2,
    1-p.1^2,
    2*(fibreRadius fibreBasis K+1-UMoser.qn fibreBasis p.2.2)-1,
    A-(squaredRadii (physicalDiskCoordinates L p.2.2)).1-CubicBridge.delta A B L K,
    B-(squaredRadii (physicalDiskCoordinates L p.2.2)).1-
      (squaredRadii (physicalDiskCoordinates L p.2.2)).2-CubicBridge.delta A B L K,
    CubicFamily.R1 KB KH-CubicFamily.nsq y,
    CubicFamily.gsq y.1-CubicFamily.mPar KB,
    Complex.normSq z.1.1,
    Complex.normSq z.1.2]


#check_explicit primitiveAmbient
#check_explicit primitiveNative
#check_explicit cutoff
#check_explicit guards
end SymplecticPacking.BranchLarge3.RawTransfer
