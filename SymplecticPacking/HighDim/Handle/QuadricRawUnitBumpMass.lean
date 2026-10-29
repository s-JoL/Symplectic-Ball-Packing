import SymplecticPacking.HighDim.Handle.RawUnitBumpIntrinsic
import SymplecticPacking.HighDim.Handle.QuadricRawCanonicalOrientation

/-!
# Intrinsic mass of the quadric root bump

Intrinsic normalization of the explicitly given quadric root bump.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem quadricRawUnitBump_partition_mass
    (B : RawAmbientBox (Affine m) (locus a))
    (centre : locus a) (tag : Option (Fin m)) (hc : centre.val∈regularCoordinate tag)
    (hchart : B.box.chart=rawQuadricRealChart centre tag hc)
    (hinc : B.inclusion=Subtype.val) (hB : B.box.Smooth)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {I : Type} [Fintype I] {L : Set (locus a)}
    (Boxes : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier)) (hUL : B.unitSupport⊆L) :
    partitionFormMass Boxes ρ (semanticTwoForm Subtype.val B.unitBump)=1 := by
  apply B.unitBump_partition_mass (real_inclusion_contMDiff a) hinc hB hsB _ Boxes ρ hρ hUL
  intro c y hy hc'
  rw [hchart] at hy hc' ⊢
  exact rawQuadricChart_canonical_transition_positive centre tag hc c hy hc'

end SymplecticPacking.HighDim.ToricPackingStages
