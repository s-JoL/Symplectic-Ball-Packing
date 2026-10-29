import SymplecticPacking.HighDim.Handle.QuadricModelPresentation

/-!
# Coverage of the correction core by the quadric presentation

The finite presentation covers the entire correction core in native coordinates.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix

variable {q : ℕ} {a b : Fin q → ℂ} {r s t : ℝ}

theorem transportQuadricPresentation_inclusion (hab : a=b) (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : D.inclusion=Subtype.val) :
    (transportQuadricPresentation hab hrs D).inclusion=Subtype.val := by
  subst b
  subst s
  exact hD

theorem transportQuadricPresentation_cover (hab : a=b) (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : projectionDomain a t⊆⋃ i,(D.boxes i).box.inner) :
    projectionDomain b t⊆⋃ i,((transportQuadricPresentation hab hrs D).boxes i).box.inner := by
  subst b
  subst s
  exact hD

theorem quadricModelRawPresentation_inclusion (m ℓ : ℕ) :
    (quadricModelRawPresentation m ℓ).inclusion=Subtype.val :=
  transportQuadricPresentation_inclusion _ _ _ rfl

theorem quadricModelRawPresentation_cover (m ℓ : ℕ) :
    projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)⊆
      ⋃ i,((quadricModelRawPresentation m ℓ).boxes i).box.inner :=
  transportQuadricPresentation_cover _ _ _
    (quadricFinitePresentation_cover (quadricRationalParameters m)
      (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
      (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ))

end SymplecticPacking.HighDim.ToricPackingStages
