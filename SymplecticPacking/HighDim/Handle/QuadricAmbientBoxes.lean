import SymplecticPacking.HighDim.Handle.QuadricFiniteAtlas
import SymplecticPacking.HighDim.Handle.RawAmbientBox

/-!
# Ambient coordinate projections for the quadric atlas

Ambient linear-coordinate interfaces for the finite quadric atlas.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

def quadricCoordinateProjection {m : ℕ} (c : Option (Fin m)) : Affine m →L[ℝ] Plane :=
  (Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp ((curveCoordinate c).restrictScalars ℝ)

variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]

def quadricFiniteAmbientBox {R : ℚ} (hR : 0 ≤ R) (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖)
    (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricFiniteIndex a R) : RawAmbientBox (Affine m) (locus (fun j => (a j:ℂ))) where
  box := quadricFiniteBox a hR hsep₀ hsep idx
  inclusion := Subtype.val
  coordinate := match idx with
    | .inl _ => quadricCoordinateProjection none
    | .inr (i, _, _) => quadricCoordinateProjection (some i)
  coordinate_eq := by intro x; cases idx <;> rfl

#check_explicit quadricFiniteAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
