import SymplecticPacking.HighDim.Handle.QuadricAmbientBoxes
import SymplecticPacking.HighDim.Handle.QuadricTightFiniteAtlas

/-!
# Smoothness of the trimmed finite quadric boxes

Every box of the trimmed finite quadric atlas is smooth.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]

def quadricTightFiniteAmbientBox {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) : RawAmbientBox (Affine m) (locus (fun j => (a j:ℂ))) where
  box := quadricTightFiniteBox a hR hsep₀ hsep idx
  inclusion := Subtype.val
  coordinate := match idx with
    | .inl _ => quadricCoordinateProjection none
    | .inr (i,_,_) => quadricCoordinateProjection (some i)
  coordinate_eq := by intro x; cases idx <;> rfl

theorem quadricTightFiniteBox_smooth {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) : (quadricTightFiniteBox a hR hsep₀ hsep idx).Smooth := by
  cases idx with
  | inl i => exact ordinaryGridBox_smooth a hR i.val
  | inr idx => exact uniformBranchBox_smooth a hsep₀ hsep idx.1 idx.2.1 idx.2.2

#check_explicit quadricTightFiniteAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
