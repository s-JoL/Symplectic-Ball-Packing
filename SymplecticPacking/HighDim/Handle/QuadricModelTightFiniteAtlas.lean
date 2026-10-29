import SymplecticPacking.HighDim.Handle.QuadricModelFiniteAtlas
import SymplecticPacking.HighDim.Handle.QuadricTightFiniteNerve
import SymplecticPacking.HighDim.Handle.QuadricTightAmbientBoxes

/-!
# Support radii of the trimmed quadric atlas

Positivity of the finite support radius at the integer parameters of the quadric model, and
the bound placing every branch parameter inside it.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff

theorem quadricFiniteSupportRadius_pos (m ℓ : ℕ) : 0 < quadricFiniteSupportRadius m ℓ := by
  unfold quadricFiniteSupportRadius quadricRationalParameters
  positivity

theorem quadricFiniteSupportRadius_branch_core (m ℓ : ℕ) (i : Fin (m+2)) :
    ‖(quadricRationalParameters m i:ℂ)‖ < (quadricFiniteSupportRadius m ℓ:ℝ)^2 := by
  have hnonneg (j : Fin (m+2)) : 0 ≤ (quadricRationalParameters m j:ℝ) := by
    dsimp [quadricRationalParameters]
    positivity
  have hi : (quadricRationalParameters m i:ℝ) ≤ ∑ j, (quadricRationalParameters m j:ℝ) :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hR : (quadricRationalParameters m i:ℝ)+1 ≤ (quadricFiniteSupportRadius m ℓ:ℝ) := by
    unfold quadricFiniteSupportRadius
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  rw [quadricRationalParameters_norm]
  nlinarith [hnonneg i]

abbrev QuadricModelTightFiniteIndex (m ℓ : ℕ) :=
  QuadricTightFiniteIndex (quadricRationalParameters m) (quadricFiniteSupportRadius m ℓ)

def quadricModelTightFiniteAmbientBox (m ℓ : ℕ) (idx : QuadricModelTightFiniteIndex m ℓ) :
    RawAmbientBox (Affine (m+2)) (locus (fun j => (quadricRationalParameters m j:ℂ))) :=
  quadricTightFiniteAmbientBox (quadricRationalParameters m)
    (quadricFiniteSupportRadius_nonneg m ℓ)
    (quadricRationalParameters_sep₀ m) (quadricRationalParameters_sep m) idx

def canonicalQuadricTightFiniteAmbientBox (m ℓ : ℕ) (idx : QuadricModelTightFiniteIndex m ℓ) :
    RawAmbientBox (Affine (m+2)) (locus (parameters m)) :=
  (quadricRationalParameters_cast m) ▸ quadricModelTightFiniteAmbientBox m ℓ idx

#check_explicit quadricModelTightFiniteAmbientBox
#check_explicit canonicalQuadricTightFiniteAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
