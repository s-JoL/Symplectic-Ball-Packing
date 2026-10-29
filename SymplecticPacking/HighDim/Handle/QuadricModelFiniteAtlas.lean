import SymplecticPacking.HighDim.Handle.QuadricFiniteAtlas
import OAI.Geometry.BallPacking.SurfaceArea.QuadricSmoothExhaustion

/-!
# Integer parameters of the quadric finite atlas

The rational finite atlas specialized to the quadric model's integer parameters.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open scoped ContDiff Manifold Topology
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

def quadricRationalParameters (m : ℕ) (j : Fin (m+2)) : ℚ := j.val+1

theorem quadricRationalParameters_cast (m : ℕ) :
    (fun j => (quadricRationalParameters m j:ℂ)) = parameters m := by
  funext j
  simp [quadricRationalParameters, parameters]

instance quadricRationalParameters_injective (m : ℕ) :
    Fact (Injective (fun j => (quadricRationalParameters m j:ℂ))) := ⟨by
  rw [quadricRationalParameters_cast]
  exact Fact.out⟩

instance quadricRationalParameters_nonzero (m : ℕ) :
    Fact (∀ j, (quadricRationalParameters m j:ℂ) ≠ 0) := ⟨by
  intro j
  rw [congrFun (quadricRationalParameters_cast m) j]
  exact (parameters_nonzero m).out j⟩

theorem quadricRationalParameters_norm (m : ℕ) (j : Fin (m+2)) :
    ‖(quadricRationalParameters m j:ℂ)‖ = (quadricRationalParameters m j:ℝ) := by
  have he : (quadricRationalParameters m j:ℂ) = ((quadricRationalParameters m j:ℝ):ℂ) := by simp
  rw [he, Complex.norm_real]
  exact abs_of_nonneg (by dsimp [quadricRationalParameters]; positivity)

theorem quadricRationalParameters_sep₀ (m : ℕ) (i : Fin (m+2)) :
    1 ≤ ‖(quadricRationalParameters m i:ℂ)‖ := by
  rw [quadricRationalParameters_norm]
  simp only [quadricRationalParameters, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
  linarith [Nat.cast_nonneg (α := ℝ) i.val]

theorem quadricRationalParameters_sep (m : ℕ) (i j : Fin (m+2)) (hji : j≠i) :
    1 ≤ ‖(quadricRationalParameters m i:ℂ)-(quadricRationalParameters m j:ℂ)‖ := by
  have hne : i.val ≠ j.val := by intro h; exact hji (Fin.ext h).symm
  have he : (quadricRationalParameters m i:ℂ)-(quadricRationalParameters m j:ℂ) =
      (((i.val:ℝ)-(j.val:ℝ)):ℂ) := by
    simp [quadricRationalParameters]
  rw [he, ← Complex.ofReal_sub, Complex.norm_real]
  change 1 ≤ |(i.val:ℝ)-(j.val:ℝ)|
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_nonneg (by linarith)]
    linarith

def quadricFiniteSupportRadius (m ℓ : ℕ) : ℚ :=
  1+∑ j, quadricRationalParameters m j+ℓ

theorem quadricFiniteSupportRadius_nonneg (m ℓ : ℕ) : 0 ≤ quadricFiniteSupportRadius m ℓ := by
  unfold quadricFiniteSupportRadius quadricRationalParameters
  positivity

theorem quadricFiniteSupportRadius_exhaustion (m ℓ : ℕ) :
    (quadricFiniteSupportRadius m ℓ:ℝ)+1 = exhaustionRadius (parameters m) ℓ := by
  unfold quadricFiniteSupportRadius exhaustionRadius
  push_cast
  have he : (∑ j, (quadricRationalParameters m j:ℝ)) = ∑ j, ‖parameters m j‖ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← quadricRationalParameters_norm]
    exact congrArg norm (congrFun (quadricRationalParameters_cast m) j)
  rw [he]
  ring

def quadricModelFiniteBox (m ℓ : ℕ)
    (idx : QuadricFiniteIndex (quadricRationalParameters m) (quadricFiniteSupportRadius m ℓ)) :
    RawCoordinateBox (locus (fun j => (quadricRationalParameters m j:ℂ))) :=
  quadricFiniteBox (quadricRationalParameters m) (quadricFiniteSupportRadius_nonneg m ℓ)
    (quadricRationalParameters_sep₀ m) (quadricRationalParameters_sep m) idx

/-- The same box data at the literal parameter function used by the model providers. -/
def canonicalQuadricFiniteBox (m ℓ : ℕ)
    (idx : QuadricFiniteIndex (quadricRationalParameters m) (quadricFiniteSupportRadius m ℓ)) :
    RawCoordinateBox (locus (parameters m)) :=
  (quadricRationalParameters_cast m) ▸ quadricModelFiniteBox m ℓ idx

/-- Coefficients consumed by the raw algorithm; no manifold structure is an input. -/
def quadricModelFinitePartitionWeight (m ℓ : ℕ)
    (idx : QuadricFiniteIndex (quadricRationalParameters m) (quadricFiniteSupportRadius m ℓ))
    (x : locus (fun j => (quadricRationalParameters m j:ℂ))) : ℝ :=
  RawBoxFamily.partitionWeight (quadricModelFiniteBox m ℓ) idx x

#check_explicit quadricModelFiniteBox
#check_explicit canonicalQuadricFiniteBox
#check_explicit quadricModelFinitePartitionWeight
end SymplecticPacking.HighDim.ToricPackingStages
