import OAI.Geometry.BallPacking.Surfaces.DiagonalQuadric
import SymplecticPacking.Explicit

/-!
# Centres of the quadric coordinate boxes

Explicit points for finite coordinate-box certificates on diagonal quadric curves.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

/-- A root sign is finite data; the square root itself is Mathlib's principal root. -/
def signedRoot (ε : Bool) (z : ℂ) : ℂ := if ε then -Complex.sqrt z else Complex.sqrt z

theorem signedRoot_sq (ε : Bool) (z : ℂ) : signedRoot ε z ^ 2 = z := by
  cases ε <;> simp [signedRoot, sqrt_sq_complex]

theorem signedRoot_ne_zero (ε : Bool) {z : ℂ} (hz : z ≠ 0) : signedRoot ε z ≠ 0 := by
  intro h
  have hs := signedRoot_sq ε z
  rw [h, zero_pow (by decide)] at hs
  exact hz hs.symm

def ordinaryPresentationCenter {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool) (u : ℂ) : locus a :=
  ⟨(u, fun j => signedRoot (ε j) (u^2-a j)), mem_locus.mpr (fun j => signedRoot_sq _ _)⟩

def branchPresentationCenter {m : ℕ} (a : Fin m → ℂ) (i : Fin m)
    (ε₀ : Bool) (ε : Fin m → Bool) : locus a :=
  ⟨(signedRoot ε₀ (a i), fun j => if j=i then 0 else signedRoot (ε j) (a i-a j)), by
    apply mem_locus.mpr
    intro j
    change (if j=i then 0 else signedRoot (ε j) (a i-a j))^2 = signedRoot ε₀ (a i)^2-a j
    rw [signedRoot_sq]
    by_cases h : j=i
    · subst j
      simp
    · rw [if_neg h, signedRoot_sq]⟩

theorem branchPresentationCenter_regular {m : ℕ} (a : Fin m → ℂ) (ha : Injective a)
    (ha₀ : ∀ j, a j ≠ 0) (i : Fin m) (ε₀ : Bool) (ε : Fin m → Bool) :
    (branchPresentationCenter a i ε₀ ε : Affine m) ∈ regularCoordinate (some i) := by
  refine ⟨signedRoot_ne_zero ε₀ (ha₀ i), ?_⟩
  intro j hji
  change (if j=i then 0 else signedRoot (ε j) (a i-a j)) ≠ 0
  rw [if_neg hji]
  exact signedRoot_ne_zero (ε j) (sub_ne_zero.mpr (fun h => hji (ha h).symm))

/-- Every square root is one of the two explicitly signed roots. -/
theorem signedRoot_complete {z w : ℂ} (hz : z^2 = w) :
    ∃ ε : Bool, signedRoot ε w = z := by
  have hs : Complex.sqrt w ^ 2 = z^2 := (sqrt_sq_complex w).trans hz.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change -Complex.sqrt w = z
    rw [h, neg_neg]

/-- The finite sign vector gives every point of a fixed projection fibre. -/
theorem ordinaryPresentationCenter_complete {m : ℕ} (a : Fin m → ℂ) (x : locus a) :
    ∃ ε : Fin m → Bool, ordinaryPresentationCenter a ε x.val.1 = x := by
  have hh (j : Fin m) := signedRoot_complete (mem_locus.mp x.property j)
  choose ε hε using hh
  refine ⟨ε, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    exact hε j

#check_explicit signedRoot
#check_explicit ordinaryPresentationCenter
#check_explicit branchPresentationCenter
end SymplecticPacking.HighDim.ToricPackingStages
