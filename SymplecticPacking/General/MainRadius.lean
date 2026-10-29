import SymplecticPacking.General.Main
import SymplecticPacking.General.Ham.Isotopy.TargetRadii
import SymplecticPacking.General.Ham.PreciseSupport

/-!
# The explicit support radius

`packingSupportRadius n k C c s` is an explicit radius outside which the Hamiltonian
`packingHamiltonian n k C c s` vanishes for all times (`packingHamiltonian_support_radius`,
Theorem C(i)); `packingSupportSet` is the compact set swept by the cut-off balls under the
common isotopy, which contains the support.
-/

noncomputable section
namespace SymplecticPacking.General

open Metric Set Problem Ham Ham.Isotopy

/-- The explicit radius of Theorem C(i): `isotopyRadius` of the common isotopy of the selected
embeddings with target radius `capRadius C`; `packingHamiltonian n k C c s` vanishes outside
the closed ball of this radius for all times. -/
def packingSupportRadius (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n) : ℝ :=
  let D := selectEmbeddings n k C c
  isotopyRadius D.f s (rad c s D 3) (capRadius C)

/-- The image of `[0,1] × B̄(r₂ i)` under the common isotopy of the selected embeddings; it
contains the spatial support of `packingHamiltonian n k C c s`. -/
def packingSupportSet (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n) : Set (E n) :=
  let D := selectEmbeddings n k C c
  isotopySupport (isoF D.f s (rad c s D 3)) (rad c s D 2)

theorem packingSupportSet_compact {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    IsCompact (packingSupportSet n k C c s) := by
  have hi := isoInput (by have := hA.two_le; omega) hA.c_pos hs (selectEmbeddings_spec hA)
  exact isotopySupport_compact hi.commonIsotopy.1

theorem packingHamiltonian_support_precise {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    ∀ t,∀ x ∉ packingSupportSet n k C c s,packingHamiltonian n k C c s t x=0 := by
  have hi := isoInput (by have := hA.two_le; omega) hA.c_pos hs (selectEmbeddings_spec hA)
  exact ofIsotopy_support_precise hi.commonIsotopy.1

theorem packingSupportSet_subset_radius {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    packingSupportSet n k C c s ⊆ closedBall 0 (packingSupportRadius n k C c s) := by
  have hi := targetIsoInput (by have := hA.two_le; omega) hA.one_le hA.C_pos
    hA.c_pos hs (selectEmbeddings_spec hA)
  intro x hx
  obtain ⟨i,p,hp,rfl⟩ := mem_iUnion.mp hx
  apply mem_closedBall_zero_iff.mpr
  apply hi.isoF_norm_le i p.1
  exact closedBall_subset_closedBall (hi.toIsoInput.radii i).2.2.1.le hp.2

/-- The radius printed in the paper bounds the spatial support of its Hamiltonian. -/
theorem packingHamiltonian_support_radius {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    ∀ t,∀ x ∉ closedBall (0 : E n) (packingSupportRadius n k C c s),
      packingHamiltonian n k C c s t x=0 := by
  have hi := targetIsoInput (by have := hA.two_le; omega) hA.one_le hA.C_pos
    hA.c_pos hs (selectEmbeddings_spec hA)
  exact ofIsotopy_support (fun i t u hu => hi.isoF_norm_le i t hu)

end SymplecticPacking.General
