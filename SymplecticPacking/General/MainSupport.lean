import SymplecticPacking.General.Main
import SymplecticPacking.General.Ham.TimeSupport

/-!
# Time support of the packing Hamiltonian

The Hamiltonian `hamiltonianOfEmbeddings` of the Hamiltonian end, and hence the
dimension-independent `packingHamiltonian`, vanish for `t ≤ 0` and for `t ≥ 1`.
-/

namespace SymplecticPacking.HamEnd

open SymplecticPacking.Problem SymplecticPacking.General
open SymplecticPacking.General.Ham SymplecticPacking.General.Ham.Isotopy

theorem hamiltonianOfEmbeddings_eq_zero_of_time {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} {D : EmbeddingData n k} (hn : 1 ≤ n) (hc : ∀ i, 0 < c i)
    (hs : BallsDisjoint n k c s) (hD : EmbeddingSpec n k C c D) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) (y : E n) : hamiltonianOfEmbeddings n k c s D t y = 0 := by
  have hF := (isoInput hn hc hs hD).commonIsotopy.1
  exact ofIsotopy_eq_zero_of_time hF ht y

end SymplecticPacking.HamEnd

namespace SymplecticPacking.General

open Problem

/-- The additional time-support clause of Theorem C(i), for the construction term. -/
theorem packingHamiltonian_eq_zero_of_time {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) (y : E n) : packingHamiltonian n k C c s t y = 0 :=
  HamEnd.hamiltonianOfEmbeddings_eq_zero_of_time (by have := hA.two_le; omega)
    hA.c_pos hs (selectEmbeddings_spec hA) ht y

end SymplecticPacking.General
