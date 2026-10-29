import SymplecticPacking.General.MainSupport
import SymplecticPacking.General.Ham.GlobalFlow

/-!
# The time-one flow of the packing Hamiltonian

Global smooth symplectic flow for the packing Hamiltonian.
-/

noncomputable section
namespace SymplecticPacking.General
open Problem Ham
open Set Function
open scoped ContDiff

def packingFlow (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (t : ℝ) (x : E n) : E n := Return.flow (Problem.hamVF (packingHamiltonian n k C c s)) t x

theorem packingHamiltonian_compact {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    HasCompactSupport (Function.uncurry (packingHamiltonian n k C c s)) := by
  obtain ⟨K,hK,hzero⟩ := (packing_main hA hs).compactSupport
  exact hasCompactSupport_of_space_time hK hzero
    (fun t x ht => packingHamiltonian_eq_zero_of_time hA hs ht x)

theorem packingFlow_diffeomorphism {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (t : ℝ) :
    ∃ Φ : E n ≃ₜ E n, ⇑Φ=packingFlow n k C c s t ∧ ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      ∀ x v w,Problem.omega0 (fderiv ℝ Φ x v) (fderiv ℝ Φ x w)=Problem.omega0 v w :=
  compact_hamiltonian_flow (packing_main hA hs).smooth (packingHamiltonian_compact hA hs) t

theorem packingFlow_integral {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (x : E n) :
    packingFlow n k C c s 0 x = x ∧
    ∀ t, HasDerivAt (fun τ => packingFlow n k C c s τ x)
      (Problem.hamVF (packingHamiltonian n k C c s) t (packingFlow n k C c s t x)) t := by
  have hV := compact_hamiltonian_csField (packing_main hA hs).smooth (packingHamiltonian_compact hA hs)
  exact ⟨hV.flow_zero x, fun t => hV.flow_hasDerivAt x t⟩

theorem packingFlow_into {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (i : Fin k)
    (x : E n) (hx : x∈capBall (s i) (c i)) :
    packingFlow n k C c s 1 x∈capBallOpen 0 C := by
  have hP := packing_main hA hs
  have hV := compact_hamiltonian_csField hP.smooth (packingHamiltonian_compact hA hs)
  exact hP.maps_into i x hx (fun t => Return.flow (Problem.hamVF (packingHamiltonian n k C c s)) t x)
    (hV.flow_zero x) (fun t _ => (hV.flow_hasDerivAt x t).hasDerivWithinAt)

theorem packingFlow_disjoint {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (t : ℝ) :
    ∀ i j,i≠j → Disjoint (packingFlow n k C c s t '' capBall (s i) (c i))
      (packingFlow n k C c s t '' capBall (s j) (c j)) := by
  obtain ⟨Φ,he,_,_,_⟩ := packingFlow_diffeomorphism hA hs t
  rw [←he]
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,hxy⟩ := hz'
  have hyx : y=x := Φ.injective hxy
  subst y
  exact Set.disjoint_left.mp (hs i j hij) hx hy

end SymplecticPacking.General
