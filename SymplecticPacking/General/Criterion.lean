import SymplecticPacking.General.MainFlow
import SymplecticPacking.General.Rigidity

/-!
# Corollary D: the neighbourhood criterion

In dimension `2n ≥ 6` a symplectic embedding of an open neighbourhood of the closed source
balls into the open target exists iff the volume and two-ball inequalities hold
(`symplectic_neighbourhood_criterion`). Sufficiency is the time-one map of the explicit
Hamiltonian (`symplectic_neighbourhood_sufficient`); necessity is the rigidity of
`General/Rigidity.lean`.
-/

noncomputable section
namespace SymplecticPacking.General

open Set Problem
open scoped ContDiff

/-- One symplectic embedding of an open neighbourhood of all source balls. -/
def SymplecticNeighbourhoodPacking (n k : ℕ) (C : ℝ) (c : Fin k → ℝ)
    (s : Fin k → E n) : Prop :=
  ∃ (U : Set (E n)) (F : E n → E n), IsOpen U ∧
    ContDiffOn ℝ ∞ F U ∧ Topology.IsEmbedding (fun x : U => F x) ∧
    (∀ x ∈ U, IsSymplecticLinear (fderiv ℝ F x)) ∧
    (∀ i, capBall (s i) (c i) ⊆ U) ∧ MapsTo F U (capBallOpen 0 C)

/-- The construction supplies sufficiency in every admissible dimension, independently of
the rigidity argument used for the converse below. -/
theorem symplectic_neighbourhood_sufficient {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    {s : Fin k → E n} (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    SymplecticNeighbourhoodPacking n k C c s := by
  obtain ⟨Φ,hΦ,hsm,_,hω⟩ := packingFlow_diffeomorphism hA hs 1
  let U : Set (E n) := Φ ⁻¹' capBallOpen 0 C
  have hO : IsOpen (capBallOpen (0 : E n) C) := by
    rw [Ham.Isotopy.capBallOpen_zero_eq hA.C_pos.le]
    exact Metric.isOpen_ball
  refine ⟨U,Φ,hO.preimage Φ.continuous,hsm.contDiffOn,
    Φ.isEmbedding.comp Topology.IsEmbedding.subtypeVal,fun x _ => hω x,?_,?_⟩
  · intro i x hx
    change Φ x ∈ capBallOpen 0 C
    rw [hΦ]
    exact packingFlow_into hA hs i x hx
  · intro x hx
    exact hx

theorem symplectic_neighbourhood_criterion {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hs : BallsDisjoint n k c s) :
    SymplecticNeighbourhoodPacking n k C c s ↔
      (∑ i, c i ^ n) < C ^ n ∧ ∀ i j, i ≠ j → c i + c j < C := by
  constructor
  · rintro ⟨U,F,hU,hF,hemb,hω,hsrc,hinto⟩
    exact symplectic_embedding_necessary hn hk hC hc hs hU hF hemb hω hsrc
      (fun i x hx => hinto (hsrc i hx))
  · rintro ⟨hvol,hpair⟩
    exact symplectic_neighbourhood_sufficient
      ⟨by omega,hk,hC,hc,hvol,by intro h; omega,fun _ => hpair⟩ hs

end SymplecticPacking.General
