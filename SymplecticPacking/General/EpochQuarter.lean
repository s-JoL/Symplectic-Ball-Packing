import SymplecticPacking.General.Main

/-!
# The four-dimensional theorem: the Epoch data at density `1 - ε/4`

The Epoch Hamiltonian run at `ε/2`: target radius `R = (k / (1 - ε/4))^{1/4}`, so that
`k / R⁴ = 1 - ε/4 > 1 - ε`. For `k ≥ 10` the normalised capacity satisfies
`(c/C)√k = √(1 - ε/4) ∈ (3/4, 1)` for every `ε ∈ (0, 1)`, so the construction takes the
linear comparison datum of the equal case (`Branch2.EqualCase`).
-/

noncomputable section

namespace SymplecticPacking.General

open Problem

/-- `R = (k / (1 - ε/4))^{1/4}`, the Epoch radius at `ε/2`. -/
def epochRadiusQ (k : ℕ) (ε : ℝ) : ℝ := epochRadius k (ε / 2)

/-- The Epoch Hamiltonian at `ε/2`: `packingHamiltonian 2 k (π R²) (π, …, π) ((3i, 0, 0, 0))_i`
with `R = epochRadiusQ k ε`. -/
def epochHamiltonianQ (k : ℕ) (ε : ℝ) : ℝ → E 2 → ℝ := epochHamiltonian k (ε / 2)

/-- `k / R⁴ = 1 - ε/4`. -/
theorem epochQ_density {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (k : ℝ) / epochRadiusQ k ε ^ 4 = 1 - ε / 4 := by
  rw [epochRadiusQ, epochRadius_pow_four hk (by linarith) (by linarith),
    (epochR4_bounds hk (by linarith : 0 < ε / 2) (by linarith)).2]
  ring

/-- The packing specification with the open target `B°(π R²)` and `k / R⁴ = 1 - ε/4`. -/
theorem epochQ_packing {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Problem.PackingSpec 2 k (Real.pi * epochRadiusQ k ε ^ 2) (fun _ => Real.pi)
        (fun i => epochCenter i) (epochHamiltonianQ k ε) ∧
      (k : ℝ) / epochRadiusQ k ε ^ 4 = 1 - ε / 4 :=
  ⟨packing_main (epoch_admissible (ε := ε / 2) hk (by linarith) (by linarith)) (epoch_disjoint k),
    epochQ_density hk h0 h1⟩

/-- The Epoch specification (closed unit balls into the closed ball `B(R)`, `k / R⁴ > 1 - ε`). -/
theorem epochQ_spec {k : ℕ} (hk : 9 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Problem.EpochSpecR k ε (epochRadiusQ k ε) (epochHamiltonianQ k ε) := by
  have h := epoch_general k hk (ε / 2) (by linarith) (by linarith)
  have hd := epochQ_density hk h0 h1
  refine ⟨h.smooth, h.compactSupport, h.radius_pos, ?_, h.exists_curve, h.maps_into⟩
  change 1 - ε < (k : ℝ) / epochRadiusQ k ε ^ 4
  rw [hd]; linarith

/-- For `k ≥ 10` and every `ε ∈ (0, 1)` the data are in the equal case, so the four-dimensional
branch uses the linear comparison datum (`Branch2.embeddingsEq`). -/
theorem epochQ_equalCase {k : ℕ} (hk : 10 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Branch2.EqualCase k (Real.pi * epochRadiusQ k ε ^ 2) (fun _ => Real.pi) := by
  have hk9 : 9 ≤ k := by omega
  have hR : 0 < epochRadiusQ k ε := epochRadius_pos (ε := ε / 2) hk9 (by linarith) (by linarith)
  have hd := epochQ_density hk9 h0 h1
  have hpi := Real.pi_pos
  have hk10 : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set R := epochRadiusQ k ε
  set x := Real.pi / (Real.pi * R ^ 2) * Real.sqrt k with hx
  have hx' : x = Real.sqrt k / R ^ 2 := by rw [hx]; field_simp
  have hxpos : 0 < x := by rw [hx']; positivity
  have hsq : x ^ 2 = 1 - ε / 4 := by
    rw [hx', div_pow, Real.sq_sqrt hkpos.le, ← hd]; ring
  refine ⟨hk, fun _ _ => rfl, fun _ => ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith

end SymplecticPacking.General
