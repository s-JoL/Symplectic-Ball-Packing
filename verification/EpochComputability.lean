import SymplecticPacking.Effective.PackingCertificateEpochAlgorithm
import verification.AxiomCheck
import SymplecticPacking.Explicit

/-!
# The algorithm for the Epoch data

**Input.** One stream of natural numbers `epsilon` naming `ε ∈ (0, 1)` (`CodeName.Names`:
rational codes within `2⁻ᵖ` of `ε`); the runtime input of the machine is `k`.

**Output.** A natural number decoded as in `verification/Computability.lean`: an integer `B`
and a rational polynomial `P`, denoting the Hamiltonian `β_B · P`
(`PackingSearch.codeHamiltonian 2`).

**Theorems.** `epoch_name_algorithm`: one machine `PackingEpoch.machine epsilon`, recursive in
the stream `epsilon`, halts on every `k ≥ 9`, and its output satisfies `EpochSpecR k ε R` with
`R = epochRadius k ε` (closed unit balls at `epochCenter i`, closed target ball,
`k / R⁴ > 1 - ε`). `epoch_name_algorithm_packing`: the same output in the form of Definition
1.1, with `k / R⁴ = 1 - ε/2`. The machine passes `#check_constructive`.
-/

open SymplecticPacking SymplecticPacking.Problem SymplecticPacking.Effective
open PackingEpoch

/-- The single machine reads only the stream `epsilon`. For every runtime `k ≥ 9` it halts
with a finite rational Hamiltonian meeting Epoch's closed-unit-ball, closed-target-ball and
strict density requirements. -/
theorem epoch_name_algorithm {ε : ℝ} (epsilon : ℕ → ℕ)
    (he : CodeName.Names epsilon ε) (h0 : 0 < ε) (h1 : ε < 1) :
    Nat.RecursiveIn (PackingEpoch.originalOracles epsilon)
      (machine epsilon (validEpsilon_of_names epsilon he h1)) ∧
    ∀ (k : ℕ) (hk : 9 ≤ k),
      compiledCode epsilon he hk h0 h1 ∈ machine epsilon (validEpsilon_of_names epsilon he h1) k ∧
      Problem.EpochSpecR k ε (General.epochRadius k ε)
        (PackingSearch.codeHamiltonian 2 (compiledCode epsilon he hk h0 h1)) := by
  refine ⟨machine_recursive epsilon (validEpsilon_of_names epsilon he h1), ?_⟩
  intro k hk
  exact ⟨machine_halts (k := k) epsilon he hk h0 h1,
    compiled_epoch_spec (k := k) epsilon he hk h0 h1⟩

/-- The same output in the form of Definition 1.1: `β_B · P` satisfies the packing
specification for `C = π R²`, capacities `π` and centres `epochCenter i = (3i, 0, 0, 0)`,
`0 ≤ i < k` (open target), and `k / R⁴ = 1 - ε/2`. -/
theorem epoch_name_algorithm_packing {ε : ℝ} (epsilon : ℕ → ℕ)
    (he : CodeName.Names epsilon ε) (h0 : 0 < ε) (h1 : ε < 1) (k : ℕ) (hk : 9 ≤ k) :
    compiledCode epsilon he hk h0 h1 ∈ machine epsilon (validEpsilon_of_names epsilon he h1) k ∧
      PackingSpec 2 k (Real.pi * General.epochRadius k ε ^ 2) (fun _ => Real.pi)
        (fun i => epochCenter i)
        (PackingSearch.codeHamiltonian 2 (compiledCode epsilon he hk h0 h1)) ∧
      (k : ℝ) / General.epochRadius k ε ^ 4 = 1 - ε / 2 := by
  refine ⟨machine_halts (k := k) epsilon he hk h0 h1,
    compiled_packing_spec epsilon he hk h0 h1, ?_⟩
  rw [General.epochRadius_pow_four hk h0 h1]
  exact (General.epochR4_bounds hk h0 h1).2

#assert_publication_axioms epoch_name_algorithm
#assert_publication_axioms epoch_name_algorithm_packing
#assert_publication_axioms PackingEpoch.machine_recursive
#assert_publication_axioms PackingEpoch.machine_halts
#assert_publication_axioms PackingEpoch.compiled_epoch_spec
#check_explicit PackingEpoch.machine
#check_constructive PackingEpoch.machine
#check_explicit PackingEpoch.compiledCode
#check_explicit PackingEpoch.radiusCode
