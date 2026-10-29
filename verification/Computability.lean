import SymplecticPacking.Effective.PackingCertificateAlgorithm
import verification.AxiomCheck
import SymplecticPacking.Explicit

/-!
# The algorithm

**Input.** Two streams of natural numbers: `capacities` names the target capacity `C` at
index `0` and the capacity `c_i` at index `i + 1` (`capacityFamily`; entries beyond `k` repeat
`C`), and `centres` names the coordinate `j` of the centre `s_i` at index
`pair (pair i p) j`. A name of a real `x` is a stream of rational codes `q` with
`|q p − x| ≤ 2⁻ᵖ` (`Effective.Names`); the runtime input of the machine is `pair n k`.

**Output.** A natural number `m`, decoded as an integer `B = (unpair m).1` and a straight-line
rational polynomial program `(unpair m).2`; the Hamiltonian it denotes is `β_B · P`
(`codeHamiltonian`), with `β_B` the product of flat-step box cutoffs. The decoding is given
below by definitional equalities.

**Theorem.** `original_name_algorithm`: one machine `rawProgramMachine capacities centres`,
recursive in the two input streams, halts on `pair n k` for every admissible input with
disjoint source balls, and the Hamiltonian `codeHamiltonian n m` of its output `m` satisfies
`PackingSpec n k C c s`. The machine passes `#check_constructive`: its computational closure
contains no classical constant, so it is one fixed program in the two oracle streams.
-/

open SymplecticPacking SymplecticPacking.Problem SymplecticPacking.Effective
open PackingSearch

/-! ## What the output code means -/

example (n m : ℕ) : codeHamiltonian n m =
    General.Compile.finiteHam n (Nat.unpair m).1
      (PackingPolynomial.toPolynomial (2 * n + 1)
        (PackingPolynomial.programExpression
          (PackingStateList.decodeList (Nat.unpair m).2))) := rfl

example (n B : ℕ) (P : MvPolynomial (Fin (2 * n + 1)) ℚ) (t : ℝ) (y : E n) :
    General.Compile.finiteHam n B P t y =
      General.Compile.boxCut n B y * General.Compile.evalPoly P t y :=
  rfl

example (n : ℕ) (B : ℝ) (y : E n) : General.Compile.boxCut n B y =
    ∏ l : Fin (2 * n),
      (1 - Real.smoothTransition ((y l ^ 2 - (B / 2) ^ 2) / ((3 * B / 4) ^ 2 - (B / 2) ^ 2))) :=
  rfl

/-- Rational inputs are names: the constant stream of a rational number names it. -/
example (q : ℚ) : Effective.Names (fun _ => q) (q : ℝ) := Effective.names_rational q

/-! ## The machine -/

/-- One machine takes `pair n k`, queries only the capacity and centre streams, halts on
admissible inputs, and returns a Hamiltonian packing code. -/
theorem original_name_algorithm {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (capacities centres : ℕ → ℕ) (hcap : Family.Names capacities (capacityFamily C c))
    (hcentre : ∀ i : Fin k, ∀ j : Fin (2 * n), Names
      (fun p => RationalCode.value (centres (Nat.pair (Nat.pair i.val p) j.val))) (s i j))
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    let input := OriginalNames.ofQueries capacities centres hcap hcentre
    let hv : ValidCapacities capacities := input.validCapacities hA
    let machine := rawProgramMachine capacities centres hv
    Nat.RecursiveIn (originalOracles capacities centres) machine ∧
    compiledCode input hA hs ∈ machine (Nat.pair n k) ∧
    PackingSpec n k C c s (codeHamiltonian n (compiledCode input hA hs)) := by
  let input := OriginalNames.ofQueries capacities centres hcap hcentre
  let hv : ValidCapacities capacities := input.validCapacities hA
  change Nat.RecursiveIn (originalOracles capacities centres)
      (rawProgramMachine capacities centres hv) ∧
    compiledCode input hA hs ∈ rawProgramMachine capacities centres hv (Nat.pair n k) ∧
    PackingSpec n k C c s (codeHamiltonian n (compiledCode input hA hs))
  refine ⟨?_, ?_, ?_⟩
  · exact rawProgramMachine_recursive (O := originalOracles capacities centres) hv
      (Oracle.query (q := capacities) (Set.mem_insert _ _))
      (Oracle.query (q := centres) (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · have hh := original_program_machine_halts input hA hs
    simpa only [rawProgramMachine, input, OriginalNames.ofQueries] using hh
  · have hp := compiledHamiltonian_spec input hA hs
    have he := congrArg (fun H : ℝ → E n → ℝ => PackingSpec n k C c s H)
      (compiledHamiltonian_eq_code input hA hs)
    exact he.mp hp

#assert_publication_axioms original_name_algorithm
#assert_publication_axioms stageFailure_recursive
#assert_publication_axioms stage_sound
#assert_publication_axioms actual_exists_stage
#check_explicit stageFailure
#check_explicit selectedStage
#check_explicit compiledCode
#check_explicit codeHamiltonian
-- Uniformity: the machine's computational closure contains no classical constant at all,
-- so it is one fixed program in the two oracle streams.
#check_constructive rawProgramMachine
