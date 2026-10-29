import SymplecticPacking.General.Main
import SymplecticPacking.General.EpochQuarter
import SymplecticPacking.General.CompileOutput

/-!
# The construction, top level

`packingHamiltonian n k C c s` (`SymplecticPacking/General/Main.lean`) is

  `HamEnd.hamiltonianOfEmbeddings n k c s (selectEmbeddings n k C c)`

1. **Branch selection** (`selectEmbeddings`): by the dimension and by whether some ball has
   capacity at least `C/2`:
   * `n = 2`                     → `Branch2.embeddings`        (Fermat cubic normal model);
   * `n ≥ 3`, all `2c_i < C`     → `BranchSmall.embeddings`    (complete-intersection curves);
   * `n = 3`, some `2c_j ≥ C`    → `BranchLarge3.embeddings`   (`Bl_o CP³`, quadric divisor);
   * `n ≥ 4`, some `2c_j ≥ C`    → `BranchLargeHigh.embeddings` (quadric curve, slit shell).
   Each produces `EmbeddingData n k`: explicit maps `f_i`, enlarged source capacities `c'_i > c_i`
   and domain capacities `a_i > c'_i` (`SymplecticPacking/General/Interface.lean`).
2. **Hamiltonian end** (`HamEnd.hamiltonianOfEmbeddings`): common isotopy from the translations
   `u ↦ s_i + u` to the `f_i`, radial primitive, cut-off; one Hamiltonian on `ℝ × ℝ^{2n}`.

The Epoch Hamiltonian is the instance
`epochHamiltonian k ε = packingHamiltonian 2 k (π R²) (π, …, π) ((3i, 0, 0, 0))_i` with
`R⁴ = k / (1 - ε/2)` (so `k / R⁴ = 1 - ε/2`).
-/

open SymplecticPacking SymplecticPacking.General

example (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → Problem.E n) :
    packingHamiltonian n k C c s =
      HamEnd.hamiltonianOfEmbeddings n k c s (selectEmbeddings n k C c) := rfl

example (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) :
    selectEmbeddings n k C c =
      open Classical in
      if n = 2 then Branch2.embeddings n k C c
      else if ∃ j, C ≤ 2 * c j then
        (if n = 3 then BranchLarge3.embeddings n k C c else BranchLargeHigh.embeddings n k C c)
      else BranchSmall.embeddings n k C c := rfl

example (k : ℕ) (ε : ℝ) :
    epochHamiltonian k ε =
      packingHamiltonian 2 k (Real.pi * epochRadius k ε ^ 2) (fun _ => Real.pi)
        (fun i => Problem.epochCenter i) := rfl

example (k : ℕ) (ε : ℝ) : epochRadius k ε = ((k : ℝ) / (1 - ε / 2)) ^ (1 / 4 : ℝ) := rfl

/-- The Hamiltonian `H_{k,ε}` of Theorem A: the Epoch instance at `ε/2`. -/
example (k : ℕ) (ε : ℝ) :
    epochHamiltonianQ k ε =
      packingHamiltonian 2 k (Real.pi * epochRadiusQ k ε ^ 2) (fun _ => Real.pi)
        (fun i => Problem.epochCenter i) := rfl

example (k : ℕ) (ε : ℝ) : epochRadiusQ k ε = ((k : ℝ) / (1 - ε / 4)) ^ (1 / 4 : ℝ) := by
  norm_num [epochRadiusQ, epochRadius, epochR4, div_div]

#print packingHamiltonian
#print selectEmbeddings
#print epochHamiltonian
#print epochRadius

-- The finite result consists of the integer B and the rational polynomial P supplied by
-- a datum satisfying (C1)–(C7). The original-name finite search and its decoded output
-- are given separately in verification/Computability.lean.
#print SymplecticPacking.General.Compile.compileOutput
#check SymplecticPacking.General.Compile.main_finite
