import SymplecticPacking.BranchSmall.Model

/-!
# Supporting lemmas for `vectorTransfer_spec` (paper thm:qdr-transfer (a))

The radial injection `ι_b(U) = W`, `W_j = √π U_j / √(b − |p|)` of the tube `{|p| < b}` into the
fibre of the weight-two bundle: explicit formula, the inverse moment formula
`p_j = b |W_j|² / (1 + |W|²)` (written with moments `π|W_j|²`), injectivity and smoothness on the
tube. These are the formula-level parts of supplement lem:vtr-injection.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff

variable {q : ℕ}

/-- Total moment `|p| = Σ_j π|U_j|²`. -/
def totalMoment (U : Fibre q) : ℝ := ∑ j, planeMoments U j

theorem planeMoments_smul (c : ℝ) (U : Fibre q) (j : Fin q) :
    planeMoments (fun i => c • U i) j = c ^ 2 * planeMoments U j := by
  simp only [planeMoments, radialArea, radiusSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem totalMoment_smul (c : ℝ) (U : Fibre q) :
    totalMoment (fun i => c • U i) = c ^ 2 * totalMoment U := by
  simp only [totalMoment, planeMoments_smul, Finset.mul_sum]

theorem totalMoment_nonneg (U : Fibre q) : 0 ≤ totalMoment U := by
  apply Finset.sum_nonneg
  intro j _
  simp only [planeMoments, radialArea, radiusSq]
  positivity

end SymplecticPacking.BranchSmall
