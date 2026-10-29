import SymplecticPacking.HighDim.Handle.RawFullProductMoserSpec

/-!
# Gram matrices and coordinate norms

Finite matrix and coordinate-norm facts shared by native cutoff constructions.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.RawGram
open Set Module
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def gram (b : Basis ι ℝ E) (β : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  (Matrix.of fun i j => β (b i) (b j)).det

def qn (b : Basis ι ℝ E) (x : E) : ℝ := ∑ i, (b.repr x i) ^ 2

theorem qn_eq (b : Basis ι ℝ E) (x : E) : qn b x = ∑ i, (b.equivFunL x i) ^ 2 := by
  simp [qn]

theorem qn_contDiff (b : Basis ι ℝ E) : ContDiff ℝ ∞ (qn b) := by
  have h : qn b = fun x => ∑ i, (b.equivFunL x i) ^ 2 := funext (qn_eq b)
  rw [h]
  refine ContDiff.sum fun i _ => ?_
  exact (((ContinuousLinearMap.proj i).comp
    b.equivFunL.toContinuousLinearMap).contDiff).pow 2

theorem isCompact_qn_le (b : Basis ι ℝ E) (M : ℝ) : IsCompact {x | qn b x ≤ M} := by
  have hs : {x | qn b x ≤ M} = b.equivFunL ⁻¹' {c : ι → ℝ | ∑ i, c i ^ 2 ≤ M} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, qn_eq]
  rw [hs]
  apply b.equivFunL.toHomeomorph.isCompact_preimage.mpr
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
      continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt M, fun c hc => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg M)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    calc c i ^ 2 ≤ ∑ j, c j ^ 2 :=
          Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)
      _ ≤ M := hc

theorem gram_apply_sum (b : Basis ι ℝ E) (β : E →L[ℝ] E →L[ℝ] ℝ) (c : ι → ℝ) (j : ι) :
    β (∑ i, c i • b i) (b j) = (Matrix.vecMul c (Matrix.of fun i j => β (b i) (b j))) j := by
  simp [Matrix.vecMul, dotProduct, map_sum, map_smul, ContinuousLinearMap.sum_apply]

theorem clm_eq_zero_of_basis (b : Basis ι ℝ E) {f : E →L[ℝ] ℝ} (h : ∀ j, f (b j) = 0) :
    f = 0 := by
  apply ContinuousLinearMap.coe_injective
  exact b.ext fun j => by simpa using h j

theorem gram_ne_zero_of_isInvertible (b : Basis ι ℝ E) {β : E →L[ℝ] E →L[ℝ] ℝ}
    (h : β.IsInvertible) : gram b β ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  have hv : β (∑ i, c i • b i) = 0 := by
    apply clm_eq_zero_of_basis b
    intro j
    rw [gram_apply_sum, hcM]
    rfl
  obtain ⟨e, he⟩ := h
  have h0' : (∑ i, c i • b i) = 0 := by
    apply e.injective
    rw [map_zero]
    rw [← he] at hv
    exact hv
  exact hc (funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent c h0' i)

theorem isInvertible_of_gram_ne_zero (b : Basis ι ℝ E) {β : E →L[ℝ] E →L[ℝ] ℝ}
    (h : gram b β ≠ 0) : β.IsInvertible := by
  have hI : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    apply h
    apply Matrix.exists_vecMul_eq_zero_iff.mp
    refine ⟨fun i => b.repr v i, ?_, ?_⟩
    · intro hz
      apply hne
      have : b.repr v = 0 := by
        ext i
        exact congrFun hz i
      simpa using this
    · funext j
      rw [← gram_apply_sum]
      simp [b.sum_repr v, hv]
  have hS : Function.Surjective β :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := E)).symm).mp hI
  exact ⟨(LinearEquiv.ofBijective β.toLinearMap ⟨hI, hS⟩).toContinuousLinearEquiv, rfl⟩

end SymplecticPacking.HighDim.ToricPackingStages.RawGram
