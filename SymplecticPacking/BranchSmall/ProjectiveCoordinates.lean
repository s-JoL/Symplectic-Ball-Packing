import SymplecticPacking.BranchSmall.HomogeneousReturn
import SymplecticPacking.BranchSmall.ProjectiveGrowth

/-!
# Coordinates and uniform normal bounds for homogeneous Moser fields
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {m : ℕ}

section coordinates
variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem complex_phaseSq_norm_bounds (z : ι → ℂ) :
    ‖z‖ ^ 2 ≤ phaseSq (complexCartesian z) ∧
      phaseSq (complexCartesian z) ≤ (Fintype.card ι : ℝ) * ‖z‖ ^ 2 := by
  rw [complexCartesian_sq]
  constructor
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => ‖z i‖₊)
    have hn : ‖z‖ = ‖z i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun r : NNReal => (r : ℝ)) hi
    rw [hn, ← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  · calc
      (∑ i, Complex.normSq (z i)) ≤ ∑ _i : ι, ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
      _ = _ := by simp [nsmul_eq_mul]

end coordinates

def homogeneousSplit (m : ℕ) : HomogeneousInput m ≃L[ℝ] (ℂ × (Option (Fin m) → ℂ)) :=
  (LinearEquiv.piOptionEquivProd ℝ).toContinuousLinearEquiv

theorem homogeneousSplit_norm (z : HomogeneousInput m) : ‖homogeneousSplit m z‖ = ‖z‖ := by
  apply le_antisymm
  · change max ‖z none‖ ‖fun i => z (some i)‖ ≤ ‖z‖
    apply max_le (norm_le_pi_norm z none)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => norm_le_pi_norm z (some i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    change ‖z i‖ ≤ max ‖z none‖ ‖fun i => z (some i)‖
    cases i with
    | none => exact le_max_left _ _
    | some i => exact (norm_le_pi_norm (fun i => z (some i)) i).trans (le_max_right _ _)

theorem smooth_homogeneous_normal_bound {Y : ℝ → HomogeneousInput m → HomogeneousInput m}
    (hY : ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => Y p.1 p.2))
    (hzero : ∀ s z, z none = 0 → Y s z none = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : HomogeneousInput m,
      ‖z‖ ≤ 1 → ‖Y s z none‖ ≤ L * ‖z none‖ := by
  let A := homogeneousSplit m
  let Y' : ℝ → (ℂ × (Option (Fin m) → ℂ)) → (ℂ × (Option (Fin m) → ℂ)) :=
    fun s z => A (Y s (A.symm z))
  have hY' : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × (Option (Fin m) → ℂ)) => Y' p.1 p.2) :=
    A.contDiff.comp (hY.comp (contDiff_fst.prodMk (A.symm.contDiff.comp contDiff_snd)))
  obtain ⟨L, hL, hbound⟩ := smooth_normal_component_bound hY'
    (fun s _ z => hzero s (A.symm (0, z)) rfl) 1
  refine ⟨L, hL, ?_⟩
  intro s hs z hz
  have hb := hbound s hs (A z) ((homogeneousSplit_norm z).trans_le hz)
  have hAf (u : HomogeneousInput m) : (A u).1 = u none := rfl
  simpa only [Y', ContinuousLinearEquiv.symm_apply_apply, hAf] using hb


theorem complexAffineQuotient_fderiv_apply (z v : HomogeneousInput m) (hz : z none ≠ 0)
    (j : Option (Fin m)) :
    fderiv ℝ complexAffineQuotient z v j =
      v (some j) * (z none)⁻¹ - z (some j) * (z none)⁻¹ * v none * (z none)⁻¹ := by
  let P : Option (Option (Fin m)) → HomogeneousInput m →L[ℝ] ℂ :=
    fun i => ContinuousLinearMap.proj i
  have hn : HasFDerivAt (fun y : HomogeneousInput m => y (some j)) (P (some j)) z :=
    (P (some j)).hasFDerivAt
  have hd : HasFDerivAt (fun y : HomogeneousInput m => (y none)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (z none)⁻¹ (z none)⁻¹).comp (P none)) z :=
    (hasFDerivAt_inv' (𝕜 := ℝ) hz).comp z (P none).hasFDerivAt
  have hp := hn.fun_mul hd
  have hQ := ((complexAffineQuotient_smoothAt hz).differentiableAt (by simp)).hasFDerivAt
  let Qj : (Option (Fin m) → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj j
  have heval : HasFDerivAt (fun y : HomogeneousInput m => complexAffineQuotient y j)
      (Qj.comp (fderiv ℝ complexAffineQuotient z)) z := Qj.hasFDerivAt.comp z hQ
  have hp' : HasFDerivAt (fun y : HomogeneousInput m => complexAffineQuotient y j)
      (z (some j) • ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (z none)⁻¹ (z none)⁻¹).comp (P none)) +
        (z none)⁻¹ • P (some j)) z := by
    simpa only [complexAffineQuotient, div_eq_mul_inv] using hp
  have he := heval.unique hp'
  have hv := congrArg (fun L => L v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, smul_eq_mul, neg_apply, ContinuousLinearMap.mulLeftRight_apply, P, Qj] at hv
  rw [hv]
  ring

theorem complexAffineQuotient_fderiv_scaled (x : Affine m) {σ : ℝ} (hσ : 0 < σ)
    (v : HomogeneousInput m) (j : Option (Fin m)) :
    fderiv ℝ complexAffineQuotient (σ • complexAffineLift (affineComplex m x)) v j =
      (v (some j) - affineComplex m x j * v none) / (σ : ℂ) := by
  have hs : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  rw [complexAffineQuotient_fderiv_apply _ v (by
    simpa only [Pi.smul_apply, complexAffineLift_none, Complex.real_smul, mul_one] using hs)]
  simp only [Pi.smul_apply, complexAffineLift_none, complexAffineLift_some,
    Complex.real_smul, mul_one]
  field_simp


theorem affineComplex_norm (x : Affine m) : ‖affineComplex m x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
    intro i
    cases i with
    | none => exact norm_fst_le x
    | some i => exact (norm_le_pi_norm x.2 i).trans (norm_snd_le x)
  · change max ‖x.1‖ ‖x.2‖ ≤ ‖affineComplex m x‖
    apply max_le (norm_le_pi_norm (affineComplex m x) none)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (affineComplex m x) (some i)

theorem returnQuotient_fderiv_norm (z v : HomogeneousInput m) (hz : z none ≠ 0) :
    ‖fderiv ℝ (returnQuotient m) z v‖ = ‖fderiv ℝ complexAffineQuotient z v‖ := by
  have hQ := (returnQuotient_contDiffAt hz).differentiableAt (by simp)
  have hA := (affineComplexEquiv m).hasFDerivAt.comp z hQ.hasFDerivAt
  have he : (affineComplexEquiv m) ∘ returnQuotient m = complexAffineQuotient := by
    funext z
    exact (affineComplexEquiv m).apply_symm_apply _
  have hd := hA.fderiv
  rw [he] at hd
  have hv := congrArg (fun K => K v) hd
  change fderiv ℝ complexAffineQuotient z v = affineComplexEquiv m (fderiv ℝ (returnQuotient m) z v) at hv
  rw [hv, affineComplexEquiv_apply, affineComplex_norm]


end SymplecticPacking.BranchSmall.VT
