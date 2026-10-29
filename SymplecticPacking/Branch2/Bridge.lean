import SymplecticPacking.General.Interface
import SymplecticPacking.E4

/-!
# Bridges between `Problem` (phase space `ℝ^{2n}`) and the four-dimensional `E4`

For `n = 2`, `Problem.E 2 = EuclideanSpace ℝ (Fin (2 * 2))` is definitionally `E4`, and the two
symplectic forms agree (`omega0_two`).
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Problem General

/-! ### Bridges between `Problem` (dimension `2n`) and `E4` -/

/-- For `n = 2`, `Problem.omega0` is `SymplecticPacking.omega0`. -/
lemma omega0_two (x y : E 2) : Problem.omega0 x y = SymplecticPacking.omega0 x y := by
  simp only [Problem.omega0, SymplecticPacking.omega0, Fin.sum_univ_two, Problem.qIdx,
    Problem.pIdx]
  rw [add_sub_assoc]
  rfl

lemma isSymplecticLinear_two (A : E 2 →L[ℝ] E 2) (hA : SymplecticPacking.IsSymplecticLinear A) :
    General.IsSymplecticLinear A := fun x y => by
  rw [omega0_two, omega0_two]; exact hA x y

/-! ### Conjugation by one common dilation -/

open Set Metric
open scoped ContDiff Real

/-- `π‖μ⁻¹ u‖² = π‖u‖²/μ²`. -/
lemma pi_norm_inv_smul_sq {μ : ℝ} (hμ : 0 < μ) (u : E 2) :
    π * ‖(μ⁻¹ • u : E4)‖ ^ 2 = π * ‖u‖ ^ 2 / μ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hμ]
  field_simp

/-- **Rescaling.** Maps `g_i` of `ℝ⁴` that are smooth and symplectic on `{π‖X‖² < a_i/μ²}`,
injective with pairwise disjoint images on `{π‖X‖² ≤ c'_i/μ²}` and land in `{π‖·‖² < C/μ²}`
give, after conjugation by the dilation `u ↦ μ u`, embedding data satisfying `EmbeddingSpec`
with enlarged capacities `c'_i` and domain capacities `a_i`. -/
theorem scaled_spec {k : ℕ} {C μ : ℝ} {c : Fin k → ℝ} (hμ : 0 < μ) (g : Fin k → E4 → E4)
    (enl dom : Fin k → ℝ) (hlt : ∀ i, c i < enl i) (hle : ∀ i, enl i < dom i)
    (hsm : ∀ i, ∀ X : E4, π * ‖X‖ ^ 2 < dom i / μ ^ 2 → ContDiffAt ℝ ∞ (g i) X)
    (hsy : ∀ i, ∀ X : E4, π * ‖X‖ ^ 2 < dom i / μ ^ 2 →
      SymplecticPacking.IsSymplecticLinear (fderiv ℝ (g i) X))
    (hinj : ∀ i, InjOn (g i) {X : E4 | π * ‖X‖ ^ 2 ≤ enl i / μ ^ 2})
    (hdisj : ∀ i j, i ≠ j → Disjoint (g i '' {X : E4 | π * ‖X‖ ^ 2 ≤ enl i / μ ^ 2})
      (g j '' {X : E4 | π * ‖X‖ ^ 2 ≤ enl j / μ ^ 2}))
    (hinto : ∀ i, ∀ X : E4, π * ‖X‖ ^ 2 ≤ enl i / μ ^ 2 → π * ‖g i X‖ ^ 2 < C / μ ^ 2) :
    EmbeddingSpec 2 k C c ⟨fun i u => μ • g i (μ⁻¹ • u), enl, dom⟩ := by
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hcl : ∀ i, ∀ u ∈ capBall (0 : E 2) (enl i),
      π * ‖(μ⁻¹ • u : E4)‖ ^ 2 ≤ enl i / μ ^ 2 := by
    intro i u hu
    simp only [capBall, mem_ofPred_eq, sub_zero] at hu
    rw [pi_norm_inv_smul_sq hμ]
    exact div_le_div_of_nonneg_right hu hμ2.le
  have hop : ∀ i, ∀ u ∈ capBallOpen (0 : E 2) (dom i),
      π * ‖(μ⁻¹ • u : E4)‖ ^ 2 < dom i / μ ^ 2 := by
    intro i u hu
    simp only [capBallOpen, mem_ofPred_eq, sub_zero] at hu
    rw [pi_norm_inv_smul_sq hμ]
    exact div_lt_div_of_pos_right hu hμ2
  refine ⟨hlt, hle, ?_, ?_, ?_, ?_, ?_⟩
  · intro i u hu
    have hlin : ContDiff ℝ ∞ (fun u : E 2 => (μ⁻¹ • u : E4)) := contDiff_id.const_smul _
    exact (((hsm i _ (hop i u hu)).comp u hlin.contDiffAt).const_smul μ).contDiffWithinAt
  · intro i u hu
    have hv := hop i u hu
    have hdf : HasFDerivAt (g i) (fderiv ℝ (g i) (μ⁻¹ • u)) (μ⁻¹ • u) :=
      ((hsm i _ hv).differentiableAt (by simp)).hasFDerivAt
    have hcomp : HasFDerivAt (fun u : E 2 => μ • g i (μ⁻¹ • u))
        (fderiv ℝ (g i) (μ⁻¹ • u)) u := by
      have := (hdf.comp u ((hasFDerivAt_id (𝕜 := ℝ) u).const_smul μ⁻¹)).const_smul μ
      refine this.congr_fderiv ?_
      ext1 x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    show General.IsSymplecticLinear (fderiv ℝ (fun u : E 2 => μ • g i (μ⁻¹ • u)) u)
    rw [hcomp.fderiv]
    exact isSymplecticLinear_two _ (hsy i _ hv)
  · intro i u hu u' hu' huu
    have e1 : g i (μ⁻¹ • u) = g i (μ⁻¹ • u') := smul_right_injective _ hμ0 huu
    have e2 := (hinj i) (hcl i u hu) (hcl i u' hu') e1
    have := congrArg (fun v : E4 => μ • v) e2
    simpa [smul_smul, mul_inv_cancel₀ hμ0] using this
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', huu⟩
    have e1 : g j (μ⁻¹ • u') = g i (μ⁻¹ • u) := smul_right_injective _ hμ0 huu
    exact Set.disjoint_left.1 (hdisj i j hij) ⟨_, hcl i u hu, rfl⟩ ⟨_, hcl j u' hu', e1⟩
  · rintro i _ ⟨u, hu, rfl⟩
    have hin := hinto i _ (hcl i u hu)
    show π * ‖μ • g i (μ⁻¹ • u) - 0‖ ^ 2 < C
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, mul_pow]
    rw [lt_div_iff₀ hμ2] at hin
    linarith

end SymplecticPacking.Branch2
