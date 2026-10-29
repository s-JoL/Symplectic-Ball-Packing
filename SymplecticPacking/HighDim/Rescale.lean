import SymplecticPacking.General.Interface

/-!
# Normalisation of the target capacity

Each branch works with normalised target capacity `1` and capacities `ρ_i = c_i / C`.
`scaleData C D` conjugates the normalised maps by the dilation `u ↦ √C u`; conjugation by a
dilation preserves symplecticity (the factors `√C` and `1/√C` cancel in `ω₀`).
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Problem General
open scoped ContDiff

theorem omega0_smul_left {n : ℕ} (r : ℝ) (x y : E n) :
    Problem.omega0 (r • x) y = r * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem omega0_smul_right {n : ℕ} (r : ℝ) (x y : E n) :
    Problem.omega0 x (r • y) = r * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Conjugation of the normalised embeddings by the dilation `u ↦ √C u`. -/
def scaleData {n k : ℕ} (C : ℝ) (D : EmbeddingData n k) : EmbeddingData n k where
  f i u := Real.sqrt C • D.f i ((Real.sqrt C)⁻¹ • u)
  enlarged i := C * D.enlarged i
  domain i := C * D.domain i

theorem capBall_smul_iff {n : ℕ} {C a : ℝ} (hC : 0 < C) {u : E n} :
    (Real.sqrt C)⁻¹ • u ∈ capBall 0 a ↔ u ∈ capBall 0 (C * a) := by
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  simp only [capBall, mem_setOf_eq, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hs, mul_pow, inv_pow, Real.sq_sqrt hC.le]
  rw [show Real.pi * (C⁻¹ * ‖u‖ ^ 2) = (Real.pi * ‖u‖ ^ 2) / C by field_simp,
    div_le_iff₀ hC, mul_comm a]

theorem capBallOpen_smul_iff {n : ℕ} {C a : ℝ} (hC : 0 < C) {u : E n} :
    (Real.sqrt C)⁻¹ • u ∈ capBallOpen 0 a ↔ u ∈ capBallOpen 0 (C * a) := by
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  simp only [capBallOpen, mem_setOf_eq, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hs, mul_pow, inv_pow, Real.sq_sqrt hC.le]
  rw [show Real.pi * (C⁻¹ * ‖u‖ ^ 2) = (Real.pi * ‖u‖ ^ 2) / C by field_simp,
    div_lt_iff₀ hC, mul_comm a]

theorem scaleData_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {D : EmbeddingData n k}
    (hC : 0 < C) (h : EmbeddingSpec n k 1 (fun i => c i / C) D) :
    EmbeddingSpec n k C c (scaleData C D) := by
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hs0 : Real.sqrt C ≠ 0 := hs.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := h.lt_enlarged i
    simp only [scaleData]
    rw [div_lt_iff₀ hC] at this
    linarith
  · intro i
    exact mul_lt_mul_of_pos_left (h.enlarged_lt_domain i) hC
  · intro i
    have hmaps : MapsTo (fun u : E n => (Real.sqrt C)⁻¹ • u)
        (capBallOpen 0 (C * D.domain i)) (capBallOpen 0 (D.domain i)) :=
      fun u hu => (capBallOpen_smul_iff hC).mpr hu
    exact (contDiff_const_smul _).comp_contDiffOn
      ((h.smooth i).comp (contDiff_const_smul _).contDiffOn hmaps)
  · intro i u hu x y
    have hu' : (Real.sqrt C)⁻¹ • u ∈ capBallOpen 0 (D.domain i) :=
      (capBallOpen_smul_iff hC).mpr hu
    have hopen : IsOpen (capBallOpen (0 : E n) (D.domain i)) :=
      isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
        continuous_const
    have hdf : DifferentiableAt ℝ (D.f i) ((Real.sqrt C)⁻¹ • u) :=
      ((h.smooth i).contDiffAt (hopen.mem_nhds hu')).differentiableAt (by simp)
    have hd : HasFDerivAt (fun u => Real.sqrt C • D.f i ((Real.sqrt C)⁻¹ • u))
        (Real.sqrt C • ((fderiv ℝ (D.f i) ((Real.sqrt C)⁻¹ • u)).comp
          ((Real.sqrt C)⁻¹ • ContinuousLinearMap.id ℝ (E n)))) u := by
      have h1 : HasFDerivAt (fun u : E n => (Real.sqrt C)⁻¹ • u)
          ((Real.sqrt C)⁻¹ • ContinuousLinearMap.id ℝ (E n)) u :=
        ((Real.sqrt C)⁻¹ • ContinuousLinearMap.id ℝ (E n)).hasFDerivAt
      exact (hdf.hasFDerivAt.comp u h1).const_smul (Real.sqrt C)
    change Problem.omega0 (fderiv ℝ (fun u => Real.sqrt C • D.f i ((Real.sqrt C)⁻¹ • u)) u x)
      (fderiv ℝ (fun u => Real.sqrt C • D.f i ((Real.sqrt C)⁻¹ • u)) u y) = Problem.omega0 x y
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.id_apply, map_smul]
    rw [omega0_smul_left, omega0_smul_right, omega0_smul_left, omega0_smul_right]
    have hsym := h.sympl i _ hu' x y
    rw [hsym]
    field_simp
  · intro i x hx y hy hxy
    have hxy' : D.f i ((Real.sqrt C)⁻¹ • x) = D.f i ((Real.sqrt C)⁻¹ • y) :=
      smul_right_injective _ hs0 hxy
    have := h.inj i ((capBall_smul_iff hC).mpr hx) ((capBall_smul_iff hC).mpr hy) hxy'
    exact smul_right_injective _ (inv_ne_zero hs0) this
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxy' : D.f j ((Real.sqrt C)⁻¹ • y) = D.f i ((Real.sqrt C)⁻¹ • x) :=
      smul_right_injective _ hs0 hxy
    exact Set.disjoint_left.mp (h.disj i j hij) ⟨_, (capBall_smul_iff hC).mpr hx, rfl⟩
      ⟨_, (capBall_smul_iff hC).mpr hy, hxy'⟩
  · rintro i _ ⟨x, hx, rfl⟩
    have hv := h.into i ⟨_, (capBall_smul_iff hC).mpr hx, rfl⟩
    have : (Real.sqrt C)⁻¹ • (Real.sqrt C • D.f i ((Real.sqrt C)⁻¹ • x)) ∈ capBallOpen 0 1 := by
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := (capBallOpen_smul_iff hC).mp this
    rw [mul_one] at h2
    exact h2

end SymplecticPacking.HighDim
