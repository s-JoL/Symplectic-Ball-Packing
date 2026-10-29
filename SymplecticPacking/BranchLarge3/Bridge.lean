import SymplecticPacking.General.Interface
import OAI.Geometry.BallPacking.Models.BallVolume

/-!
# Bridge: OpenAI ball embeddings (target capacity 1) → `EmbeddingSpec` (target capacity C)

Dimension-free. `phaseEquiv n : ℝ^{2n} ≃L[ℝ] ℂⁿ` is `z_j = q_j + i p_j` (`General.toPhase`);
it carries `ω₀` to the OpenAI `standardForm` and `π‖y‖²` to the OpenAI `capacity`.

For a map `F : ℂⁿ → ℂⁿ` of the OpenAI library and `C > 0`, the conjugate
`conjMap C F y = √C · Φ⁻¹ (F (Φ (y / √C)))` is symplectic wherever `F` is, and maps
`capBall 0 (C r)` onto the image of `closedBall n r`. `embeddingSpec_of_ballMaps` turns explicit
OpenAI ball embeddings of radii `rad_i` into the open unit-capacity ball, with pairwise disjoint
images, into `EmbeddingSpec` with enlarged capacities `C enl_i` and domains `C rad_i`.

(Generic in `n`; usable by every branch that ends in the OpenAI normalisation.)
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open Problem General Set
open OAI.PackingSufficiencySupport (Ambient capacity closedBall openBall standardForm
  IsBallEmbedding)
open scoped ContDiff

variable {n : ℕ}

/-- Inverse of `toPhase`: `(q, p) = (Re z, Im z)`. -/
def ofPhase (z : Fin n → ℂ) : E n :=
  WithLp.toLp 2 fun i : Fin (2 * n) =>
    if h : (i : ℕ) < n then (z ⟨i, h⟩).re
    else (z ⟨i - n, by have := i.isLt; omega⟩).im

@[simp] lemma toPhase_re (y : E n) (j : Fin n) : (toPhase y j).re = y (qIdx j) := rfl
@[simp] lemma toPhase_im (y : E n) (j : Fin n) : (toPhase y j).im = y (pIdx j) := rfl

lemma toPhase_ofPhase (z : Fin n → ℂ) : toPhase (ofPhase z) = z := by
  funext j
  apply Complex.ext
  · simp [toPhase, ofPhase, qIdx]
  · simp [toPhase, ofPhase, pIdx]

lemma ofPhase_toPhase (y : E n) : ofPhase (toPhase y) = y := by
  refine PiLp.ext fun i => ?_
  by_cases h : (i : ℕ) < n
  · simp [toPhase, ofPhase, qIdx, h]
  · simp [toPhase, ofPhase, pIdx, h]
    have e : (⟨n + (i - n), by omega⟩ : Fin (2 * n)) = i := Fin.ext (by simp; omega)
    rw [e]

/-- `toPhase` as a linear equivalence. -/
def phaseEquivₗ (n : ℕ) : E n ≃ₗ[ℝ] (Fin n → ℂ) where
  toFun := toPhase
  invFun := ofPhase
  map_add' x y := by
    funext j; apply Complex.ext <;> simp [toPhase]
  map_smul' r x := by
    funext j; apply Complex.ext <;> simp [toPhase]
  left_inv := ofPhase_toPhase
  right_inv := toPhase_ofPhase

/-- `toPhase` as a continuous linear equivalence. -/
def phaseEquiv (n : ℕ) : E n ≃L[ℝ] (Fin n → ℂ) := (phaseEquivₗ n).toContinuousLinearEquiv

@[simp] lemma phaseEquiv_apply (y : E n) : phaseEquiv n y = toPhase y := rfl
@[simp] lemma phaseEquiv_symm_apply (z : Fin n → ℂ) : (phaseEquiv n).symm z = ofPhase z := rfl

/-- The coordinates `q` and `p` together enumerate `Fin (2n)`. -/
def qpEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

lemma qpEquiv_inl (j : Fin n) : qpEquiv n (Sum.inl j) = qIdx j := by
  ext; simp [qpEquiv, qIdx]

lemma qpEquiv_inr (j : Fin n) : qpEquiv n (Sum.inr j) = pIdx j := by
  ext; simp [qpEquiv, pIdx, add_comm]

lemma sum_fin_two_mul {M : Type*} [AddCommMonoid M] (f : Fin (2 * n) → M) :
    ∑ i, f i = ∑ j : Fin n, (f (qIdx j) + f (pIdx j)) := by
  rw [← (qpEquiv n).sum_comp, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [qpEquiv_inl, qpEquiv_inr]

lemma norm_sq_eq (y : E n) :
    ‖y‖ ^ 2 = ∑ j : Fin n, Complex.normSq (toPhase y j) := by
  rw [EuclideanSpace.norm_sq_eq, sum_fin_two_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Real.norm_eq_abs, sq_abs, Complex.normSq_apply, toPhase_re, toPhase_im]
  ring

lemma capacity_toPhase (y : E n) : capacity (toPhase y) = Real.pi * ‖y‖ ^ 2 := by
  rw [capacity, norm_sq_eq]

lemma standardForm_toPhase (u v : E n) :
    standardForm (toPhase u) (toPhase v) = Problem.omega0 u v := by
  simp [standardForm, Problem.omega0]

lemma omega0_smul (a b : ℝ) (u v : E n) :
    Problem.omega0 (a • u) (b • v) = a * b * Problem.omega0 u v := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The conjugated map -/

/-- `conjMap C F y = √C · Φ⁻¹ (F (Φ (y / √C)))`. -/
def conjMap (C : ℝ) (F : Ambient n → Ambient n) (y : E n) : E n :=
  Real.sqrt C • ofPhase (F (toPhase ((Real.sqrt C)⁻¹ • y)))

/-- The source rescaling `y ↦ Φ (y / √C)`. -/
def inMap (C : ℝ) : E n →L[ℝ] Ambient n :=
  (phaseEquiv n : E n →L[ℝ] (Fin n → ℂ)).comp ((Real.sqrt C)⁻¹ • ContinuousLinearMap.id ℝ (E n))

/-- The target rescaling `z ↦ √C Φ⁻¹ z`. -/
def outMap (C : ℝ) : Ambient n →L[ℝ] E n :=
  Real.sqrt C • ((phaseEquiv n).symm : (Fin n → ℂ) →L[ℝ] E n)

lemma inMap_apply (C : ℝ) (y : E n) : inMap C y = toPhase ((Real.sqrt C)⁻¹ • y) := by
  simp only [inMap, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq]
  rfl

lemma outMap_apply (C : ℝ) (z : Ambient n) : outMap C z = Real.sqrt C • ofPhase z := by
  simp [outMap]

lemma conjMap_eq (C : ℝ) (F : Ambient n → Ambient n) :
    conjMap C F = outMap C ∘ F ∘ inMap C := by
  funext y; simp [conjMap, inMap_apply, outMap_apply]

lemma capacity_inMap {C : ℝ} (hC : 0 < C) (y : E n) :
    capacity (inMap C y) = Real.pi * ‖y‖ ^ 2 / C := by
  rw [inMap_apply, capacity_toPhase, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hC), inv_pow, Real.sq_sqrt hC.le]
  field_simp

lemma mem_closedBall_inMap {C : ℝ} (hC : 0 < C) {r : ℝ} {y : E n} :
    inMap C y ∈ closedBall n r ↔ y ∈ capBall 0 (C * r) := by
  simp only [closedBall, capBall, mem_setOf_eq, sub_zero, capacity_inMap hC]
  rw [div_le_iff₀ hC, mul_comm r C]

lemma mem_openBall_inMap {C : ℝ} (hC : 0 < C) {r : ℝ} {y : E n} :
    inMap C y ∈ openBall n r ↔ y ∈ capBallOpen 0 (C * r) := by
  simp only [openBall, capBallOpen, mem_setOf_eq, sub_zero, capacity_inMap hC]
  rw [div_lt_iff₀ hC, mul_comm r C]

lemma capacity_outMap {C : ℝ} (hC : 0 < C) (z : Ambient n) :
    Real.pi * ‖outMap C z‖ ^ 2 = C * capacity z := by
  rw [outMap_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hC.le]
  have := capacity_toPhase (ofPhase z)
  rw [toPhase_ofPhase] at this
  rw [this]; ring

lemma inMap_injective {C : ℝ} (hC : 0 < C) : Function.Injective (inMap (n := n) C) := by
  intro x y h
  rw [inMap_apply, inMap_apply] at h
  have h2 := congrArg ofPhase h
  rw [ofPhase_toPhase, ofPhase_toPhase] at h2
  have hs : (Real.sqrt C)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hC).ne'
  exact smul_right_injective _ hs h2

lemma outMap_injective {C : ℝ} (hC : 0 < C) : Function.Injective (outMap (n := n) C) := by
  intro x y h
  rw [outMap_apply, outMap_apply] at h
  have hs : Real.sqrt C ≠ 0 := (Real.sqrt_pos.2 hC).ne'
  have h2 := smul_right_injective _ hs h
  have h3 := congrArg toPhase h2
  simpa [toPhase_ofPhase] using h3

lemma omega0_outMap {C : ℝ} (hC : 0 < C) (z w : Ambient n) :
    Problem.omega0 (outMap C z) (outMap C w) = C * standardForm z w := by
  rw [outMap_apply, outMap_apply, omega0_smul, ← standardForm_toPhase, toPhase_ofPhase,
    toPhase_ofPhase, Real.mul_self_sqrt hC.le]

lemma standardForm_inMap {C : ℝ} (hC : 0 < C) (u v : E n) :
    standardForm (inMap C u) (inMap C v) = Problem.omega0 u v / C := by
  rw [inMap_apply, inMap_apply, standardForm_toPhase, omega0_smul, ← mul_inv,
    Real.mul_self_sqrt hC.le]
  field_simp

/-! ### From OpenAI ball embeddings to `EmbeddingSpec` -/

lemma closedBall_of_openBall {r : ℝ} {z : Ambient n} (h : z ∈ openBall n r) :
    z ∈ closedBall n r := by
  simp only [openBall, closedBall, mem_setOf_eq] at h ⊢; exact h.le

lemma closedBall_mono {r r' : ℝ} (hr : r ≤ r') : closedBall n r ⊆ closedBall n r' := by
  intro z hz
  simp only [closedBall, mem_setOf_eq] at hz ⊢; linarith

/-- The interface data built from OpenAI ball maps. -/
def dataOfBallMaps {k : ℕ} (C : ℝ) (F : Fin k → Ambient n → Ambient n)
    (enl rad : Fin k → ℝ) : EmbeddingData n k where
  f i := conjMap C (F i)
  enlarged i := C * enl i
  domain i := C * rad i

theorem embeddingSpec_of_ballMaps {k : ℕ} {C : ℝ} (hC : 0 < C) {c : Fin k → ℝ}
    (F : Fin k → Ambient n → Ambient n) (enl rad : Fin k → ℝ)
    (hF : ∀ i, IsBallEmbedding (rad i) (F i))
    (hinto : ∀ i, F i '' closedBall n (rad i) ⊆ openBall n 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i '' closedBall n (rad i)) (F j '' closedBall n (rad j)))
    (hlt : ∀ i, c i < C * enl i) (henl : ∀ i, enl i < rad i) :
    EmbeddingSpec n k C c (dataOfBallMaps C F enl rad) := by
  have hsub : ∀ i, closedBall n (enl i) ⊆ closedBall n (rad i) := fun i =>
    closedBall_mono (henl i).le
  refine ⟨hlt, fun i => mul_lt_mul_of_pos_left (henl i) hC, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro i
    obtain ⟨U, hU, hBU, hs, -, -⟩ := hF i
    show ContDiffOn ℝ ∞ (conjMap C (F i)) _
    rw [conjMap_eq]
    refine (outMap C).contDiff.comp_contDiffOn (hs.comp (inMap C).contDiff.contDiffOn ?_)
    intro y hy
    apply hBU
    exact closedBall_of_openBall ((mem_openBall_inMap hC).2 hy)
  · -- symplectic
    intro i u hu
    obtain ⟨U, hU, hBU, hs, -, hω⟩ := hF i
    have hxU : inMap C u ∈ U := hBU (closedBall_of_openBall ((mem_openBall_inMap hC).2 hu))
    have hdF : DifferentiableAt ℝ (F i) (inMap C u) :=
      (hs.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hfd : fderiv ℝ (conjMap C (F i)) u =
        (outMap C).comp ((fderiv ℝ (F i) (inMap C u)).comp (inMap C)) := by
      rw [conjMap_eq]
      have h1 : HasFDerivAt (F i ∘ inMap C) ((fderiv ℝ (F i) (inMap C u)).comp (inMap C)) u :=
        hdF.hasFDerivAt.comp u (inMap C).hasFDerivAt
      exact ((outMap C).hasFDerivAt.comp u h1).fderiv
    intro x y
    show Problem.omega0 (fderiv ℝ (conjMap C (F i)) u x) (fderiv ℝ (conjMap C (F i)) u y) =
      Problem.omega0 x y
    rw [hfd]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [omega0_outMap hC, hω _ hxU, standardForm_inMap hC]
    field_simp
  · -- injectivity
    intro i y₁ hy₁ y₂ hy₂ h
    obtain ⟨U, hU, hBU, hs, he, hω⟩ := hF i
    have hinjU : InjOn (F i) U := fun a ha b hb hab => by
      have := he.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
      simpa using this
    have hx₁ : inMap C y₁ ∈ U := hBU (hsub i ((mem_closedBall_inMap hC).2 hy₁))
    have hx₂ : inMap C y₂ ∈ U := hBU (hsub i ((mem_closedBall_inMap hC).2 hy₂))
    have h' : outMap C (F i (inMap C y₁)) = outMap C (F i (inMap C y₂)) := by
      have := h; simp only [dataOfBallMaps, conjMap_eq, Function.comp_apply] at this; exact this
    exact inMap_injective hC (hinjU hx₁ hx₂ (outMap_injective hC h'))
  · -- disjointness
    intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, h⟩
    simp only [dataOfBallMaps, conjMap_eq, Function.comp_apply] at h
    have h' := outMap_injective hC h
    have hm₁ : F i (inMap C y₁) ∈ F i '' closedBall n (rad i) :=
      ⟨_, hsub i ((mem_closedBall_inMap hC).2 hy₁), rfl⟩
    have hm₂ : F i (inMap C y₁) ∈ F j '' closedBall n (rad j) :=
      ⟨_, hsub j ((mem_closedBall_inMap hC).2 hy₂), h'⟩
    exact Set.disjoint_left.1 (hdisj i j hij) hm₁ hm₂
  · -- into the target
    intro i
    rintro _ ⟨y, hy, rfl⟩
    have hz : F i (inMap C y) ∈ openBall n 1 :=
      hinto i ⟨_, hsub i ((mem_closedBall_inMap hC).2 hy), rfl⟩
    simp only [capBallOpen, mem_setOf_eq, sub_zero, dataOfBallMaps, conjMap_eq,
      Function.comp_apply]
    rw [capacity_outMap hC]
    have : capacity (F i (inMap C y)) < 1 := by simpa only [openBall, mem_setOf_eq] using hz
    nlinarith

end SymplecticPacking.BranchLarge3
