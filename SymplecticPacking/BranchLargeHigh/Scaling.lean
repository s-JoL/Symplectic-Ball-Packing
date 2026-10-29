import SymplecticPacking.General.Interface

/-!
# Normalisation by one dilation

Paper `def:ham-normalise`: physical data `(C, c_i)` correspond to normalised data `(1, c_i/C)`
under the single dilation `y ↦ y/√C`. A normalised map `g` becomes the physical map
`scaleConj C g = √C · g(· / √C)`; it is symplectic wherever `g` is, and capacities scale by `C`.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Set
open scoped ContDiff

variable {n : ℕ}

lemma omega0_smul_left (r : ℝ) (x y : E n) :
    Problem.omega0 (r • x) y = r * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => by ring

lemma omega0_smul_right (r : ℝ) (x y : E n) :
    Problem.omega0 x (r • y) = r * Problem.omega0 x y := by
  simp only [Problem.omega0, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => by ring

/-- The physical map of a normalised map `g`: `y ↦ √C · g(y/√C)`. -/
def scaleConj (C : ℝ) (g : E n → E n) (y : E n) : E n :=
  Real.sqrt C • g ((Real.sqrt C)⁻¹ • y)

section
variable {C : ℝ} (hC : 0 < C)
include hC

lemma cap_smul_inv (y : E n) :
    Real.pi * ‖(Real.sqrt C)⁻¹ • y‖ ^ 2 = (Real.pi * ‖y‖ ^ 2) / C := by
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hC), inv_pow,
    Real.sq_sqrt hC.le]
  field_simp

lemma cap_smul (z : E n) :
    Real.pi * ‖Real.sqrt C • z‖ ^ 2 = C * (Real.pi * ‖z‖ ^ 2) := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hC), Real.sq_sqrt hC.le]
  ring

lemma mem_capBall_scale {y : E n} {e : ℝ} :
    y ∈ capBall 0 (C * e) ↔ (Real.sqrt C)⁻¹ • y ∈ capBall 0 e := by
  simp only [capBall, mem_setOf_eq, sub_zero, cap_smul_inv hC]
  rw [div_le_iff₀ hC, mul_comm e]

lemma mem_capBallOpen_scale {y : E n} {e : ℝ} :
    y ∈ capBallOpen 0 (C * e) ↔ (Real.sqrt C)⁻¹ • y ∈ capBallOpen 0 e := by
  simp only [capBallOpen, mem_setOf_eq, sub_zero, cap_smul_inv hC]
  rw [div_lt_iff₀ hC, mul_comm e]

lemma scaleConj_cap (g : E n → E n) (y : E n) :
    Real.pi * ‖scaleConj C g y‖ ^ 2 = C * (Real.pi * ‖g ((Real.sqrt C)⁻¹ • y)‖ ^ 2) :=
  cap_smul hC _

lemma scaleConj_contDiffOn {g : E n → E n} {d : ℝ} (hg : ContDiffOn ℝ ∞ g (capBallOpen 0 d)) :
    ContDiffOn ℝ ∞ (scaleConj C g) (capBallOpen 0 (C * d)) := by
  unfold scaleConj
  refine ContDiffOn.const_smul _ (hg.comp (contDiff_const_smul _).contDiffOn ?_)
  intro y hy; exact (mem_capBallOpen_scale hC).1 hy

lemma scaleConj_injOn {g : E n → E n} {e : ℝ} (hg : InjOn g (capBall 0 e)) :
    InjOn (scaleConj C g) (capBall 0 (C * e)) := by
  intro y hy y' hy' h
  have hs : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
  have h1 := hg ((mem_capBall_scale hC).1 hy) ((mem_capBall_scale hC).1 hy')
    (smul_right_injective _ hs h)
  have := congrArg (fun z => Real.sqrt C • z) h1
  simpa [smul_smul, hs] using this

lemma scaleConj_image (g : E n → E n) (e : ℝ) :
    scaleConj C g '' capBall 0 (C * e) = (Real.sqrt C • ·) '' (g '' capBall 0 e) := by
  have hs : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
  ext z
  simp only [mem_image, scaleConj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g ((Real.sqrt C)⁻¹ • y), ⟨_, (mem_capBall_scale hC).1 hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨Real.sqrt C • x, (mem_capBall_scale hC).2 (by simpa [smul_smul, hs] using hx), ?_⟩
    simp [smul_smul, hs]

/-- The physical map is symplectic wherever the normalised map is. -/
lemma scaleConj_sympl {g : E n → E n} {y : E n}
    (hd : DifferentiableAt ℝ g ((Real.sqrt C)⁻¹ • y))
    (hs : ∀ v w, Problem.omega0 (fderiv ℝ g ((Real.sqrt C)⁻¹ • y) v)
      (fderiv ℝ g ((Real.sqrt C)⁻¹ • y) w) = Problem.omega0 v w) :
    IsSymplecticLinear (fderiv ℝ (scaleConj C g) y) := by
  set s := Real.sqrt C
  have hs0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
  have hL : HasFDerivAt (scaleConj C g)
      (s • (fderiv ℝ g (s⁻¹ • y)).comp (s⁻¹ • ContinuousLinearMap.id ℝ (E n))) y := by
    have h1 : HasFDerivAt (fun y : E n => s⁻¹ • y) (s⁻¹ • ContinuousLinearMap.id ℝ (E n)) y :=
      ((ContinuousLinearMap.id ℝ (E n)).hasFDerivAt).const_smul s⁻¹
    exact (hd.hasFDerivAt.comp y h1).const_smul s
  intro v w
  rw [hL.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul]
  rw [omega0_smul_left, omega0_smul_right, omega0_smul_left, omega0_smul_right, hs]
  field_simp

end

end SymplecticPacking.BranchLargeHigh
