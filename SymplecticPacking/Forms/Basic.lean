import Mathlib
import SymplecticPacking.E4

/-!
# Coordinate differential forms on a normed space `E`

Forms are fields `E → E →L[ℝ] ℝ` (1-forms) and `E → E →L[ℝ] E →L[ℝ] ℝ` (2-forms), matching the
OAI convention in `Moser/SymplecticFamily.lean` (there with an extra time variable).
We define `d` on functions and 1-forms, pullbacks, the wedge of two covectors, closedness of
2-forms, and prove the basic identities (`d ∘ d = 0`, Leibniz, naturality, functoriality).
At the end: a 4-dimensional Pfaffian criterion for nondegeneracy and the "split form"
computation used in `sec:fer` (Lemma bundle-positivity).
-/

noncomputable section

namespace SymplecticPacking.Forms

open ContinuousLinearMap
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Definitions -/

/-- 1-forms on `E` (in coordinates). -/
abbrev Form1 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E → E →L[ℝ] ℝ

/-- 2-forms on `E` (in coordinates). -/
abbrev Form2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E → E →L[ℝ] E →L[ℝ] ℝ

/-- Exterior derivative of a function. -/
def d0 (f : E → ℝ) : Form1 E := fun x => fderiv ℝ f x

/-- Exterior derivative of a 1-form: `d1 α x v w = Dα(x) v w - Dα(x) w v`. -/
def d1 (α : Form1 E) : Form2 E := fun x => fderiv ℝ α x - (fderiv ℝ α x).flip

/-- Pullback of a 1-form. -/
def pull1 (φ : E → F) (α : Form1 F) : Form1 E := fun x => (α (φ x)).comp (fderiv ℝ φ x)

/-- Pullback of a 2-form. -/
def pull2 (φ : E → F) (Ω : Form2 F) : Form2 E :=
  fun x => (Ω (φ x)).bilinearComp (fderiv ℝ φ x) (fderiv ℝ φ x)

/-- Wedge of two covectors: `(α ∧ β)(v, w) = α v * β w - α w * β v`. -/
def wedge (α β : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ := α.smulRight β - β.smulRight α

/-- Pointwise wedge of two 1-form fields. -/
def wedgeF (α β : Form1 E) : Form2 E := fun x => wedge (α x) (β x)

/-- Closedness of a 2-form (same convention as `hclosed` in OAI's
`formMoserField_transport_equation`, without the time variable). -/
def IsClosed2 (Ω : Form2 E) : Prop :=
  ∀ x u v w, fderiv ℝ Ω x u v w - fderiv ℝ Ω x v u w + fderiv ℝ Ω x w u v = 0

/-! ### Application lemmas -/

@[simp] lemma d0_apply (f : E → ℝ) (x v : E) : d0 f x v = fderiv ℝ f x v := rfl

@[simp] lemma d1_apply (α : Form1 E) (x v w : E) :
    d1 α x v w = fderiv ℝ α x v w - fderiv ℝ α x w v := rfl

@[simp] lemma pull1_apply (φ : E → F) (α : Form1 F) (x v : E) :
    pull1 φ α x v = α (φ x) (fderiv ℝ φ x v) := rfl

@[simp] lemma pull2_apply (φ : E → F) (Ω : Form2 F) (x v w : E) :
    pull2 φ Ω x v w = Ω (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := rfl

@[simp] lemma wedge_apply (α β : E →L[ℝ] ℝ) (v w : E) :
    wedge α β v w = α v * β w - α w * β v := by
  simp [wedge, smulRight_apply, smul_eq_mul]; ring

@[simp] lemma wedgeF_apply (α β : Form1 E) (x v w : E) :
    wedgeF α β x v w = α x v * β x w - α x w * β x v := wedge_apply _ _ _ _

/-! ### Skewness -/

lemma d1_skew (α : Form1 E) (x v w : E) : d1 α x v w = -d1 α x w v := by simp

/-! ### Second derivatives -/

/-- `C²` at a point gives symmetric second derivative (Mathlib's Schwarz theorem). -/
lemma symm2 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {f : E → H} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
  (hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])).eq v w

lemma differentiableAt_fderiv_of_contDiffAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → H} {x : E} (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-! ### `d1 ∘ d0 = 0` -/

/-! ### Linearity and Leibniz rule -/

lemma d1_add_apply {α β : Form1 E} {x : E} (hα : DifferentiableAt ℝ α x)
    (hβ : DifferentiableAt ℝ β x) : d1 (α + β) x = d1 α x + d1 β x := by
  ext v w
  have h : fderiv ℝ (α + β) x = fderiv ℝ α x + fderiv ℝ β x := fderiv_add hα hβ
  simp only [d1_apply, add_apply, h]; ring

theorem d1_smul_const (c : ℝ) (α : Form1 E) : d1 (c • α) = c • d1 α := by
  funext x
  ext v w
  have h : fderiv ℝ (c • α) x = c • fderiv ℝ α x := by
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := α) c]; rfl
  simp only [d1_apply, Pi.smul_apply, smul_apply, h, smul_eq_mul]; ring

lemma d1_mul_apply {g : E → ℝ} {α : Form1 E} {x : E} (hg : DifferentiableAt ℝ g x)
    (hα : DifferentiableAt ℝ α x) :
    d1 (fun y => g y • α y) x = wedge (d0 g x) (α x) + g x • d1 α x := by
  ext v w
  have h := fderiv_fun_smul hg hα
  simp only [d1_apply, h, add_apply, smul_apply, smulRight_apply, wedge_apply, d0_apply,
    smul_eq_mul]
  ring

/-! ### Pullbacks: naturality and functoriality -/

lemma pull2_comp_apply {φ : E → F} {ψ : F → G} {Ω : Form2 G} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ (φ x)) :
    pull2 (ψ ∘ φ) Ω x = pull2 φ (pull2 ψ Ω) x := by
  ext v w
  simp only [pull2_apply, fderiv_comp x hψ hφ, comp_apply, Function.comp_apply]

/-- `d` commutes with pullback (pointwise): `d(φ^*α) = φ^*(dα)`. -/
lemma pull2_d1_apply {φ : E → F} {α : Form1 F} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
    (hα : DifferentiableAt ℝ α (φ x)) : d1 (pull1 φ α) x = pull2 φ (d1 α) x := by
  have hφ1 : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have hA : HasFDerivAt (fun y => α (φ y)) ((fderiv ℝ α (φ x)).comp (fderiv ℝ φ x)) x :=
    hα.hasFDerivAt.comp x hφ1.hasFDerivAt
  have hB : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (differentiableAt_fderiv_of_contDiffAt hφ).hasFDerivAt
  have hC := hA.clm_comp hB
  have hD : fderiv ℝ (pull1 φ α) x = _ := hC.fderiv
  ext v w
  simp only [d1_apply, pull2_apply, hD, add_apply, comp_apply, compL_apply, flip_apply]
  rw [symm2 hφ v w]
  ring

theorem pull2_d1 {φ : E → F} {α : Form1 F} (hφ : ContDiff ℝ 2 φ) (hα : ContDiff ℝ 1 α) :
    d1 (pull1 φ α) = pull2 φ (d1 α) :=
  funext fun _ => pull2_d1_apply hφ.contDiffAt (hα.differentiable one_ne_zero _)

/-! ### `d1 α` is closed -/

/-! Note: Mathlib's `fderiv` is stated for topological vector spaces, so for a field
`E → E →L E →L ℝ` the instances on `E →L E →L ℝ` are found directly, and Lean fails to unify
them with the normed-space instances used by e.g. `HasFDerivAt.comp` (and `+`/`-` on
`E →L E →L E →L ℝ` fail to synthesize). We therefore compute `fderiv (d1 α)` only after
evaluating, via `fderiv_clm_apply`. -/

lemma differentiableAt_eval2 {A : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : DifferentiableAt ℝ A x)
    (v w : E) : DifferentiableAt ℝ (fun y => A y v w) x := by
  fun_prop

lemma fderiv_eval2 {A : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : DifferentiableAt ℝ A x)
    (u v w : E) : fderiv ℝ (fun y => A y v w) x u = fderiv ℝ A x u v w := by
  have h1 : DifferentiableAt ℝ (fun y => A y v) x := by fun_prop
  rw [fderiv_clm_apply h1 (differentiableAt_const w)]
  simp
  rw [fderiv_clm_apply h (differentiableAt_const v)]
  simp

/-- The derivative of `d1 α`, evaluated (assuming `d1 α` is differentiable at `x`). -/
lemma fderiv_d1_apply {α : Form1 E} {x : E} (hα : ContDiffAt ℝ 2 α x)
    (hd : DifferentiableAt ℝ (d1 α) x) (u v w : E) :
    fderiv ℝ (d1 α) x u v w =
      fderiv ℝ (fderiv ℝ α) x u v w - fderiv ℝ (fderiv ℝ α) x u w v := by
  have hB := differentiableAt_fderiv_of_contDiffAt hα
  rw [← fderiv_eval2 hd]
  have he : (fun y => d1 α y v w) = fun y => fderiv ℝ α y v w - fderiv ℝ α y w v := by
    funext y; simp
  rw [he, fderiv_fun_sub (differentiableAt_eval2 hB v w) (differentiableAt_eval2 hB w v)]
  simp [fderiv_eval2 hB]

theorem isClosed2_d1_at {α : Form1 E} {x : E} (hα : ContDiffAt ℝ 2 α x) (u v w : E) :
    fderiv ℝ (d1 α) x u v w - fderiv ℝ (d1 α) x v u w + fderiv ℝ (d1 α) x w u v = 0 := by
  by_cases hd : DifferentiableAt ℝ (d1 α) x
  · rw [fderiv_d1_apply hα hd, fderiv_d1_apply hα hd, fderiv_d1_apply hα hd]
    rw [symm2 hα u v, symm2 hα u w, symm2 hα v w]
    ring
  · simp [fderiv_zero_of_not_differentiableAt hd]

theorem isClosed2_d1 {α : Form1 E} (hα : ContDiff ℝ 2 α) : IsClosed2 (d1 α) :=
  fun _ u v w => isClosed2_d1_at hα.contDiffAt u v w

/-! ### Four dimensions: the Pfaffian -/

/-- Standard basis of `E4`. -/
abbrev e (i : Fin 4) : E4 := EuclideanSpace.single i 1

/-- Pfaffian of a bilinear form on `E4` (w.r.t. the standard basis). -/
def pf (Ω : E4 →L[ℝ] E4 →L[ℝ] ℝ) : ℝ :=
  Ω (e 0) (e 1) * Ω (e 2) (e 3) - Ω (e 0) (e 2) * Ω (e 1) (e 3) + Ω (e 0) (e 3) * Ω (e 1) (e 2)

lemma E4_eq_sum (v : E4) : v = v 0 • e 0 + v 1 • e 1 + v 2 • e 2 + v 3 • e 3 := by
  ext i; fin_cases i <;> simp

/-- A skew bilinear form on `E4` with nonzero Pfaffian is nondegenerate. -/
theorem pf_ne_zero_nondeg {Ω : E4 →L[ℝ] E4 →L[ℝ] ℝ} (hskew : ∀ v w, Ω v w = -Ω w v)
    (hpf : pf Ω ≠ 0) : ∀ v, (∀ w, Ω v w = 0) → v = 0 := by
  intro v hv
  have hc : ∀ j, v 0 * Ω (e 0) (e j) + v 1 * Ω (e 1) (e j) + v 2 * Ω (e 2) (e j)
      + v 3 * Ω (e 3) (e j) = 0 := by
    intro j
    have h := hv (e j)
    rw [E4_eq_sum v] at h
    simpa only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] using h
  have hd : ∀ i, Ω (e i) (e i) = 0 := fun i => by linarith [hskew (e i) (e i)]
  have c0 := hc 0; have c1 := hc 1; have c2 := hc 2; have c3 := hc 3
  simp only [hd, hskew (e 1) (e 0), hskew (e 2) (e 0), hskew (e 3) (e 0), hskew (e 2) (e 1),
    hskew (e 3) (e 1), hskew (e 3) (e 2)] at c0 c1 c2 c3
  set a01 := Ω (e 0) (e 1); set a02 := Ω (e 0) (e 2); set a03 := Ω (e 0) (e 3)
  set a12 := Ω (e 1) (e 2); set a13 := Ω (e 1) (e 3); set a23 := Ω (e 2) (e 3)
  have k0 : pf Ω * v 0 = 0 := by
    simp only [pf]; linear_combination a23 * c1 - a13 * c2 + a12 * c3
  have k1 : pf Ω * v 1 = 0 := by
    simp only [pf]; linear_combination -(a23 * c0 - a03 * c2 + a02 * c3)
  have k2 : pf Ω * v 2 = 0 := by
    simp only [pf]; linear_combination -(-a13 * c0 + a03 * c1 - a01 * c3)
  have k3 : pf Ω * v 3 = 0 := by
    simp only [pf]; linear_combination -(a12 * c0 - a02 * c1 + a01 * c2)
  ext i
  fin_cases i
  · exact (mul_eq_zero.mp k0).resolve_left hpf
  · exact (mul_eq_zero.mp k1).resolve_left hpf
  · exact (mul_eq_zero.mp k2).resolve_left hpf
  · exact (mul_eq_zero.mp k3).resolve_left hpf

/-! ### The split form of `sec:fer` (Lemma bundle-positivity) -/

/-- Coordinate covector `dx_i` on `E4`; coordinates `(x, y, u, v)` = indices `(0,1,2,3)`. -/
abbrev dc (i : Fin 4) : E4 →L[ℝ] ℝ := EuclideanSpace.proj i

/-- `Ω = dx∧dy + k du∧dv + dp∧γ` with `dp = p1 dx + p2 dy`, `γ = g1 du + g2 dv`. -/
def splitForm (p1 p2 g1 g2 k : ℝ) : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  wedge (dc 0) (dc 1) + k • wedge (dc 2) (dc 3) +
    wedge (p1 • dc 0 + p2 • dc 1) (g1 • dc 2 + g2 • dc 3)

lemma splitForm_skew (p1 p2 g1 g2 k : ℝ) (v w : E4) :
    splitForm p1 p2 g1 g2 k v w = -splitForm p1 p2 g1 g2 k w v := by
  simp only [splitForm, add_apply, smul_apply, wedge_apply, smul_eq_mul]; ring

theorem pf_splitForm (p1 p2 g1 g2 k : ℝ) : pf (splitForm p1 p2 g1 g2 k) = k := by
  simp [pf, splitForm, wedge_apply]; ring

theorem splitForm_nondeg {p1 p2 g1 g2 k : ℝ} (hk : k ≠ 0) :
    ∀ v, (∀ w, splitForm p1 p2 g1 g2 k v w = 0) → v = 0 :=
  pf_ne_zero_nondeg (splitForm_skew p1 p2 g1 g2 k) (by rw [pf_splitForm]; exact hk)

end SymplecticPacking.Forms
