import SymplecticPacking.Forms.Basic
import SymplecticPacking.Return.Algebra

/-!
# The ball chart

`sec:rtc`, the ball chart (Lemma lem:rtc-ball-chart).

* `ballChart Z = (conj Z₀/|Z₀|) (Z₁, Z₂)/√π` on unit representatives with `Z₀ ≠ 0`:
  gauge invariance, the affine form `z/√(π(1+|z|²))`, and `π‖b‖² = 1 − |Z₀|² < 1`.
* The symplectic identity in the affine chart, as an identity of coordinate 2-forms on `E4`:
  `pull2 ballAffine ωstd = d1 lamFS`, where `ωstd` is `omega0` (`E4.lean`) and
  `lamFS = d^c log(1+|z|²) = Σ Im(conj z_j dz_j)/(2π(1+|z|²))`, so `d1 lamFS = ω_FS`.

Coordinates: `ℂ² ≅ E4` by `(z₁, z₂) ↦ (Re z₁, Re z₂, Im z₁, Im z₂)` (`c2ToE4`); with this
identification `omega0 = dx₁∧dy₁ + dx₂∧dy₂` (`z_j = x_j + i y_j`).
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate SymplecticPacking.Forms ContinuousLinearMap
open scoped Real

/-! ### The ball chart on unit representatives -/

/-- `b_ball[Z] = (conj Z₀/|Z₀|) (Z₁, Z₂)/√π`. -/
def ballChart (Z : C3) : ℂ × ℂ :=
  (conj (Z 0) / (‖Z 0‖ : ℂ) * Z 1 / (Real.sqrt π : ℂ),
   conj (Z 0) / (‖Z 0‖ : ℂ) * Z 2 / (Real.sqrt π : ℂ))

/-- `|z|² = |z₁|² + |z₂|²` on `ℂ²`. -/
def nsq2 (z : ℂ × ℂ) : ℝ := normSq z.1 + normSq z.2

/-- In the affine chart `z = (Z₁/Z₀, Z₂/Z₀)`, `b_ball = z/√(π(1+|z|²))`. -/
theorem ballChart_affine (Z : C3) (hZ : nsq Z = 1) (h0 : Z 0 ≠ 0) :
    ballChart Z = ((1 / Real.sqrt (π * (1 + nsq2 (Z 1 / Z 0, Z 2 / Z 0))) : ℝ) : ℂ) •
      (Z 1 / Z 0, Z 2 / Z 0) := by
  set a := ‖Z 0‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr h0
  have hn0 : normSq (Z 0) = a ^ 2 := normSq_eq_norm_sq _
  have h1 : 1 + nsq2 (Z 1 / Z 0, Z 2 / Z 0) = 1 / a ^ 2 := by
    simp only [nsq, Fin.sum_univ_three] at hZ
    simp only [nsq2, normSq_div, hn0]
    field_simp
    linarith
  have hs : Real.sqrt (π * (1 + nsq2 (Z 1 / Z 0, Z 2 / Z 0))) = Real.sqrt π / a := by
    rw [h1, mul_one_div, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq hapos.le]
  rw [hs]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hcz : conj (Z 0) * Z 0 = ((a : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_normSq', hn0]; push_cast; ring
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hapos.ne'
  have hpi' : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
  simp only [ballChart, Prod.smul_mk, smul_eq_mul, ← ha]
  push_cast
  ext <;> simp only [] <;> field_simp <;> linear_combination (Z _) * hcz

/-- `π ‖b_ball‖² = 1 − |Z₀|²`. -/
theorem ballChart_norm (Z : C3) (hZ : nsq Z = 1) (h0 : Z 0 ≠ 0) :
    π * nsq2 (ballChart Z) = 1 - normSq (Z 0) := by
  have hapos : 0 < ‖Z 0‖ := norm_pos_iff.mpr h0
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  simp only [nsq, Fin.sum_univ_three] at hZ
  simp only [nsq2, ballChart, normSq_mul, normSq_div, normSq_conj, normSq_ofReal,
    normSq_eq_norm_sq (Z 0)]
  field_simp
  rw [normSq_eq_norm_sq (Z 0)] at hZ
  rw [Real.sq_sqrt Real.pi_pos.le]
  linear_combination π * hZ

/-- The image lies in the open capacity-one ball: `π ‖b_ball‖² < 1`. -/
theorem ballChart_norm_lt (Z : C3) (hZ : nsq Z = 1) (h0 : Z 0 ≠ 0) :
    π * nsq2 (ballChart Z) < 1 := by
  rw [ballChart_norm Z hZ h0]
  have := normSq_pos.mpr h0
  linarith

/-! ### The symplectic identity in the affine chart -/

/-- `ℂ² → E4`, `(z₁, z₂) ↦ (Re z₁, Re z₂, Im z₁, Im z₂)`. -/
def c2ToE4 (z : ℂ × ℂ) : E4 := WithLp.toLp 2 ![z.1.re, z.2.re, z.1.im, z.2.im]

lemma norm_c2ToE4_sq (z : ℂ × ℂ) : ‖c2ToE4 z‖ ^ 2 = nsq2 z := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [c2ToE4, Fin.sum_univ_four, nsq2, normSq_apply]
  ring

/-- The affine ball chart on `E4`: `x ↦ x/√(π(1+‖x‖²))`. -/
def ballAffine (x : E4) : E4 := (1 / Real.sqrt (π * (1 + ‖x‖ ^ 2))) • x

lemma ballAffine_c2ToE4 (z : ℂ × ℂ) :
    ballAffine (c2ToE4 z) = c2ToE4 (((1 / Real.sqrt (π * (1 + nsq2 z)) : ℝ) : ℂ) • z) := by
  rw [ballAffine, norm_c2ToE4_sq]
  ext i
  fin_cases i <;> simp [c2ToE4]

/-- The standard form `omega0` as a bilinear map: `dx₀∧dx₂ + dx₁∧dx₃`. -/
def omegaStd : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  wedge (EuclideanSpace.proj 0) (EuclideanSpace.proj 2) +
    wedge (EuclideanSpace.proj 1) (EuclideanSpace.proj 3)

lemma omegaStd_apply (v w : E4) : omegaStd v w = omega0 v w := by
  simp [omegaStd, omega0]; ring

lemma omegaStd_skew (v w : E4) : omegaStd v w = -omegaStd w v := by
  rw [omegaStd_apply, omegaStd_apply, omega0, omega0]; ring

/-- `ω_std` as a (constant) coordinate 2-form on `E4`. -/
def ωstd : Form2 E4 := fun _ => omegaStd

/-- The Liouville form `λ_std = ½ Σ Im(conj y_j dy_j) = ½ ω_std(y, ·)`. -/
def lamStd : Form1 E4 := ⇑((1 / 2 : ℝ) • omegaStd)

/-- `λ_FS = d^c log(1+|z|²) = Σ Im(conj z_j dz_j)/(2π(1+|z|²))`, `z_j = x_j + i x_{j+2}`. -/
def lamFS : Form1 E4 := fun x =>
  (1 / (2 * π * (1 + ‖x‖ ^ 2))) •
    (x 0 • EuclideanSpace.proj 2 - x 2 • EuclideanSpace.proj 0 +
      x 1 • EuclideanSpace.proj 3 - x 3 • EuclideanSpace.proj 1)

lemma d1_lamStd : d1 lamStd = ωstd := by
  funext x
  ext v w
  have h : fderiv ℝ lamStd x = (1 / 2 : ℝ) • omegaStd := ContinuousLinearMap.fderiv _
  simp only [d1_apply, h, ωstd, smul_apply, smul_eq_mul]
  rw [omegaStd_skew w v]; ring

/-- The scalar factor `c(x) = 1/√(π(1+‖x‖²))`. -/
def cFac (x : E4) : ℝ := 1 / Real.sqrt (π * (1 + ‖x‖ ^ 2))

lemma cFac_arg_pos (x : E4) : 0 < π * (1 + ‖x‖ ^ 2) := by positivity

lemma contDiff_cFac {n : WithTop ℕ∞} : ContDiff ℝ n cFac := by
  have h1 : ContDiff ℝ n fun x : E4 => π * (1 + ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_const.add (contDiff_norm_sq ℝ))
  have h2 := h1.sqrt fun x => (cFac_arg_pos x).ne'
  exact contDiff_const.div h2 fun x => (Real.sqrt_pos.mpr (cFac_arg_pos x)).ne'

lemma ballAffine_eq : ballAffine = fun x => cFac x • x := rfl

lemma contDiff_ballAffine {n : WithTop ℕ∞} : ContDiff ℝ n ballAffine := by
  rw [ballAffine_eq]; exact contDiff_cFac.smul contDiff_id

lemma cFac_sq (x : E4) : cFac x ^ 2 = 1 / (π * (1 + ‖x‖ ^ 2)) := by
  rw [cFac, div_pow, Real.sq_sqrt (cFac_arg_pos x).le, one_pow]

lemma pull1_lamStd : pull1 ballAffine lamStd = lamFS := by
  funext x
  ext v
  have hd : DifferentiableAt ℝ cFac x := (contDiff_cFac (n := 1)).differentiable one_ne_zero x
  have hD : fderiv ℝ ballAffine x v = cFac x • v + fderiv ℝ cFac x v • x := by
    have h := hd.hasFDerivAt.smul (hasFDerivAt_id x)
    rw [ballAffine_eq, show (fun y : E4 => cFac y • y) = cFac • id from rfl, h.fderiv]
    simp
  rw [pull1_apply, hD]
  have e1 : lamStd (ballAffine x) (cFac x • v + fderiv ℝ cFac x v • x) =
      1 / 2 * (cFac x ^ 2 * omega0 x v + cFac x * fderiv ℝ cFac x v * omega0 x x) := by
    simp only [lamStd, ballAffine_eq, smul_apply, map_add, map_smul, smul_eq_mul,
      omegaStd_apply]
    ring
  have e2 : lamFS x v = 1 / (2 * (π * (1 + ‖x‖ ^ 2))) * omega0 x v := by
    simp only [lamFS, smul_apply, add_apply, sub_apply, smul_eq_mul, PiLp.proj_apply,
      omega0]
    ring
  rw [e1, e2, cFac_sq]
  generalize π * (1 + ‖x‖ ^ 2) = X
  simp only [omega0]
  ring

/-- The ball chart is symplectic in the affine chart: `b^* ω_std = d λ_FS = ω_FS`. -/
theorem ballChart_symplectic : pull2 ballAffine ωstd = d1 lamFS := by
  have hl : ContDiff ℝ 1 lamStd := ((1 / 2 : ℝ) • omegaStd).contDiff
  rw [← d1_lamStd, ← pull2_d1 contDiff_ballAffine hl, pull1_lamStd]

end SymplecticPacking.Return
