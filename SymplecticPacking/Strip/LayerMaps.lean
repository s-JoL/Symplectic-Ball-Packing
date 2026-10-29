import SymplecticPacking.Strip.Layer

/-!
# Source coordinates of the layer maps

`sec:str-layer-maps` (`cons:str-layer-map`): the complex coordinates of the source of the layer
maps `E_i`; the maps themselves for cubic data are in `Branch2/Model/Cubic/Strip/LayerMaps.lean`.

The source `ℂ² ∋ (z_b, z_f)` is `E4` with `z_b = q₁ + i p₁ = zbL X` (`X 0 + i X 2`) and
`z_f = q₂ + i p₂ = zfL X` (`X 1 + i X 3`), so that `ω_std = ω_ℂ(z_b) + ω_ℂ(z_f)` is `omega0`
(`omega0_eq`). Also: `omega2_eq_im`, `omega2_rot` (the area form of `ℂ` and its rotation
invariance), `norm_sq_E4`, `pull2_congr_pt`.
-/

noncomputable section

namespace SymplecticPacking.Strip

open Set Filter Topology ContinuousLinearMap ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE bB annulus u0 u1)
open SymplecticPacking.Handle (mk mkL wL omegaV aLayer rhoLayer layerLeft layerRight OmegaPre)
open SymplecticPacking.Qhat (omega2)
open scoped ContDiff Real

/-! ### Complex helpers -/

lemma omega2_eq_im (a b : ℂ) : omega2 a b = (conj a * b).im := by
  simp [omega2, Complex.mul_im]; ring

lemma omega2_rot {R : ℂ} (hR : conj R * R = 1) (a b : ℂ) :
    omega2 (R * a) (R * b) = omega2 a b := by
  rw [omega2_eq_im, omega2_eq_im, map_mul]
  congr 1
  linear_combination (conj a * b) * hR

lemma dpE_eq_re (Z u : E4) : dpE Z u = 2 * π * (conj (wL Z) * wL u).re := by
  simp [dpE, Handle.dc_apply, Complex.mul_re]; ring

lemma conj_exp_mul (θ : ℝ) :
    conj (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp

variable (P : Params)

/-! ### The fibre shear (`prop:shd4-maps`) -/

/-- **The fibre shear** `Σ_{i,T}(z) = exp(−2πi T a_i'(π|z|²)) z`. -/
def shear (i : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((-(2 * π) * (T * deriv (aLayer P i) (π * ‖z‖ ^ 2)) : ℝ) : ℂ) * Complex.I) * z

/-- Its inverse `z ↦ exp(2πi T a_i'(π|z|²)) z`. -/
def shearInv (i : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((((2 * π) * (T * deriv (aLayer P i) (π * ‖z‖ ^ 2)) : ℝ) : ℂ) * Complex.I) * z

@[simp] lemma norm_shear (i : ℕ) (T : ℝ) (z : ℂ) : ‖shear P i T z‖ = ‖z‖ := by
  rw [shear, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

@[simp] lemma norm_shearInv (i : ℕ) (T : ℝ) (z : ℂ) : ‖shearInv P i T z‖ = ‖z‖ := by
  rw [shearInv, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The shear on `E4`** `(w, x, T) ↦ (Σ_{i,T}(w), x, T)`. -/
def shearE (i : ℕ) (Y : E4) : E4 := mk (shear P i (Y 3) (wL Y)) (Y 2) (Y 3)

@[simp] lemma pE_shearE (i : ℕ) (Y : E4) : pE (shearE P i Y) = pE Y := by
  rw [shearE, Handle.pE_mk, norm_shear, Handle.pE_eq]

@[simp] lemma shearE_apply2 (i : ℕ) (Y : E4) : shearE P i Y 2 = Y 2 := by simp [shearE]
@[simp] lemma shearE_apply3 (i : ℕ) (Y : E4) : shearE P i Y 3 = Y 3 := by simp [shearE]

/-! ### Source coordinates and the strip map -/

/-- `z_b = q₁ + i p₁`. -/
def zbL : E4 →L[ℝ] ℂ := (dc 0).smulRight (1 : ℂ) + (dc 2).smulRight Complex.I

/-- `z_f = q₂ + i p₂`. -/
def zfL : E4 →L[ℝ] ℂ := (dc 1).smulRight (1 : ℂ) + (dc 3).smulRight Complex.I

@[simp] lemma zbL_re (X : E4) : (zbL X).re = X 0 := by simp [zbL]
@[simp] lemma zbL_im (X : E4) : (zbL X).im = X 2 := by simp [zbL]
@[simp] lemma zfL_re (X : E4) : (zfL X).re = X 1 := by simp [zfL]
@[simp] lemma zfL_im (X : E4) : (zfL X).im = X 3 := by simp [zfL]

/-- `ω_std = ω_ℂ(z_b) + ω_ℂ(z_f)` is `omega0`. -/
theorem omega0_eq (v w : E4) : omega0 v w = omega2 (zbL v) (zbL w) + omega2 (zfL v) (zfL w) := by
  simp [omega0, omega2]; ring

theorem E4_ext_zb_zf {X X' : E4} (hb : zbL X = zbL X') (hf : zfL X = zfL X') : X = X' := by
  have h0 := congrArg Complex.re hb; have h2 := congrArg Complex.im hb
  have h1 := congrArg Complex.re hf; have h3 := congrArg Complex.im hf
  simp only [zbL_re, zbL_im, zfL_re, zfL_im] at h0 h1 h2 h3
  ext j; fin_cases j <;> simp [h0, h1, h2, h3]

theorem norm_sq_E4 (X : E4) : ‖X‖ ^ 2 = ‖zbL X‖ ^ 2 + ‖zfL X‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_four]
  simp only [Complex.sq_norm, Complex.normSq_apply, zbL_re, zbL_im, zfL_re, zfL_im,
    Real.norm_eq_abs, sq_abs]
  ring

/-- **The source ball** `𝔹_{ρ̂} = {π|z_b|² + π|z_f|² < ρ̂}`. -/
def srcBall : Set E4 := {X | π * ‖zbL X‖ ^ 2 + π * ‖zfL X‖ ^ 2 < rhoHat P}

/-! ### The layer maps (`cons:str-layer-map`) -/

lemma pull2_congr_pt {φ : E4 → E4} {Ω Ω' : Form2 E4} {x : E4} (h : Ω (φ x) = Ω' (φ x)) :
    pull2 φ Ω x = pull2 φ Ω' x := by
  unfold pull2; rw [h]

/-- **The layer map** `E_i(z_b, z_f) = (s = σ_i(x, T, p), v = v(T), Σ_{i,T}(z_f))` with
`(x, T) = Ψ_strip(z_b)`, `p = π|z_f|²` (the fibre point in the unitary frame of `𝒜⁺`). -/
def layerMap (i : ℕ) (X : E4) : E4 :=
  mk (shear P i (psiStrip (deltaStrip P) (zbL X)).im (zfL X))
    (layerRoot P i (psiStrip (deltaStrip P) (zbL X)).re (psiStrip (deltaStrip P) (zbL X)).im
      (π * ‖zfL X‖ ^ 2))
    (vOfT (psiStrip (deltaStrip P) (zbL X)).im)

end SymplecticPacking.Strip
