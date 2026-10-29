import SymplecticPacking.Handle.Twist

/-!
# The `𝒜⁺`-frame chart of the handle

`sec:shd-four` (notation and standing facts): the fibre rotation between the global
`Zunit`-frame coordinates and the local `𝒜⁺`-frame coordinates of the handle.

The global representation of `N` over the cover is `E4` with coordinates `(x, y, u, v)`, the
fibre coordinate `w_Z = x + iy` being taken in the frame `Zunit` (`Bundle/OmegaT.lean`). Over the
band `𝒜⁺ = {1/12 < u < 1/4}` (where `Z₀ ≠ 0`) the `𝒜⁺`-frame `(Z₀/|Z₀|)³` has fibre coordinate
`w = conj(F) w_Z`, `F = frameA u v`. The handle works in the local coordinates `(x, y, s, t)`
with `w = x + iy`, `(s, t) = (u, v)` (`Handle/Twist.lean`).

* `chartA : (w, s, t) ↦ (F(s, t) w, s, t)` (local → global) and `chartInv` (global → local) are
  the explicit fibre rotations; they preserve `p` (`pE_chartA`, `pE_chartInv`) and the base
  point and are mutually inverse over the band `bandE` (`chartInv_chartA`, `chartA_chartInv`).
* derivatives of `frameA` (`deriv_frameA_u`, `deriv_frameA_v`) and of the charts;
* `splitForm_mk`, `splitForm_rot`, `splitForm_twist`: split forms in the rotated coordinates.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e
  d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus frameA ZnzSet
  lambdaCu lambdaCv etaHu etaHv kappaT kappa1 alpha1 OmegaT OmegaT_split Zunit pp)
open SymplecticPacking.Qhat (omega2)
open scoped ContDiff Real

attribute [local irreducible] frameA Zunit lambdaCu lambdaCv etaHu etaHv Bundle.sigmaC

/-! ### The frame function -/

/-- `F(u, v) = frameA u v = (Z₀/|Z₀|)³` as a function on `ℝ × ℝ`. -/
def FΦ (x : ℝ × ℝ) : ℂ := frameA x.1 x.2

lemma frameA_eq_smul (u v : ℝ) :
    frameA u v = ((‖Zunit u v 0‖⁻¹ : ℝ) • Zunit u v 0) ^ 3 := by
  rw [frameA, Complex.real_smul, div_eq_mul_inv, mul_comm, Complex.ofReal_inv]

lemma contDiff_Z0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => Zunit x.1 x.2 0) :=
  contDiff_pi.mp Bundle.contDiff_Zunit 0

lemma contDiffAt_FΦ {x : ℝ × ℝ} (hx : x ∈ ZnzSet) : ContDiffAt ℝ ∞ FΦ x := by
  have hz : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => Zunit x.1 x.2 0) x := contDiff_Z0.contDiffAt
  have hn := hz.norm ℝ hx
  have hi := hn.inv (norm_ne_zero_iff.mpr hx)
  have h : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ =>
      ((‖Zunit x.1 x.2 0‖⁻¹ : ℝ) • Zunit x.1 x.2 0) ^ 3) x := (hi.smul hz).pow 3
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => frameA_eq_smul y.1 y.2)

lemma norm_FΦ {x : ℝ × ℝ} (hx : x ∈ ZnzSet) : ‖FΦ x‖ = 1 := Bundle.norm_frameA hx

lemma normSq_one {F : ℂ} (hF : ‖F‖ = 1) : F.re * F.re + F.im * F.im = 1 := by
  have := Complex.sq_norm F
  rw [hF, Complex.normSq_apply] at this; linarith

/-- The derivative of the unit frame is infinitesimally a rotation:
`DF(h) = F · i · Im(DF(h)/F)`. -/
lemma fderiv_FΦ_rot {x : ℝ × ℝ} (hx : x ∈ ZnzSet) (h : ℝ × ℝ) :
    fderiv ℝ FΦ x h = FΦ x * (Complex.I * ((fderiv ℝ FΦ x h / FΦ x).im : ℂ)) := by
  have hd : HasFDerivAt FΦ (fderiv ℝ FΦ x) x :=
    ((contDiffAt_FΦ hx).differentiableAt (by simp)).hasFDerivAt
  have hsq := hd.norm_sq
  have hconst : (fun y => ‖FΦ y‖ ^ 2) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Bundle.isOpen_ZnzSet.mem_nhds hx] with y hy
    rw [norm_FΦ hy, one_pow]
  have h0 : (0 : ℝ × ℝ →L[ℝ] ℝ) = 2 • (innerSL ℝ (FΦ x)).comp (fderiv ℝ FΦ x) := by
    rw [← hsq.fderiv, hconst.fderiv_eq]; simp
  have hi := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L h) h0
  simp only [Pi.zero_apply, zero_apply, smul_apply, comp_apply, innerSL_apply_apply,
    nsmul_eq_mul, Nat.cast_ofNat] at hi
  rw [Complex.inner] at hi
  have hF := normSq_one (norm_FΦ hx)
  set F := FΦ x
  set D := fderiv ℝ FΦ x h
  have hre : F.re * D.re + F.im * D.im = 0 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hi; linarith
  have hF0 : F ≠ 0 := by
    intro h0; rw [h0] at hF; simp at hF
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_im, Complex.normSq_apply]
    rw [hF]
    linear_combination F.re * hre - D.re * hF
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_im, Complex.normSq_apply]
    rw [hF]
    linear_combination F.im * hre - D.im * hF

lemma clm_pair_C (L : ℝ × ℝ →L[ℝ] ℂ) (a b : ℝ) :
    L (a, b) = (a : ℂ) * L (1, 0) + (b : ℂ) * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- `∂_s F` and `∂_t F` as partial derivatives. -/
lemma deriv_frameA_u {u v : ℝ} (h0 : (u, v) ∈ ZnzSet) :
    deriv (fun s => frameA s v) u = fderiv ℝ FΦ (u, v) (1, 0) :=
  (Bundle.vec_hasDerivAt_u ((contDiffAt_FΦ h0).differentiableAt (by simp))).deriv

lemma deriv_frameA_v {u v : ℝ} (h0 : (u, v) ∈ ZnzSet) :
    deriv (fun t => frameA u t) v = fderiv ℝ FΦ (u, v) (0, 1) :=
  (Bundle.vec_hasDerivAt_v ((contDiffAt_FΦ h0).differentiableAt (by simp))).deriv

/-! ### The charts -/

/-- **Local → global chart**: the point with `𝒜⁺`-frame coordinate `w` over `(s, t)` has
`Zunit`-frame coordinate `F(s, t) w`. -/
def chartA (X : E4) : E4 := mk (frameA (X 2) (X 3) * wL X) (X 2) (X 3)

/-- **Global → local chart**: `w = conj(F) w_Z` (`Bundle.frameA_coord`). -/
def chartInv (X : E4) : E4 := mk (conj (frameA (X 2) (X 3)) * wL X) (X 2) (X 3)

/-- The band `{(x, y, u, v) : u ∈ 𝒜⁺}`. -/
def bandE : Set E4 := {X | X 2 ∈ annulusPlus}

lemma isOpen_bandE : IsOpen bandE := isOpen_Ioo.preimage (dc 2).continuous

lemma band_Znz {X : E4} (hX : X ∈ bandE) : (X 2, X 3) ∈ ZnzSet :=
  Bundle.Zunit_zero_ne_zero_of_mem hX (X 3)

lemma annulus_subset_annulusPlus : annulus ⊆ annulusPlus := fun u hu =>
  ⟨by linarith [hu.1], by linarith [hu.2]⟩

@[simp] lemma chartA_apply2 (X : E4) : chartA X 2 = X 2 := by simp [chartA]
@[simp] lemma chartA_apply3 (X : E4) : chartA X 3 = X 3 := by simp [chartA]
@[simp] lemma chartInv_apply2 (X : E4) : chartInv X 2 = X 2 := by simp [chartInv]
@[simp] lemma chartInv_apply3 (X : E4) : chartInv X 3 = X 3 := by simp [chartInv]

lemma norm_frameA_of {X : E4} (hX : X ∈ bandE) : ‖frameA (X 2) (X 3)‖ = 1 :=
  norm_FΦ (x := (X 2, X 3)) (band_Znz hX)

lemma conj_mul_frame {X : E4} (hX : X ∈ bandE) :
    conj (frameA (X 2) (X 3)) * frameA (X 2) (X 3) = 1 :=
  Bundle.conj_mul_self_of_norm_one (norm_frameA_of hX)

lemma chartInv_chartA {X : E4} (hX : X ∈ bandE) : chartInv (chartA X) = X := by
  conv_rhs => rw [← mk_wL X]
  simp only [chartInv, chartA, wL_mk, mk_apply2, mk_apply3]
  rw [← mul_assoc, conj_mul_frame hX, one_mul]

lemma chartA_chartInv {X : E4} (hX : X ∈ bandE) : chartA (chartInv X) = X := by
  conv_rhs => rw [← mk_wL X]
  simp only [chartA, chartInv, wL_mk, mk_apply2, mk_apply3]
  rw [← mul_assoc, mul_comm (frameA _ _), conj_mul_frame hX, one_mul]

lemma pE_chartA {X : E4} (hX : X ∈ bandE) : pE (chartA X) = pE X := by
  rw [chartA, pE_mk, pE_eq, norm_mul, norm_frameA_of hX, one_mul]

lemma pE_chartInv {X : E4} (hX : X ∈ bandE) : pE (chartInv X) = pE X := by
  rw [chartInv, pE_mk, pE_eq, norm_mul, Complex.norm_conj, norm_frameA_of hX, one_mul]

lemma chartA_mem_band {X : E4} (hX : X ∈ bandE) : chartA X ∈ bandE := by
  simpa [bandE] using hX

lemma chartInv_mem_band {X : E4} (hX : X ∈ bandE) : chartInv X ∈ bandE := by
  simpa [bandE] using hX

lemma contDiffAt_chartA {X : E4} (hX : X ∈ bandE) : ContDiffAt ℝ ∞ chartA X := by
  have hb : ContDiffAt ℝ ∞ (fun Y : E4 => FΦ (Y 2, Y 3)) X :=
    (contDiffAt_FΦ (band_Znz hX)).comp X ((dc 2).contDiff.prodMk (dc 3).contDiff).contDiffAt
  have h : ContDiffAt ℝ ∞ (fun Y : E4 => mkL (FΦ (Y 2, Y 3) * wL Y, Y 2, Y 3)) X :=
    mkL.contDiff.contDiffAt.comp X ((hb.mul wL.contDiff.contDiffAt).prodMk
      ((dc 2).contDiff.contDiffAt.prodMk (dc 3).contDiff.contDiffAt))
  exact h

lemma contDiffAt_chartInv {X : E4} (hX : X ∈ bandE) : ContDiffAt ℝ ∞ chartInv X := by
  have hb : ContDiffAt ℝ ∞ (fun Y : E4 => FΦ (Y 2, Y 3)) X :=
    (contDiffAt_FΦ (band_Znz hX)).comp X ((dc 2).contDiff.prodMk (dc 3).contDiff).contDiffAt
  have hc : ContDiffAt ℝ ∞ (fun Y : E4 => conj (FΦ (Y 2, Y 3))) X :=
    (Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt).comp X hb
  have h : ContDiffAt ℝ ∞ (fun Y : E4 => mkL (conj (FΦ (Y 2, Y 3)) * wL Y, Y 2, Y 3)) X :=
    mkL.contDiff.contDiffAt.comp X ((hc.mul wL.contDiff.contDiffAt).prodMk
      ((dc 2).contDiff.contDiffAt.prodMk (dc 3).contDiff.contDiffAt))
  exact h

/-- The derivative of the chart: `D chartA (a, v₂, v₃) = (F a + w DF(v₂, v₃), v₂, v₃)`. -/
theorem fderiv_chartA_apply {X : E4} (hX : X ∈ bandE) (v : E4) :
    fderiv ℝ chartA X v = mk (frameA (X 2) (X 3) * wL v +
      wL X * fderiv ℝ FΦ (X 2, X 3) (v 2, v 3)) (v 2) (v 3) := by
  have hF : HasFDerivAt FΦ (fderiv ℝ FΦ (X 2, X 3)) (X 2, X 3) :=
    ((contDiffAt_FΦ (band_Znz hX)).differentiableAt (by simp)).hasFDerivAt
  have hb := hF.comp X ((dc 2).prod (dc 3)).hasFDerivAt
  have hm := hb.mul wL.hasFDerivAt
  have hall : HasFDerivAt chartA _ X :=
    mkL.hasFDerivAt.comp X (hm.prodMk ((dc 2).hasFDerivAt.prodMk (dc 3).hasFDerivAt))
  rw [hall.fderiv]
  simp only [comp_apply, prod_apply, add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  simp only [mk, FΦ, dc_apply]

/-! ### Algebra of split forms under the rotation -/

lemma splitForm_mk (p1 p2 g1 g2 k : ℝ) (A B : ℂ) (v2 v3 w2 w3 : ℝ) :
    splitForm p1 p2 g1 g2 k (mk A v2 v3) (mk B w2 w3) =
      omega2 A B + k * (v2 * w3 - w2 * v3) + (p1 * A.re + p2 * A.im) * (g1 * w2 + g2 * w3) -
        (p1 * B.re + p2 * B.im) * (g1 * v2 + g2 * v3) := by
  simp only [splitForm, add_apply, smul_apply, wedge_apply, smul_eq_mul, dc_apply, mk_apply0,
    mk_apply1, mk_apply2, mk_apply3, omega2]
  ring

/-- A unit fibre rotation does not change a split form with `dp = 2π(x dx + y dy)`. -/
lemma splitForm_rot {F : ℂ} (hF : ‖F‖ = 1) (w A B : ℂ) (g1 g2 k v2 v3 w2 w3 : ℝ) :
    splitForm (2 * π * (F * w).re) (2 * π * (F * w).im) g1 g2 k (mk (F * A) v2 v3)
        (mk (F * B) w2 w3) =
      splitForm (2 * π * w.re) (2 * π * w.im) g1 g2 k (mk A v2 v3) (mk B w2 w3) := by
  have hcd := normSq_one hF
  rw [splitForm_mk, splitForm_mk]
  simp only [omega2, Complex.mul_re, Complex.mul_im]
  linear_combination ((A.re * B.im - A.im * B.re) +
    2 * π * (w.re * A.re + w.im * A.im) * (g1 * w2 + g2 * w3) -
    2 * π * (w.re * B.re + w.im * B.im) * (g1 * v2 + g2 * v3)) * hcd

/-- An infinitesimal fibre rotation by `dφ = m₁ ds + m₂ dt` changes the angular coefficients of a
split form by `dφ/2π`. -/
lemma splitForm_twist (w a b : ℂ) (g1 g2 k m1 m2 v2 v3 w2 w3 : ℝ) :
    splitForm (2 * π * w.re) (2 * π * w.im) g1 g2 k
        (mk (a + Complex.I * ((v2 * m1 + v3 * m2 : ℝ) : ℂ) * w) v2 v3)
        (mk (b + Complex.I * ((w2 * m1 + w3 * m2 : ℝ) : ℂ) * w) w2 w3) =
      splitForm (2 * π * w.re) (2 * π * w.im) (g1 + m1 / (2 * π)) (g2 + m2 / (2 * π)) k
        (mk a v2 v3) (mk b w2 w3) := by
  rw [splitForm_mk, splitForm_mk]
  simp only [omega2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-! ### Transfer of `Ω_t` to the `𝒜⁺`-frame -/

end SymplecticPacking.Handle
