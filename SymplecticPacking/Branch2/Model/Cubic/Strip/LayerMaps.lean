import SymplecticPacking.Strip.LayerMaps
import SymplecticPacking.Branch2.Model.Cubic.Strip.Layer

/-!
# The fibre shear and the layer maps

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Strip.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:str-layer-maps` (`prop:shd4-maps`, `cons:str-layer-map`):
the fibre shear and the layer maps `E_i`.

Source coordinates. The source `ℂ² ∋ (z_b, z_f)` is `E4` with `z_b = q₁ + i p₁ = zbL X`
(`X 0 + i X 2`) and `z_f = q₂ + i p₂ = zfL X` (`X 1 + i X 3`), so that
`ω_std = ω_ℂ(z_b) + ω_ℂ(z_f)` is `omega0` (`omega0_eq`). The target is the handle's local
`𝒜⁺`-frame coordinates `(w, s, v)` (`Handle/Twist.lean`).

* `shear P i T z = exp(−2πi T a_i'(π|z|²)) z` and `shearE P i : (w, x, T) ↦ (Σ_{i,T}(w), x, T)`;
  `shear_pullback`: `shearE^*(ω_V + dx ∧ dT + da_i ∧ dT) = ω_V + dx ∧ dT` (everywhere).
* `srcMap P : (z_b, z_f) ↦ (z_f, x, T)` with `x + iT = Ψ_strip(z_b)`, `δ = δ_strip`;
  `srcMap_pullback`: `srcMap^*(ω_V + dx ∧ dT) = ω_std`.
* `layerMap P i (z_b, z_f) = (σ_i(x, T, p), v(T), Σ_{i,T}(z_f))` (`cons:str-layer-map`);
  `layerMap_eq`: `layerMap = layerChart ∘ shearE ∘ srcMap`.
* `prop:shd4-maps`: `layerMap_smooth`, `layerMap_symplectic` (`E_i^* Ω_pre = ω_std`),
  `layerMap_injective`, `layerMap_disjoint`, `layerMap_mem`, all on the open ball
  `srcBall P = 𝔹_{ρ̂}` (`= ball 0 √(ρ̂/π)`, `srcBall_eq_ball`).
-/

noncomputable section

namespace SymplecticPacking.Strip.Cubic

open Set Filter Topology ContinuousLinearMap ComplexConjugate
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE bB annulus u0 u1)
open SymplecticPacking.Handle (mk mkL wL omegaV)
open SymplecticPacking.Handle.Cubic (aLayer rhoLayer layerLeft layerRight OmegaPre)
open SymplecticPacking.Qhat (omega2)
open scoped ContDiff Real

/-! ### Complex helpers -/

variable (P : Branch2.VCubic)

lemma contDiff_deriv_aLayer (i : ℕ) : ContDiff ℝ ∞ (deriv (aLayer P i)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_aLayer P i)).2

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

theorem shearInv_shear (i : ℕ) (T : ℝ) (z : ℂ) : shearInv P i T (shear P i T z) = z := by
  rw [shearInv, norm_shear, shear, ← mul_assoc, ← Complex.exp_add]
  push_cast; ring_nf; simp

theorem shear_injective (i : ℕ) (T : ℝ) : Function.Injective (shear P i T) := fun a b h => by
  rw [← shearInv_shear P i T a, h, shearInv_shear]

theorem contDiff_shear_joint (i : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℂ => shear P i q.1 q.2) := by
  unfold shear
  have hp : ContDiff ℝ ∞ (fun q : ℝ × ℂ => π * ‖q.2‖ ^ 2) :=
    Handle.contDiff_fibreArea.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : ℝ × ℂ => -(2 * π) * (q.1 * deriv (aLayer P i) (π * ‖q.2‖ ^ 2))) :=
    contDiff_const.mul (contDiff_fst.mul ((contDiff_deriv_aLayer P i).comp hp))
  exact ((Complex.ofRealCLM.contDiff.comp hθ).mul contDiff_const).cexp.mul contDiff_snd

/-- **The shear on `E4`** `(w, x, T) ↦ (Σ_{i,T}(w), x, T)`. -/
def shearE (i : ℕ) (Y : E4) : E4 := mk (shear P i (Y 3) (wL Y)) (Y 2) (Y 3)

/-- The rotation angle `θ = −2π T a_i'(p)` on `E4`. -/
def thetaE (i : ℕ) (Y : E4) : ℝ := -(2 * π) * (Y 3 * deriv (aLayer P i) (pE Y))

lemma shearE_eq (i : ℕ) : shearE P i = fun Y =>
    mkL (Complex.exp ((thetaE P i Y : ℂ) * Complex.I) * wL Y, Y 2, Y 3) := by
  funext Y; simp [shearE, shear, thetaE, Handle.pE_eq, Handle.mk]

@[simp] lemma pE_shearE (i : ℕ) (Y : E4) : pE (shearE P i Y) = pE Y := by
  rw [shearE, Handle.pE_mk, norm_shear, Handle.pE_eq]

@[simp] lemma shearE_apply2 (i : ℕ) (Y : E4) : shearE P i Y 2 = Y 2 := by simp [shearE]
@[simp] lemma shearE_apply3 (i : ℕ) (Y : E4) : shearE P i Y 3 = Y 3 := by simp [shearE]

theorem contDiff_shearE (i : ℕ) : ContDiff ℝ ∞ (shearE P i) := by
  have h : ContDiff ℝ ∞ (fun Y : E4 => mkL (shear P i (Y 3) (wL Y), Y 2, Y 3)) :=
    mkL.contDiff.comp (((contDiff_shear_joint P i).comp ((dc 3).contDiff.prodMk wL.contDiff)).prodMk
      ((dc 2).contDiff.prodMk (dc 3).contDiff))
  exact h

/-- The derivative of `θ`. -/
def dthetaE (i : ℕ) (Y v : E4) : ℝ :=
  -(2 * π) * (deriv (aLayer P i) (pE Y) * v 3 + Y 3 * (deriv (deriv (aLayer P i)) (pE Y) * dpE Y v))

theorem fderiv_shearE_apply (i : ℕ) (Y v : E4) :
    fderiv ℝ (shearE P i) Y v =
      mk (Complex.exp ((thetaE P i Y : ℂ) * Complex.I) *
        (wL v + (dthetaE P i Y v : ℂ) * Complex.I * wL Y)) (v 2) (v 3) := by
  have hA := hasFDerivAt_compP (X := Y) (hasDerivAt_of_contDiff (contDiff_deriv_aLayer P i) (pE Y))
  have hθ : HasFDerivAt (thetaE P i) _ Y := ((dc 3).hasFDerivAt.mul hA).const_mul (-(2 * π))
  have hθC := (Complex.ofRealCLM.hasFDerivAt (x := thetaE P i Y)).comp Y hθ
  have hR := (hθC.mul_const Complex.I).cexp
  have hm := hR.mul wL.hasFDerivAt
  have hall := mkL.hasFDerivAt.comp Y (hm.prodMk ((dc 2).hasFDerivAt.prodMk (dc 3).hasFDerivAt))
  rw [shearE_eq, show (fun Y => mkL (Complex.exp ((thetaE P i Y : ℂ) * Complex.I) * wL Y, Y 2, Y 3))
    = mkL ∘ fun Y => (((fun Y => Complex.exp ((Complex.ofRealCLM ∘ thetaE P i) Y * Complex.I)) *
      ⇑wL) Y, dc 2 Y, dc 3 Y) from rfl, hall.fderiv]
  simp only [comp_apply, prod_apply, add_apply, smul_apply, smul_eq_mul, Handle.dc_apply,
    Handle.mk, Function.comp_apply, Pi.mul_apply, Complex.ofRealCLM_apply, dthetaE]
  congr 1
  simp only [Prod.mk.injEq, and_true]
  push_cast
  ring

/-- **`prop:shd4-maps`.** `Σ_i^*(ω_V + dx ∧ dT + da_i ∧ dT) = ω_ℂ(z) + dx ∧ dT`. -/
theorem shear_pullback (i : ℕ) (Y : E4) :
    pull2 (shearE P i) (OmegaLayer P i) Y = OmegaFlat Y := by
  set R := Complex.exp ((thetaE P i Y : ℂ) * Complex.I)
  have hR : conj R * R = 1 := conj_exp_mul _
  have hdp : ∀ v, dpE (shearE P i Y) (fderiv ℝ (shearE P i) Y v) = dpE Y v := by
    intro v
    rw [dpE_eq_re, dpE_eq_re, fderiv_shearE_apply, Handle.wL_mk,
      show wL (shearE P i Y) = R * wL Y by
        simp only [shearE, Handle.wL_mk, shear, R, thetaE, Handle.pE_eq]]
    rw [map_mul, show conj R * conj (wL Y) * (R * (wL v + (dthetaE P i Y v : ℂ) * Complex.I * wL Y))
      = (conj R * R) * (conj (wL Y) * wL v + (dthetaE P i Y v : ℂ) * Complex.I *
        (conj (wL Y) * wL Y)) by ring, hR, one_mul, Complex.conj_mul']
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hω : ∀ v w, omega2 (wL (fderiv ℝ (shearE P i) Y v)) (wL (fderiv ℝ (shearE P i) Y w)) =
      omega2 (wL v) (wL w) + deriv (aLayer P i) (pE Y) * (v 3 * dpE Y w - w 3 * dpE Y v) := by
    intro v w
    rw [fderiv_shearE_apply, fderiv_shearE_apply, Handle.wL_mk, Handle.wL_mk, omega2_rot hR]
    simp only [omega2, dthetaE, dpE, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Handle.wL_re, Handle.wL_im, add_apply, smul_apply, smul_eq_mul, Handle.dc_apply]
    ring
  ext v w
  simp only [Forms.pull2_apply, OmegaLayer, OmegaFlat, add_apply, wedge_apply, smul_apply,
    smul_eq_mul, Handle.omegaV_apply, hω, hdp, pE_shearE, Handle.dc_apply]
  rw [fderiv_shearE_apply, fderiv_shearE_apply]
  simp only [Handle.mk_apply2, Handle.mk_apply3]
  ring

/-! ### Source coordinates and the strip map -/

/-- **The source ball** `𝔹_{ρ̂_i} = {π|z_b|² + π|z_f|² < ρ̂_i}`. -/
def srcBall (i : ℕ) : Set E4 := {X | π * ‖zbL X‖ ^ 2 + π * ‖zfL X‖ ^ 2 < P.rhoHat i}

theorem srcBall_eq_ball (i : ℕ) : srcBall P i = Metric.ball 0 (Real.sqrt (P.rhoHat i / π)) := by
  ext X
  rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg _), norm_sq_E4, srcBall,
    mem_setOf_eq, lt_div_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith

theorem isOpen_srcBall (i : ℕ) : IsOpen (srcBall P i) := by
  rw [srcBall_eq_ball]; exact Metric.isOpen_ball

/-- `(z_b, z_f) ↦ (z_f, x, T)` with `x + iT = Ψ_strip(z_b)`, `δ = δ_i`. -/
def srcMap (i : ℕ) (X : E4) : E4 :=
  mk (zfL X) (psiStrip (P.deltaStrip i) (zbL X)).re (psiStrip (P.deltaStrip i) (zbL X)).im

lemma psi_hasFDerivAt {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (z : ℂ) :
    HasFDerivAt (psiStrip (P.deltaStrip i)) (fderiv ℝ (psiStrip (P.deltaStrip i)) z) z :=
  ((psiStrip_smooth (P.deltaStrip_pos hi1 hik)).differentiable (by simp) z).hasFDerivAt

theorem contDiff_srcMap {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) : ContDiff ℝ ∞ (srcMap P i) := by
  have hψ := (psiStrip_smooth (P.deltaStrip_pos hi1 hik)).comp zbL.contDiff
  have h : ContDiff ℝ ∞ (fun X : E4 => mkL (zfL X,
      Complex.reCLM (psiStrip (P.deltaStrip i) (zbL X)),
      Complex.imCLM (psiStrip (P.deltaStrip i) (zbL X)))) :=
    mkL.contDiff.comp (zfL.contDiff.prodMk ((Complex.reCLM.contDiff.comp hψ).prodMk
      (Complex.imCLM.contDiff.comp hψ)))
  exact h

theorem fderiv_srcMap_apply {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (X v : E4) :
    fderiv ℝ (srcMap P i) X v = mk (zfL v)
      (fderiv ℝ (psiStrip (P.deltaStrip i)) (zbL X) (zbL v)).re
      (fderiv ℝ (psiStrip (P.deltaStrip i)) (zbL X) (zbL v)).im := by
  have hψ := (psi_hasFDerivAt P hi1 hik (zbL X)).comp X zbL.hasFDerivAt
  have hall := mkL.hasFDerivAt.comp X (zfL.hasFDerivAt.prodMk
    ((Complex.reCLM.hasFDerivAt.comp X hψ).prodMk (Complex.imCLM.hasFDerivAt.comp X hψ)))
  rw [show srcMap P i = mkL ∘ fun X => (zfL X,
    (Complex.reCLM ∘ (psiStrip (P.deltaStrip i) ∘ zbL)) X,
    (Complex.imCLM ∘ (psiStrip (P.deltaStrip i) ∘ zbL)) X) from rfl, hall.fderiv]
  simp [Handle.mk]

/-- **The flat form** `ω_ℂ(w) + dx ∧ dT`. -/
theorem srcMap_pullback {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (X v w : E4) :
    pull2 (srcMap P i) OmegaFlat X v w = omega0 v w := by
  have hdet := (psiStrip_normalize (P.deltaStrip_pos hi1 hik)).2.1 (zbL X)
  have hm := Qhat.omega2_map (fderiv ℝ (psiStrip (P.deltaStrip i)) (zbL X)) (zbL v) (zbL w)
  rw [hdet, one_mul] at hm
  rw [omega0_eq, ← hm]
  simp only [Forms.pull2_apply, OmegaFlat, add_apply, wedge_apply, Handle.omegaV_apply,
    fderiv_srcMap_apply P hi1 hik, Handle.wL_mk, Handle.mk_apply2, Handle.mk_apply3,
    Handle.dc_apply]
  simp only [omega2]; ring

/-! ### The layer maps (`cons:str-layer-map`) -/

/-- **The layer map** `E_i(z_b, z_f) = (s = σ_i(x, T, p), v = v(T), Σ_{i,T}(z_f))` with
`(x, T) = Ψ_strip(z_b)` (`δ = δ_i`), `p = π|z_f|²` (the fibre point in the unitary frame of
`𝒜⁺`). -/
def layerMap (i : ℕ) (X : E4) : E4 :=
  mk (shear P i (psiStrip (P.deltaStrip i) (zbL X)).im (zfL X))
    (layerRoot P i (psiStrip (P.deltaStrip i) (zbL X)).re (psiStrip (P.deltaStrip i) (zbL X)).im
      (π * ‖zfL X‖ ^ 2))
    (vOfT (psiStrip (P.deltaStrip i) (zbL X)).im)

/-- `E_i = (layer coordinates)⁻¹ ∘ Σ_i ∘ (Ψ_strip × id)`. -/
theorem layerMap_eq (i : ℕ) : layerMap P i = layerChart P i ∘ shearE P i ∘ srcMap P i := by
  funext X
  simp [layerMap, layerChart, shearE, srcMap, Handle.pE_mk, norm_shear]

theorem shearE_srcMap_mem {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    shearE P i (srcMap P i X) ∈ layerTarget P i := by
  have hδ := P.deltaStrip_pos hi1 hik
  obtain ⟨hx, hT0, hT1⟩ := psiStrip_mem hδ (zbL X)
  have hb := (x_lt_hi P hi1 hik (zbL X) (zfL X)).2 hX
  have hp : pE (shearE P i (srcMap P i X)) = π * ‖zfL X‖ ^ 2 := by
    rw [pE_shearE, srcMap, Handle.pE_mk]
  refine ⟨?_, ?_, ?_⟩
  · simpa [srcMap] using hx
  · rw [hp]; simp only [shearE_apply2, srcMap, Handle.mk_apply2]; linarith [hb.1, hb.2.1]
  · simpa [srcMap] using (⟨hT0, hT1⟩ : _ ∈ Ioo (0 : ℝ) 1)

/-- **`prop:shd4-maps`, smoothness** on the open ball `𝔹_{ρ̂_i}`. -/
theorem layerMap_smooth {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    ContDiffAt ℝ ∞ (layerMap P i) X := by
  rw [layerMap_eq]
  exact (layerChart_smooth P i (shearE_srcMap_mem P hi1 hik hX)).comp X
    ((contDiff_shearE P i).comp (contDiff_srcMap P hi1 hik)).contDiffAt

/-- **`prop:shd4-maps`, `E_i^* Ω_pre = ω_std`** on `𝔹_{ρ̂_i}`. -/
theorem layerMap_symplectic {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4}
    (hX : X ∈ srcBall P i) (v w : E4) : pull2 (layerMap P i) (OmegaPre P) X v w = omega0 v w := by
  set Z := shearE P i (srcMap P i X) with hZdef
  have hZ := shearE_srcMap_mem P hi1 hik hX
  have hKd : DifferentiableAt ℝ (layerChart P i) Z :=
    (layerChart_smooth P i hZ).differentiableAt (by simp)
  have hSQ : DifferentiableAt ℝ (shearE P i ∘ srcMap P i) X :=
    ((contDiff_shearE P i).comp (contDiff_srcMap P hi1 hik)).differentiable (by simp) X
  have hm := layerChart_mem P i hZ
  have hLd : DifferentiableAt ℝ (layerCoord P i) (layerChart P i Z) :=
    (contDiffAt_layerCoord P i hm.2).differentiableAt (by simp)
  have h1 : pull2 (layerChart P i) (OmegaPre P) Z = OmegaLayer P i Z := by
    rw [pull2_congr_pt (layer_form P hi1 hik hm), ← Forms.pull2_comp_apply hKd hLd]
    have hev : layerCoord P i ∘ layerChart P i =ᶠ[𝓝 Z] id :=
      layerCoord_layerChart_eventually P i hZ
    have hcc : (layerCoord P i ∘ layerChart P i) Z = Z := layerCoord_layerChart P i hZ
    ext a b
    rw [Forms.pull2_apply, hev.fderiv_eq, fderiv_id, hcc]
    rfl
  rw [layerMap_eq, Forms.pull2_comp_apply hSQ hKd,
    pull2_congr_pt (φ := shearE P i ∘ srcMap P i) (Ω' := OmegaLayer P i) h1,
    Forms.pull2_comp_apply ((contDiff_srcMap P hi1 hik).differentiable (by simp) X)
      ((contDiff_shearE P i).differentiable (by simp) _),
    pull2_congr_pt (φ := srcMap P i) (Ω' := OmegaFlat) (shear_pullback P i _),
    srcMap_pullback P hi1 hik]

/-- `E_i` lands in `Λ_i`, and in `{p < a_i}`. -/
theorem layerMap_mem {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    layerMap P i X ∈ layerSet P i ∧ pE (layerMap P i X) < P.a i := by
  have hZ := shearE_srcMap_mem P hi1 hik hX
  have hb := (x_lt_hi P hi1 hik (zbL X) (zfL X)).2 hX
  have hp : pE (layerMap P i X) = π * ‖zfL X‖ ^ 2 := by
    rw [layerMap_eq, Function.comp_apply, Function.comp_apply, pE_layerChart, pE_shearE, srcMap,
      Handle.pE_mk]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [layerMap_eq]; exact layerChart_mem P i hZ
  · show pE (layerMap P i X) < P.h; rw [hp]; linarith [hb.2.2.1, hb.2.2.2]
  · rw [hp]; exact hb.2.2.1

theorem layer_subset_annulus {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) :
    Ioo (layerLeft P i) (layerRight P i) ⊆ annulus := by
  intro s hs
  have h1 := Handle.Cubic.u0_lt_layerLeft_one P
  have h2 := Handle.Cubic.layerLeft_mono P hi1
  have h3 := Handle.Cubic.layerRight_mono P
    (show i ≤ Handle.Cubic.Nlayers P by unfold Handle.Cubic.Nlayers; omega)
  have h4 := Handle.Cubic.layerRight_N_lt_u1 P
  have h5 : (1 : ℝ) / 8 < u0 := by norm_num [u0]
  have h6 : u1 < (5 : ℝ) / 24 := by norm_num [u1]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- **`prop:shd4-maps`, base region**: `E_i(𝔹_{ρ̂_i})` lies over `I_i × (1/8, 5/24) ⊂ 𝒜`. -/
theorem layerMap_mem_annulus {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4}
    (hX : X ∈ srcBall P i) : layerMap P i X 2 ∈ annulus :=
  layer_subset_annulus P hi1 hik (layerMap_mem P hi1 hik hX).1.1.1

/-- **`prop:shd4-maps`, injectivity** on `𝔹_{ρ̂_i}` (inverse: `layerCoord`, `Σ⁻¹`,
`Ψ⁻¹`). -/
theorem layerMap_injective {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) :
    InjOn (layerMap P i) (srcBall P i) := by
  intro X hX X' hX' h
  rw [layerMap_eq] at h
  have hZ := congrArg (layerCoord P i) h
  simp only [Function.comp_apply] at hZ
  rw [layerCoord_layerChart P i (shearE_srcMap_mem P hi1 hik hX),
    layerCoord_layerChart P i (shearE_srcMap_mem P hi1 hik hX')] at hZ
  have h2 := congrArg (fun Z : E4 => Z 2) hZ
  have h3 := congrArg (fun Z : E4 => Z 3) hZ
  have hw := congrArg wL hZ
  simp only [shearE, srcMap, Handle.mk_apply2, Handle.mk_apply3, Handle.wL_mk] at h2 h3 hw
  rw [h3] at hw
  have hf := shear_injective P i _ hw
  have hψ : psiStrip (P.deltaStrip i) (zbL X) = psiStrip (P.deltaStrip i) (zbL X') :=
    Complex.ext h2 h3
  have hb := (psiStrip_bijOn (P.deltaStrip_pos hi1 hik)).injOn (mem_univ _) (mem_univ _) hψ
  exact E4_ext_zb_zf hb hf

/-- **`prop:shd4-maps`, disjointness**: the images of different layer maps are disjoint
(their base coordinates `s` lie in the disjoint intervals `I_i`). -/
theorem layerMap_disjoint {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (hj1 : 1 ≤ j) (hjk : j ≤ P.k)
    (hij : i ≠ j) :
    Disjoint (layerMap P i '' srcBall P i) (layerMap P j '' srcBall P j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨X, hX, rfl⟩ ⟨X', hX', h⟩
  have hi := (layerMap_mem P hi1 hik hX).1.1.1
  have hj := (layerMap_mem P hj1 hjk hX').1.1.1
  rw [h] at hj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have := Handle.Cubic.layerRight_lt_left P hlt; linarith [hi.2, hj.1]
  · have := Handle.Cubic.layerRight_lt_left P hlt; linarith [hi.1, hj.2]

end SymplecticPacking.Strip.Cubic
