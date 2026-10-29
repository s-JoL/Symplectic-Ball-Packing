import SymplecticPacking.Branch2.Planar.UVWells
import SymplecticPacking.Branch2.Planar.Alexander

/-!
# The planar Morse pair, the endpoint map and its comparison estimate

For a planar input `D`:

* `morse D` is the Morse pair `X = X_U + ζ`, `Y = X_V + ζ` built from the two wells
  (`UVWells.lean`); the proper extension `ζ` vanishes on `|u| ≤ u₁`, where `u₁² ≥ Ē` bounds all
  energies that occur;
* the inner map `f = F_mor ∘ T⁻¹ ∘ D` (`MorsePair.lean`) sends `D̄(I)` into the sublevel set
  `{R + W ≤ E(I)}`, and (via the area estimate (F) of `Potential.lean`) `E(I) < b - m* + 2δ`
  with `b = R F(I + 3η) + 2σ`; on that sublevel set `R = f̃_U ≈ U - m*`, `W = f̃_V ≈ V`, so
  `F(p* + Re f(z)) < R F(π|z|²) + e`;
* the endpoint `Φ = C ∘ f` (`C` the area-preserving polar chart around `p*`, made globally smooth
  by a cutoff below the relevant region) feeds the Alexander family and the five-segment path.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Filter Topology Set MeasureTheory Complex
open scoped ContDiff Real

open Inner (invR Einv)

/-! ### The proper extension `ζ` -/

/-- `φ(x) = x S(x)`. -/
def phiS (x : ℝ) : ℝ := x * Real.smoothTransition x

/-- `ζ(u) = φ(u - u₁) - φ(-u - u₁)`: zero on `|u| ≤ u₁`, nondecreasing, `ζ(u) = u ∓ u₁` far out. -/
def zeta (u₁ u : ℝ) : ℝ := phiS (u - u₁) - phiS (-u - u₁)

lemma phiS_contDiff : ContDiff ℝ ∞ phiS := contDiff_id.mul Real.smoothTransition.contDiff

lemma phiS_eq_zero {x : ℝ} (hx : x ≤ 0) : phiS x = 0 := by
  simp [phiS, Real.smoothTransition.zero_of_nonpos hx]

lemma phiS_eq {x : ℝ} (hx : 1 ≤ x) : phiS x = x := by
  simp [phiS, Real.smoothTransition.one_of_one_le hx]

lemma phiS_nonneg (x : ℝ) : 0 ≤ phiS x := by
  rcases le_or_gt x 0 with h | h
  · rw [phiS_eq_zero h]
  · exact mul_nonneg h.le (Real.smoothTransition.nonneg _)

lemma phiS_mono : Monotone phiS := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · rw [phiS_eq_zero hx]; exact phiS_nonneg y
  · exact mul_le_mul hxy (Real.smoothTransition.monotone hxy)
      (Real.smoothTransition.nonneg _) (by linarith)

lemma zeta_contDiff (u₁ : ℝ) : ContDiff ℝ ∞ (zeta u₁) :=
  (phiS_contDiff.comp (contDiff_id.sub contDiff_const)).sub
    (phiS_contDiff.comp (contDiff_id.neg.sub contDiff_const))

lemma zeta_mono (u₁ : ℝ) : Monotone (zeta u₁) := by
  intro u v huv
  have h1 := phiS_mono (show u - u₁ ≤ v - u₁ by linarith)
  have h2 := phiS_mono (show -v - u₁ ≤ -u - u₁ by linarith)
  unfold zeta; linarith

lemma zeta_eq_zero {u₁ u : ℝ} (hu : |u| ≤ u₁) : zeta u₁ u = 0 := by
  rw [abs_le] at hu
  unfold zeta
  rw [phiS_eq_zero (by linarith), phiS_eq_zero (by linarith), sub_zero]

lemma zeta_ge {u₁ u : ℝ} (hu₁ : 0 ≤ u₁) (hu : u₁ + 1 ≤ u) : u - u₁ ≤ zeta u₁ u := by
  unfold zeta
  rw [phiS_eq (by linarith), phiS_eq_zero (by linarith), sub_zero]

lemma zeta_le {u₁ u : ℝ} (hu₁ : 0 ≤ u₁) (hu : u ≤ -u₁ - 1) : zeta u₁ u ≤ u + u₁ := by
  unfold zeta
  rw [phiS_eq_zero (by linarith), phiS_eq (by linarith)]; linarith

lemma deriv_zeta_nonneg (u₁ u : ℝ) : 0 ≤ deriv (zeta u₁) u := (zeta_mono u₁).deriv_nonneg

/-! ### The polar chart -/

/-- The area-preserving polar chart `C(x, y) = -√((p + x)/π) e^{2πiy}` around `p`. -/
def chart (p : ℝ) (w : ℂ) : ℂ :=
  -((√((p + w.re) / π) : ℝ) * Complex.exp ((2 * π * w.im : ℝ) * I))

/-- The cutoff radius function `s(P) = P S((P-a)/a) + (a/2)(1 - S((P-a)/a))`. -/
def sfunP (a P : ℝ) : ℝ :=
  P * Real.smoothTransition ((P - a) / a) + a / 2 * (1 - Real.smoothTransition ((P - a) / a))

/-- The globally smooth chart `C_s(x, y) = -√(s(p + x)/π) e^{2πiy}`. -/
def chartS (p a : ℝ) (w : ℂ) : ℂ :=
  -((√(sfunP a (p + w.re) / π) : ℝ) * Complex.exp ((2 * π * w.im : ℝ) * I))

lemma sfunP_eq {a P : ℝ} (ha : 0 < a) (hP : 2 * a ≤ P) : sfunP a P = P := by
  have : Real.smoothTransition ((P - a) / a) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ ha]; linarith)
  simp [sfunP, this]

lemma sfunP_pos {a : ℝ} (ha : 0 < a) (P : ℝ) : 0 < sfunP a P := by
  unfold sfunP
  have hS0 := Real.smoothTransition.nonneg ((P - a) / a)
  have hS1 := Real.smoothTransition.le_one ((P - a) / a)
  rcases le_or_gt P a with h | h
  · rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)]
    linarith
  · rcases eq_or_lt_of_le hS0 with h0 | h0
    · rw [← h0]; linarith
    · have : 0 < P * Real.smoothTransition ((P - a) / a) := mul_pos (by linarith) h0
      have : 0 ≤ a / 2 * (1 - Real.smoothTransition ((P - a) / a)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith

lemma sfunP_contDiff (a : ℝ) : ContDiff ℝ ∞ (sfunP a) := by
  unfold sfunP
  have hS : ContDiff ℝ ∞ (fun P : ℝ => Real.smoothTransition ((P - a) / a)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  exact (contDiff_id.mul hS).add (contDiff_const.mul (contDiff_const.sub hS))

lemma chartS_contDiff {p a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (chartS p a) := by
  unfold chartS
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => sfunP a (p + w.re) / π) :=
    ((sfunP_contDiff a).comp (contDiff_const.add reCLM.contDiff)).div_const _
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => √(sfunP a (p + w.re) / π)) :=
    h1.sqrt fun w => (div_pos (sfunP_pos ha _) Real.pi_pos).ne'
  have h3 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp ((2 * π * w.im : ℝ) * I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ((ofRealCLM.contDiff.comp
      (contDiff_const.mul imCLM.contDiff)).mul contDiff_const)
  exact ((ofRealCLM.contDiff.comp h2).mul h3).neg

lemma chartS_eq {p a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 * a ≤ p + w.re) :
    chartS p a w = chart p w := by
  simp [chartS, chart, sfunP_eq ha hw]

lemma chartS_eventually {p a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 * a < p + w.re) :
    chartS p a =ᶠ[𝓝 w] chart p := by
  have : {v : ℂ | 2 * a < p + v.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)).mem_nhds hw
  filter_upwards [this] with v hv using chartS_eq ha hv.le

theorem chart_moment {p : ℝ} {w : ℂ} (hw : 0 ≤ p + w.re) : π * ‖chart p w‖ ^ 2 = p + w.re := by
  rw [chart, norm_neg, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg hw Real.pi_pos.le)]
  field_simp

/-- The derivative of the chart. -/
lemma hasFDerivAt_chart {p : ℝ} {w : ℂ} (hw : 0 < p + w.re) :
    HasFDerivAt (chart p)
      (-((((√((p + w.re) / π) : ℝ) : ℂ) • ((Complex.exp (((2 * π * w.im : ℝ) : ℂ) * I)) •
          (ofRealCLM.comp ((2 * π) • imCLM)).smulRight I)) +
        Complex.exp (((2 * π * w.im : ℝ) : ℂ) * I) •
          ofRealCLM.comp ((1 / π / (2 * √((p + w.re) / π))) • reCLM))) w := by
  set q : ℝ → ℝ := fun x => (p + x) / π
  have hq : HasDerivAt q (1 / π) w.re := by
    simpa [q] using ((hasDerivAt_id w.re).const_add p).div_const π
  have hqpos : 0 < q w.re := div_pos hw Real.pi_pos
  have hs : HasDerivAt (fun x => √(q x)) (1 / π / (2 * √(q w.re))) w.re := hq.sqrt hqpos.ne'
  have h1 : HasFDerivAt (fun w : ℂ => ((√(q w.re) : ℝ) : ℂ))
      (ofRealCLM.comp ((1 / π / (2 * √(q w.re))) • reCLM)) w := by
    refine (ofRealCLM.hasFDerivAt.comp w (hs.hasFDerivAt.comp w reCLM.hasFDerivAt)).congr_fderiv ?_
    ext1 z; simp; ring
  have hg : HasFDerivAt (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ) * I)
      ((ofRealCLM.comp ((2 * π) • imCLM)).smulRight I) w := by
    have : HasFDerivAt (fun w : ℂ => ((2 * π * w.im : ℝ) : ℂ))
        (ofRealCLM.comp ((2 * π) • imCLM)) w :=
      (ofRealCLM.hasFDerivAt.comp w (((2 * π) • imCLM).hasFDerivAt)).congr_fderiv
        (by ext1 z; simp)
    refine (this.mul_const I).congr_fderiv ?_
    ext1 z; simp; ring
  have h2 := hg.cexp
  exact (h1.mul h2).neg

theorem chart_det {p : ℝ} {w : ℂ} (hw : 0 < p + w.re) :
    LinearMap.det (fderiv ℝ (chart p) w : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [(hasFDerivAt_chart hw).fderiv, Inner.det_eq_re_im]
  set q := (p + w.re) / π
  have hqpos : 0 < q := div_pos hw Real.pi_pos
  set ρ := √q
  have hρ : 0 < ρ := Real.sqrt_pos.2 hqpos
  set θ := 2 * π * w.im
  have hc := Complex.exp_ofReal_mul_I_re θ
  have hsn := Complex.exp_ofReal_mul_I_im θ
  simp [hc, hsn, -Complex.ofReal_div]
  have hρ2 : ρ * ρ = q := Real.mul_self_sqrt hqpos.le
  have hcs := Real.cos_sq_add_sin_sq θ
  have hpi := Real.pi_pos.ne'
  field_simp
  first | rfl | (rw [hcs, mul_one]) | linarith [hcs]

theorem chart_injOn {p : ℝ} : InjOn (chart p) {w | 0 < p + w.re ∧ |w.im| < 1 / 2} := by
  intro w₁ hw₁ w₂ hw₂ h
  have hm1 := chart_moment (p := p) hw₁.1.le
  have hm2 := chart_moment (p := p) hw₂.1.le
  rw [h] at hm1
  have hre : w₁.re = w₂.re := by linarith
  have hρ : 0 < √((p + w₁.re) / π) := Real.sqrt_pos.2 (div_pos hw₁.1 Real.pi_pos)
  have he : Complex.exp (((2 * π * w₁.im : ℝ) : ℂ) * I) =
      Complex.exp (((2 * π * w₂.im : ℝ) : ℂ) * I) := by
    have h' := h
    simp only [chart, neg_inj, hre] at h'
    rw [← hre] at h'
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne') h'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hn' : w₁.im = w₂.im + n := by
    have := congrArg Complex.im hn
    simp at this
    have hpi := Real.pi_pos
    nlinarith
  have hlt : |(n : ℝ)| < 1 := by
    have h1 := abs_lt.mp hw₁.2
    have h2 := abs_lt.mp hw₂.2
    rw [abs_lt]; constructor <;> linarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hlt
    rw [abs_lt] at this; omega
  rw [hn0, Int.cast_zero, add_zero] at hn'
  exact Complex.ext hre hn'

namespace PlanarInput

variable (D : PlanarInput)

/-! ### Constants and the Morse pair -/

/-- `b₀ = R F(h - η) + 2σ`. -/
def bTop : ℝ := Cmp.rearr D.h D.F (D.h - D.eta) + 2 * D.sigma

/-- `Ē = b₀ - m* + 2δ`. -/
def Ebar : ℝ := D.bTop - D.U D.pstar + 2 * D.tol

/-- `u₁ = √Ē + 1`. -/
def u1 : ℝ := √D.Ebar + 1

/-- The planar Morse pair. -/
def morse : MorsePair where
  X := fun u => D.wellU.X u + zeta D.u1 u
  Y := fun v => D.wellV.X v + zeta D.u1 v
  a := 1 / D.wellU.lin
  b := 1 / D.wellV.lin
  ε := min (min (D.wellU.lin * D.wellU.eps) (D.wellV.lin * D.wellV.eps)) 1

/-- The inner map. -/
def finner : ℂ → ℂ := D.morse.finner

/-- `P_lo = p* + X_U(-u₁)`, `P_hi = p* + X_U(u₁)`. -/
def Plo : ℝ := D.pstar + D.wellU.X (-D.u1)
def Phi : ℝ := D.pstar + D.wellU.X D.u1

/-- The cutoff level `a = P_lo/4` of the smooth chart. -/
def acut : ℝ := D.Plo / 4

/-- The endpoint map `Φ = C_s ∘ f`. -/
def endMap (z : ℂ) : ℂ := chartS D.pstar D.acut (D.finner z)

/-- `r_b = √(p*/π)`. -/
def rb : ℝ := √(D.pstar / π)

/-- `c_x = a/√(ab)`, `c_y = b/√(ab)`. -/
def cx : ℝ := D.morse.a / √(D.morse.a * D.morse.b)
def cy : ℝ := D.morse.b / √(D.morse.a * D.morse.b)

/-- The source-disk parameter `p† = h - 5η`. -/
def pdagP : ℝ := D.h - 5 * D.eta

/-- The input of the Alexander family. -/
def alexInput : AlexInput where
  Φ := D.endMap
  A11 := -(D.cx / (2 * π * D.rb))
  A22 := -(2 * π * D.rb * D.cy)
  h := D.h
  pdag := D.pdagP
  Rq := √(D.Phi / π)

variable {D}

lemma wellU_lo : D.wellU.lo = -D.pstar := by simp [Well.lo, wellU]
lemma wellU_hi : D.wellU.hi = D.h - D.pstar := rfl
lemma wellV_lo : D.wellV.lo = -(1 / 2) := by simp [Well.lo, wellV]
lemma wellV_hi : D.wellV.hi = 1 / 2 := by simp [Well.hi, wellV]

section hyp
variable (hD : D.Hyp)
include hD

lemma tol_pos : 0 < D.tol := by unfold tol; linarith [hD.e_pos]

lemma u1_pos : 1 ≤ D.u1 := by unfold u1; linarith [Real.sqrt_nonneg D.Ebar]

lemma Ebar_le : D.Ebar ≤ D.u1 ^ 2 := by
  unfold u1
  rcases le_or_gt 0 D.Ebar with h | h
  · have := Real.sq_sqrt h
    nlinarith [Real.sqrt_nonneg D.Ebar]
  · nlinarith [Real.sqrt_nonneg D.Ebar]

lemma morse_hyp : D.morse.Hyp := by
  have hU := wellU_hyp hD
  have hV := wellV_hyp hD
  have hu1 := u1_pos hD
  have hlU := Well.lin_pos hU
  have hlV := Well.lin_pos hV
  have heU := Well.eps_pos hU
  have heV := Well.eps_pos hV
  have hz := zeta_contDiff D.u1
  have hdX : ∀ u, deriv (fun u => D.wellU.X u + zeta D.u1 u) u =
      deriv D.wellU.X u + deriv (zeta D.u1) u := fun u =>
    deriv_add ((Well.X_smooth hU).differentiable (by simp) u) (hz.differentiable (by simp) u)
  have hdY : ∀ u, deriv (fun u => D.wellV.X u + zeta D.u1 u) u =
      deriv D.wellV.X u + deriv (zeta D.u1) u := fun u =>
    deriv_add ((Well.X_smooth hV).differentiable (by simp) u) (hz.differentiable (by simp) u)
  have hεle : ∀ u, |u| ≤ min (min (D.wellU.lin * D.wellU.eps) (D.wellV.lin * D.wellV.eps)) 1 →
      |u| ≤ D.u1 := fun u hu => hu.trans ((min_le_right _ _).trans hu1)
  refine
    { X_smooth := (Well.X_smooth hU).add hz
      Y_smooth := (Well.X_smooth hV).add hz
      X_deriv_pos := fun u => by
        show 0 < deriv (fun u => D.wellU.X u + zeta D.u1 u) u
        rw [hdX]; linarith [Well.X_deriv_pos hU u, deriv_zeta_nonneg D.u1 u]
      Y_deriv_pos := fun u => by
        show 0 < deriv (fun u => D.wellV.X u + zeta D.u1 u) u
        rw [hdY]; linarith [Well.X_deriv_pos hV u, deriv_zeta_nonneg D.u1 u]
      a_pos := by show 0 < 1 / D.wellU.lin; positivity
      b_pos := by show 0 < 1 / D.wellV.lin; positivity
      ε_pos := by
        show 0 < min (min (D.wellU.lin * D.wellU.eps) (D.wellV.lin * D.wellV.eps)) 1
        exact lt_min (lt_min (by positivity) (by positivity)) one_pos
      X_lin := fun u hu => by
        show D.wellU.X u + zeta D.u1 u = 1 / D.wellU.lin * u
        rw [Well.X_linear hU (hu.trans ((min_le_left _ _).trans (min_le_left _ _))),
          zeta_eq_zero (hεle u hu), add_zero]
        ring
      Y_lin := fun u hu => by
        show D.wellV.X u + zeta D.u1 u = 1 / D.wellV.lin * u
        rw [Well.X_linear hV (hu.trans ((min_le_left _ _).trans (min_le_right _ _))),
          zeta_eq_zero (hεle u hu), add_zero]
        ring
      X_top := ?_
      X_bot := ?_
      Y_top := ?_
      Y_bot := ?_ }
  · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_left _ (D.wellU.lo - D.u1)
      tendsto_id)
    filter_upwards [eventually_ge_atTop (D.u1 + 1)] with u hu
    have := (Well.X_mem hU u).1
    have := zeta_ge (by linarith) hu
    simp only [id, morse]; linarith
  · refine tendsto_atBot_mono' _ ?_ (tendsto_atBot_add_const_left _ (D.wellU.hi + D.u1)
      tendsto_id)
    filter_upwards [eventually_le_atBot (-D.u1 - 1)] with u hu
    have := (Well.X_mem hU u).2
    have := zeta_le (by linarith) hu
    simp only [id, morse]; linarith
  · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_left _ (D.wellV.lo - D.u1)
      tendsto_id)
    filter_upwards [eventually_ge_atTop (D.u1 + 1)] with u hu
    have := (Well.X_mem hV u).1
    have := zeta_ge (by linarith) hu
    simp only [id, morse]; linarith
  · refine tendsto_atBot_mono' _ ?_ (tendsto_atBot_add_const_left _ (D.wellV.hi + D.u1)
      tendsto_id)
    filter_upwards [eventually_le_atBot (-D.u1 - 1)] with u hu
    have := (Well.X_mem hV u).2
    have := zeta_le (by linarith) hu
    simp only [id, morse]; linarith

/-! ### `R = f̃_U` and `W = f̃_V` on the relevant sublevel sets -/

lemma abs_le_u1 {u : ℝ} (h : u ^ 2 ≤ D.u1 ^ 2) : |u| ≤ D.u1 := by
  have := u1_pos hD
  rw [← sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg u) (by linarith)).mp h

lemma morseX_eq {u : ℝ} (hu : |u| ≤ D.u1) : D.morse.X u = D.wellU.X u := by
  show D.wellU.X u + zeta D.u1 u = D.wellU.X u
  rw [zeta_eq_zero hu, add_zero]

lemma morseY_eq {u : ℝ} (hu : |u| ≤ D.u1) : D.morse.Y u = D.wellV.X u := by
  show D.wellV.X u + zeta D.u1 u = D.wellV.X u
  rw [zeta_eq_zero hu, add_zero]

theorem Rf_eq {x : ℝ} (hx : x ∈ Ioo D.wellU.lo D.wellU.hi) (h : D.wellU.ft x ≤ D.u1 ^ 2) :
    D.morse.Rf x = D.wellU.ft x := by
  have hU := wellU_hyp hD
  set u := D.wellU.Sig x
  have hu2 : u ^ 2 = D.wellU.ft x := Well.Sig_sq hU hx
  have hu : |u| ≤ D.u1 := abs_le_u1 hD (by rw [hu2]; exact h)
  have hX : D.morse.X u = x := by rw [morseX_eq hD hu, Well.X_Sig hU hx]
  rw [MorsePair.Rf, Inner.invR_eq_of_apply_eq (MorsePair.X_strictMono (morse_hyp hD)).injective hX,
    hu2]

theorem Wf_eq {y : ℝ} (hy : y ∈ Ioo D.wellV.lo D.wellV.hi) (h : D.wellV.ft y ≤ D.u1 ^ 2) :
    D.morse.Wf y = D.wellV.ft y := by
  have hV := wellV_hyp hD
  set u := D.wellV.Sig y
  have hu2 : u ^ 2 = D.wellV.ft y := Well.Sig_sq hV hy
  have hu : |u| ≤ D.u1 := abs_le_u1 hD (by rw [hu2]; exact h)
  have hX : D.morse.Y u = y := by rw [morseY_eq hD hu, Well.X_Sig hV hy]
  rw [MorsePair.Wf, Inner.invR_eq_of_apply_eq (MorsePair.Y_strictMono (morse_hyp hD)).injective hX,
    hu2]

theorem Rf_back {x : ℝ} (h : D.morse.Rf x ≤ D.u1 ^ 2) :
    x ∈ Ioo D.wellU.lo D.wellU.hi ∧ D.morse.Rf x = D.wellU.ft x ∧
      D.wellU.X (-D.u1) ≤ x ∧ x ≤ D.wellU.X D.u1 := by
  have hU := wellU_hyp hD
  have hM := morse_hyp hD
  set u := invR D.morse.X x
  have hXu : D.morse.X u = x := MorsePair.X_apply_inv hM x
  have hu : |u| ≤ D.u1 := abs_le_u1 hD h
  have hx : D.wellU.X u = x := by rw [← morseX_eq hD hu]; exact hXu
  have hmono := (Well.X_strictMono hU).monotone
  rw [abs_le] at hu
  refine ⟨hx ▸ Well.X_mem hU u, ?_, hx ▸ hmono hu.1, hx ▸ hmono hu.2⟩
  rw [← hx, Well.ft_X hU, MorsePair.Rf, hx]

theorem Wf_back {y : ℝ} (h : D.morse.Wf y ≤ D.u1 ^ 2) :
    y ∈ Ioo D.wellV.lo D.wellV.hi ∧ D.morse.Wf y = D.wellV.ft y := by
  have hV := wellV_hyp hD
  have hM := morse_hyp hD
  set u := invR D.morse.Y y
  have hYu : D.morse.Y u = y := MorsePair.Y_apply_inv hM y
  have hu : |u| ≤ D.u1 := abs_le_u1 hD h
  have hy : D.wellV.X u = y := by rw [← morseY_eq hD hu]; exact hYu
  refine ⟨hy ▸ Well.X_mem hV u, ?_⟩
  rw [← hy, Well.ft_X hV, MorsePair.Wf, hy]

/-! ### Closeness to `U` and `V` -/

lemma ftU_close (x : ℝ) : |D.wellU.ft x - (D.U (D.pstar + x) - D.U D.pstar)| ≤ D.tol :=
  Well.ft_close (wellU_hyp hD) x

lemma ftV_close (y : ℝ) : |D.wellV.ft y - D.V y| ≤ D.tol := by
  have := Well.ft_close (wellV_hyp hD) y
  have hg : D.wellV.g y = D.V y := by simp [Well.g, wellV, V_zero]
  rwa [hg] at this

/-! ### The area comparison -/

lemma rearr_mono {I I' : ℝ} (hI : I ∈ Icc 0 D.h) (hI' : I' ∈ Icc 0 D.h) (h : I ≤ I') :
    Cmp.rearr D.h D.F I ≤ Cmp.rearr D.h D.F I' :=
  Cmp.rearr_monotoneOn hD.F_cont hD.F_convex hI hI' h

theorem area_le {b : ℝ} (hb : b - D.U D.pstar + 2 * D.tol ≤ D.u1 ^ 2) :
    volume {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧ D.U x.1 + D.V x.2 ≤ b} ≤
      volume {p : ℝ × ℝ | D.morse.Rf p.1 + D.morse.Wf p.2 ≤ b - D.U D.pstar + 2 * D.tol} := by
  set Q := {p : ℝ × ℝ | D.morse.Rf p.1 + D.morse.Wf p.2 ≤ b - D.U D.pstar + 2 * D.tol}
  have hsub : {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧ D.U x.1 + D.V x.2 ≤ b} ⊆
      (fun x => x + (-D.pstar, 0)) ⁻¹' Q := by
    rintro ⟨P, y⟩ ⟨hP, hy, hb'⟩
    dsimp only at hP hy hb'
    simp only [mem_preimage, Prod.mk_add_mk, add_zero, Q, mem_setOf_eq]
    have hm := pstar_isMin hD hP
    have htol := tol_pos hD
    have hV0 := V_nonneg' hD (y := y) (abs_lt.mp hy)
    have hx : P + -D.pstar ∈ Ioo D.wellU.lo D.wellU.hi := by
      rw [wellU_lo, wellU_hi]; exact ⟨by linarith [hP.1], by linarith [hP.2]⟩
    have hyI : y ∈ Ioo D.wellV.lo D.wellV.hi := by
      rw [wellV_lo, wellV_hi]; exact abs_lt.mp hy
    have h1 := (abs_le.mp (ftU_close hD (P + -D.pstar))).2
    rw [show D.pstar + (P + -D.pstar) = P by ring] at h1
    have h2 := (abs_le.mp (ftV_close hD y)).2
    have hR := Rf_eq hD hx (by linarith)
    have hW := Wf_eq hD hyI (by linarith)
    rw [hR, hW]; linarith
  calc volume {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧ D.U x.1 + D.V x.2 ≤ b}
      ≤ volume ((fun x => x + (-D.pstar, (0 : ℝ))) ⁻¹' Q) := measure_mono hsub
    _ = volume Q := measure_preimage_add_right _ _ _

/-- `E(I) < b(I) - m* + 2δ` for `0 ≤ I ≤ h - 4η`, `b(I) = R F(I + 3η) + 2σ`. -/
theorem Einv_lt {I : ℝ} (hI0 : 0 ≤ I) (hIh : I ≤ D.h - 4 * D.eta) :
    Einv D.morse.JF 0 I <
      Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma - D.U D.pstar + 2 * D.tol := by
  have hη := hD.eta_pos
  have hηh := hD.eta_le
  have hh := hD.h_pos
  set b := Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma
  have hbE : b - D.U D.pstar + 2 * D.tol ≤ D.u1 ^ 2 := by
    refine le_trans ?_ (Ebar_le hD)
    have := rearr_mono hD (I := I + 3 * D.eta) (I' := D.h - D.eta)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    unfold Ebar bTop; simp only [b]; linarith
  have harea := (hD.area_sublevel hI0 hIh).1
  have hS := lt_of_lt_of_le harea (area_le hD hbE)
  apply MorsePair.Einv_lt_of_area (morse_hyp hD) _ hS
  -- nonnegativity of the level
  by_contra hneg
  push Not at hneg
  have hempty : {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧ D.U x.1 + D.V x.2 ≤ b} = ∅ := by
    ext ⟨P, y⟩
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hP hy
    have := pstar_isMin hD hP
    have := V_nonneg' hD (y := y) (abs_lt.mp hy)
    have := tol_pos hD
    linarith
  rw [hempty, measure_empty] at harea
  exact absurd harea ENNReal.not_lt_zero

/-- **Inner comparison.** For `π|z|² ≤ h - 4η`, with `f(z) = x + iy`: `x ∈ (P_lo - p*, P_hi - p*)`,
`|y| < 1/2`, and `F(p* + x) < R F(π|z|²) + e`. -/
theorem inner_comparison {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta) :
    D.Plo ≤ D.pstar + (D.finner z).re ∧ D.pstar + (D.finner z).re ≤ D.Phi ∧
      |(D.finner z).im| < 1 / 2 ∧
      D.F (D.pstar + (D.finner z).re) < Cmp.rearr D.h D.F (π * ‖z‖ ^ 2) + D.e := by
  have hM := morse_hyp hD
  have hη := hD.eta_pos
  have hηh := hD.eta_le
  have hh := hD.h_pos
  have he := hD.e_pos
  set I := π * ‖z‖ ^ 2
  have hI0 : 0 ≤ I := by positivity
  set x := (D.finner z).re
  set y := (D.finner z).im
  have hlev : D.morse.Rf x + D.morse.Wf y = Einv D.morse.JF 0 I := MorsePair.finner_level hM z
  have hE := Einv_lt hD hI0 hz
  set b := Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma
  have hbE : b - D.U D.pstar + 2 * D.tol ≤ D.u1 ^ 2 := by
    refine le_trans ?_ (Ebar_le hD)
    have := rearr_mono hD (I := I + 3 * D.eta) (I' := D.h - D.eta)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    unfold Ebar bTop; simp only [b]; linarith
  have hR0 := MorsePair.Rf_nonneg hM x
  have hW0 := MorsePair.Wf_nonneg hM y
  obtain ⟨hx, hRx, hlo, hhi⟩ := Rf_back hD (x := x) (by linarith)
  obtain ⟨hy, hWy⟩ := Wf_back hD (y := y) (by linarith)
  rw [wellU_lo, wellU_hi] at hx
  rw [wellV_lo, wellV_hi] at hy
  have h1 := (abs_le.mp (ftU_close hD x)).1
  have h2 := (abs_le.mp (ftV_close hD y)).1
  have hP : D.pstar + x ∈ Ioo 0 D.h := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hF := hD.U_ge_F hP
  have hV0 := V_nonneg' hD hy
  have hUV : D.U (D.pstar + x) + D.V y < b + 4 * D.tol := by linarith
  have hlip := Cmp.rearr_lipschitz hD.F_cont hD.L_nonneg hD.F_lip (I + 3 * D.eta)
    ⟨by linarith, by linarith⟩ I ⟨hI0, by linarith⟩
  rw [show I + 3 * D.eta - I = 3 * D.eta by ring,
    abs_of_pos (show (0 : ℝ) < 3 * D.eta by linarith)] at hlip
  have hLη := hD.L_mul_eta
  have hsig : D.sigma = D.e / 8 := rfl
  have htol : D.tol = D.e / 64 := rfl
  refine ⟨by unfold Plo; linarith, by unfold Phi; linarith, abs_lt.mpr ⟨hy.1, hy.2⟩, ?_⟩
  have := (abs_le.mp hlip).2
  simp only [b] at hUV
  nlinarith

/-! ### The endpoint map -/

lemma Plo_pos : 0 < D.Plo := by
  have := (Well.X_mem (wellU_hyp hD) (-D.u1)).1
  rw [wellU_lo] at this
  unfold Plo; linarith

lemma Phi_lt : D.Phi < D.h := by
  have := (Well.X_mem (wellU_hyp hD) D.u1).2
  rw [wellU_hi] at this
  unfold Phi; linarith

lemma Phi_pos : 0 < D.Phi := by
  have hU := wellU_hyp hD
  have := (Well.X_strictMono hU).monotone (show -D.u1 ≤ D.u1 by linarith [u1_pos hD])
  have := Plo_pos hD
  unfold Plo at this; unfold Phi; linarith

lemma acut_pos : 0 < D.acut := by unfold acut; linarith [Plo_pos hD]

lemma pdag_le : D.pdagP ≤ D.h - 4 * D.eta := by unfold pdagP; linarith [hD.eta_pos]

lemma pdag_pos : 0 < D.pdagP := by unfold pdagP; linarith [hD.eta_le, hD.h_pos]

lemma two_acut_lt {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta) :
    2 * D.acut < D.pstar + (D.finner z).re := by
  have := (inner_comparison hD hz).1
  have := Plo_pos hD
  unfold acut; linarith

lemma endMap_eq {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta) :
    D.endMap z = chart D.pstar (D.finner z) :=
  chartS_eq (acut_pos hD) (two_acut_lt hD hz).le

lemma endMap_moment {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta) :
    π * ‖D.endMap z‖ ^ 2 = D.pstar + (D.finner z).re := by
  rw [endMap_eq hD hz]
  exact chart_moment (by linarith [two_acut_lt hD hz, acut_pos hD])

lemma finner_smooth : ContDiff ℝ ∞ D.finner := MorsePair.finner_smooth (morse_hyp hD)

lemma endMap_smooth : ContDiff ℝ ∞ D.endMap :=
  (chartS_contDiff (acut_pos hD)).comp (finner_smooth hD)

theorem endMap_det {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta) :
    LinearMap.det (fderiv ℝ D.endMap z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hM := morse_hyp hD
  have h2a := two_acut_lt hD hz
  have hf : HasFDerivAt D.finner (fderiv ℝ D.finner z) z :=
    ((finner_smooth hD).differentiable (by simp) z).hasFDerivAt
  have hC : HasFDerivAt (chartS D.pstar D.acut) (fderiv ℝ (chart D.pstar) (D.finner z))
      (D.finner z) := by
    have h' := (hasFDerivAt_chart (p := D.pstar) (w := D.finner z) (by linarith [acut_pos hD]))
    rw [h'.fderiv]
    exact h'.congr_of_eventuallyEq (chartS_eventually (acut_pos hD) h2a)
  have hcomp := hC.comp z hf
  rw [show D.endMap = chartS D.pstar D.acut ∘ D.finner from rfl, hcomp.fderiv]
  show LinearMap.det ((fderiv ℝ (chart D.pstar) (D.finner z) : ℂ →ₗ[ℝ] ℂ) ∘ₗ
    (fderiv ℝ D.finner z : ℂ →ₗ[ℝ] ℂ)) = 1
  rw [LinearMap.det_comp, chart_det (by linarith [acut_pos hD]), one_mul]
  exact MorsePair.finner_symplectic hM z

theorem endMap_injOn : InjOn D.endMap {z : ℂ | π * ‖z‖ ^ 2 < D.pdagP} := by
  intro z₁ hz₁ z₂ hz₂ h
  have hz₁' : π * ‖z₁‖ ^ 2 ≤ D.h - 4 * D.eta := (le_of_lt hz₁).trans (pdag_le hD)
  have hz₂' : π * ‖z₂‖ ^ 2 ≤ D.h - 4 * D.eta := (le_of_lt hz₂).trans (pdag_le hD)
  rw [endMap_eq hD hz₁', endMap_eq hD hz₂'] at h
  have hd1 : D.finner z₁ ∈ {w : ℂ | 0 < D.pstar + w.re ∧ |w.im| < 1 / 2} :=
    ⟨by linarith [two_acut_lt hD hz₁', acut_pos hD], (inner_comparison hD hz₁').2.2.1⟩
  have hd2 : D.finner z₂ ∈ {w : ℂ | 0 < D.pstar + w.re ∧ |w.im| < 1 / 2} :=
    ⟨by linarith [two_acut_lt hD hz₂', acut_pos hD], (inner_comparison hD hz₂').2.2.1⟩
  exact (MorsePair.finner_bijective (morse_hyp hD)).1 (chart_injOn hd1 hd2 h)

lemma finner_hasFDerivAt_zero :
    HasFDerivAt D.finner (ofRealCLM.comp (D.cx • reCLM) +
      (ofRealCLM.comp (D.cy • imCLM)).smulRight I) 0 := by
  have hM := morse_hyp hD
  set L : ℂ →L[ℝ] ℂ := ofRealCLM.comp (D.cx • reCLM) + (ofRealCLM.comp (D.cy • imCLM)).smulRight I
  have hsj : 0 < √(D.morse.a * D.morse.b) := Real.sqrt_pos.2 (mul_pos hM.a_pos hM.b_pos)
  have hr : 0 < √(D.morse.a * D.morse.b) * D.morse.ε := mul_pos hsj hM.ε_pos
  have hev : D.finner =ᶠ[𝓝 0] L := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [finner, MorsePair.finner_linear hM hz]
    simp [L, cx, cy]
  exact L.hasFDerivAt.congr_of_eventuallyEq hev

theorem endMap_zero : D.endMap 0 = -((D.rb : ℝ) : ℂ) := by
  have h0 : D.finner 0 = 0 := MorsePair.finner_zero (morse_hyp hD)
  have hz : π * ‖(0 : ℂ)‖ ^ 2 ≤ D.h - 4 * D.eta := by
    simp; linarith [hD.eta_le, hD.h_pos]
  rw [endMap_eq hD hz, h0]
  simp [chart, rb]

theorem endMap_deriv_zero : fderiv ℝ D.endMap 0 = D.alexInput.A0 := by
  have hz : π * ‖(0 : ℂ)‖ ^ 2 ≤ D.h - 4 * D.eta := by
    simp; linarith [hD.eta_le, hD.h_pos]
  have h0 : D.finner 0 = 0 := MorsePair.finner_zero (morse_hyp hD)
  have h2a := two_acut_lt hD hz
  rw [h0] at h2a
  have hp : 0 < D.pstar + (0 : ℂ).re := by simp; exact (pstar_mem hD).1
  have hC := (hasFDerivAt_chart (p := D.pstar) (w := 0) hp).congr_of_eventuallyEq
    (chartS_eventually (acut_pos hD) h2a)
  rw [← h0] at hC
  have hcomp := hC.comp 0 (finner_hasFDerivAt_zero hD)
  rw [show D.endMap = chartS D.pstar D.acut ∘ D.finner from rfl, hcomp.fderiv]
  have hpi := Real.pi_pos
  have hps := (pstar_mem hD).1
  have hrb : 0 < D.rb := Real.sqrt_pos.2 (div_pos hps hpi)
  ext1 v
  apply Complex.ext
  · simp [AlexInput.A0, alexInput, h0, rb, -Complex.ofReal_div, -Complex.ofReal_mul,
      -Complex.ofReal_inv, -Complex.ofReal_one, -one_div]
    field_simp
  · simp [AlexInput.A0, alexInput, h0, rb, -Complex.ofReal_div, -Complex.ofReal_mul,
      -Complex.ofReal_inv, -Complex.ofReal_one, -one_div]
    ring

theorem alex_hyp : D.alexInput.Hyp := by
  have hM := morse_hyp hD
  have hpi := Real.pi_pos
  have hps := pstar_mem hD
  have hrb : 0 < D.rb := Real.sqrt_pos.2 (div_pos hps.1 hpi)
  have hsj : 0 < √(D.morse.a * D.morse.b) := Real.sqrt_pos.2 (mul_pos hM.a_pos hM.b_pos)
  have hcx : 0 < D.cx := div_pos hM.a_pos hsj
  have hcy : 0 < D.cy := div_pos hM.b_pos hsj
  refine
    { smooth := endMap_smooth hD
      det := fun z hz => endMap_det hD ((le_of_lt hz).trans (pdag_le hD))
      injOn := endMap_injOn hD
      deriv_zero := endMap_deriv_zero hD
      A11_neg := by
        show -(D.cx / (2 * π * D.rb)) < 0
        have : 0 < D.cx / (2 * π * D.rb) := by positivity
        linarith
      A22_neg := by
        show -(2 * π * D.rb * D.cy) < 0
        have : 0 < 2 * π * D.rb * D.cy := by positivity
        linarith
      A11_mul_A22 := by
        show -(D.cx / (2 * π * D.rb)) * -(2 * π * D.rb * D.cy) = 1
        have hc : D.cx * D.cy = 1 := by
          unfold cx cy
          rw [div_mul_div_comm, Real.mul_self_sqrt (mul_pos hM.a_pos hM.b_pos).le]
          exact div_self (mul_pos hM.a_pos hM.b_pos).ne'
        field_simp
        linarith
      pdag_pos := pdag_pos hD
      pdag_lt_h := by show D.h - 5 * D.eta < D.h; linarith [hD.eta_pos]
      b_lt := by
        show ‖D.endMap 0‖ < √(D.h / π)
        rw [endMap_zero hD, norm_neg, Complex.norm_real, Real.norm_of_nonneg hrb.le]
        exact Real.sqrt_lt_sqrt (div_nonneg hps.1.le hpi.le)
          (div_lt_div_of_pos_right hps.2 hpi)
      bound_one := fun z hz => by
        show ‖D.endMap z‖ ≤ √(D.Phi / π)
        have hz' : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta := (le_of_lt hz).trans (pdag_le hD)
        have hm := endMap_moment hD hz'
        have hc := (inner_comparison hD hz').2.1
        rw [← Real.sqrt_sq (norm_nonneg (D.endMap z))]
        exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hpi]; linarith)
      Rq_lt := Real.sqrt_lt_sqrt (div_nonneg (Phi_pos hD).le hpi.le)
        (div_lt_div_of_pos_right (Phi_lt hD) hpi) }

end hyp

end PlanarInput

end SymplecticPacking.Branch2.Planar
