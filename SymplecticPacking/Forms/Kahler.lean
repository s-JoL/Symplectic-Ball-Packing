import Mathlib
import SymplecticPacking.Forms.Basic
import SymplecticPacking.Forms.Cartan

/-!
# The operator `d^c` on a complex vector space

Generic part of the forms used in `sec:rtc`.

`V` is a complex normed space, viewed as a real one (`[NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]`,
the standard Mathlib pattern avoiding the `restrictScalars` diamond; e.g. `Fin n → ℂ`,
`EuclideanSpace ℂ (Fin n)`, `(Fin 3 → ℂ) × ℂ`).

Convention (`sec:rtc`, `sec:rtc-conventions`): `d^c = (i/4π)(∂̄ − ∂)`. For a real function
`Φ`, `∂Φ(ξ) = (dΦ(ξ) − i dΦ(iξ))/2`, `∂̄Φ(ξ) = (dΦ(ξ) + i dΦ(iξ))/2`, so
`(∂̄ − ∂)Φ(ξ) = i dΦ(iξ)` and `d^cΦ(ξ) = −(1/4π) dΦ(iξ)`. This is our definition `dc`.

Contents:
* `dc`, `dc_apply`, smoothness (`differentiableAt_dc`, `contDiffAt_dc`);
* `d1_dc_apply`: `dd^cΦ(ξ, η) = (1/4π)(D²Φ(η, iξ) − D²Φ(ξ, iη))`;
* pluriharmonic functions (`IsPluriharmonicAt`: the Levi form `D²ψ(η, iξ) − D²ψ(ξ, iη)`
  vanishes): `d1_dc_add_pluriharmonic`; real parts of holomorphic functions are pluriharmonic
  (`isPluriharmonicAt_re`), and so is `log |g|²` for holomorphic nonvanishing `g`
  (`isPluriharmonicAt_log_normSq`).
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate ContinuousLinearMap Filter Topology
open SymplecticPacking.Forms (Form1 Form2 d1 d1_apply symm2 differentiableAt_fderiv_of_contDiffAt
  fderiv_eval1)
open scoped Real ContDiff

/-! ### Directional derivatives along lines (used throughout `sec:rtc`) -/

section line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_line {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) (v : E) :
    HasDerivAt (fun t : ℝ => f (y + t • v)) (fderiv ℝ f y v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hf' : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (f := fun t : ℝ => y + t • v) 0 hl

/-- Computing a directional derivative from the derivative along the line `t ↦ y + t v`. -/
lemma fderiv_apply_of_line {f : E → ℝ} {y v : E} {D : ℝ} (hf : DifferentiableAt ℝ f y)
    (h : HasDerivAt (fun t : ℝ => f (y + t • v)) D 0) : fderiv ℝ f y v = D :=
  (hasDerivAt_line hf v).unique h

end line

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-! ### The complex structure and `d^c` -/

/-- Multiplication by `i`, as a real-linear map. -/
def Jc : V →L[ℝ] V := ((I : ℂ) • ContinuousLinearMap.id ℂ V).restrictScalars ℝ

@[simp] lemma Jc_apply (ξ : V) : (Jc : V →L[ℝ] V) ξ = I • ξ := by simp [Jc]

/-- `d^cΦ = (i/4π)(∂̄ − ∂)Φ`, i.e. `d^cΦ(x)(ξ) = −(1/4π) dΦ(x)(iξ)`. -/
def dc (Φ : V → ℝ) : Form1 V := fun x => (-(1 / (4 * π))) • (fderiv ℝ Φ x).comp Jc

lemma dc_apply (Φ : V → ℝ) (x ξ : V) : dc Φ x ξ = -(1 / (4 * π)) * fderiv ℝ Φ x (I • ξ) := by
  simp [dc]

lemma differentiableAt_dc {Φ : V → ℝ} {x : V} (h : ContDiffAt ℝ 2 Φ x) :
    DifferentiableAt ℝ (dc Φ) x := by
  have h1 := differentiableAt_fderiv_of_contDiffAt h
  exact (h1.clm_comp (differentiableAt_const (Jc : V →L[ℝ] V))).const_smul (-(1 / (4 * π)) : ℝ)

lemma contDiffAt_dc {Φ : V → ℝ} {x : V} {n : WithTop ℕ∞} (h : ContDiffAt ℝ (n + 1) Φ x) :
    ContDiffAt ℝ n (dc Φ) x := by
  have h1 : ContDiffAt ℝ n (fderiv ℝ Φ) x := h.fderiv_right le_rfl
  exact (h1.clm_comp contDiffAt_const).const_smul _

/-- `fderiv (d^cΦ)` evaluated: `D(d^cΦ)(x)(ξ)(η) = −(1/4π) D²Φ(x)(ξ)(iη)`. -/
lemma fderiv_dc_apply {Φ : V → ℝ} {x : V} (h : ContDiffAt ℝ 2 Φ x) (ξ η : V) :
    fderiv ℝ (dc Φ) x ξ η = -(1 / (4 * π)) * fderiv ℝ (fderiv ℝ Φ) x ξ (I • η) := by
  have h1 := differentiableAt_fderiv_of_contDiffAt h
  rw [← fderiv_eval1 (differentiableAt_dc h)]
  have he : (fun y => dc Φ y η) = fun y => -(1 / (4 * π)) * fderiv ℝ Φ y (I • η) := by
    funext y; exact dc_apply Φ y η
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ Φ y (I • η)) x := by fun_prop
  rw [he, fderiv_const_mul h2, smul_apply, fderiv_eval1 h1, smul_eq_mul]

/-- `dd^cΦ` in terms of the second derivative:
`dd^cΦ(x)(ξ, η) = (1/4π)(D²Φ(x)(η, iξ) − D²Φ(x)(ξ, iη))`. -/
theorem d1_dc_apply {Φ : V → ℝ} {x : V} (h : ContDiffAt ℝ 2 Φ x) (ξ η : V) :
    d1 (dc Φ) x ξ η =
      1 / (4 * π) * (fderiv ℝ (fderiv ℝ Φ) x η (I • ξ) - fderiv ℝ (fderiv ℝ Φ) x ξ (I • η)) := by
  rw [d1_apply, fderiv_dc_apply h, fderiv_dc_apply h]; ring

/-! ### Chain rule: `d^c(φ ∘ μ) = φ'(μ) d^c μ` -/

/-! ### Pluriharmonic functions -/

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in
lemma fderiv_evalH {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {A : V → V →L[ℝ] H}
    {q : V} (h : DifferentiableAt ℝ A q) (u z : V) :
    fderiv ℝ (fun p => A p z) q u = fderiv ℝ A q u z := by
  rw [fderiv_clm_apply h (differentiableAt_const z)]
  simp

/-- `ψ` is pluriharmonic at `x`: its Levi form `D²ψ(x)(η, iξ) − D²ψ(x)(ξ, iη)` vanishes. -/
def IsPluriharmonicAt (ψ : V → ℝ) (x : V) : Prop :=
  ∀ ξ η : V, fderiv ℝ (fderiv ℝ ψ) x η (I • ξ) = fderiv ℝ (fderiv ℝ ψ) x ξ (I • η)

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in
lemma eventually_differentiableAt {f : V → ℝ} {x : V} (h : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
  (h.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in
/-- Second derivatives are additive. -/
lemma fderiv2_add {Φ ψ : V → ℝ} {x : V} (hΦ : ContDiffAt ℝ 2 Φ x) (hψ : ContDiffAt ℝ 2 ψ x) :
    fderiv ℝ (fderiv ℝ (fun y => Φ y + ψ y)) x =
      fderiv ℝ (fderiv ℝ Φ) x + fderiv ℝ (fderiv ℝ ψ) x := by
  have he : fderiv ℝ (fun y => Φ y + ψ y) =ᶠ[𝓝 x] fun y => fderiv ℝ Φ y + fderiv ℝ ψ y := by
    filter_upwards [eventually_differentiableAt hΦ, eventually_differentiableAt hψ] with y h1 h2
    exact fderiv_add h1 h2
  rw [he.fderiv_eq]
  exact fderiv_add (differentiableAt_fderiv_of_contDiffAt hΦ)
    (differentiableAt_fderiv_of_contDiffAt hψ)

/-- Adding a pluriharmonic function does not change `dd^c`. -/
theorem d1_dc_add_pluriharmonic {Φ ψ : V → ℝ} {x : V} (hΦ : ContDiffAt ℝ 2 Φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) (hp : IsPluriharmonicAt ψ x) :
    d1 (dc (fun y => Φ y + ψ y)) x = d1 (dc Φ) x := by
  ext ξ η
  rw [d1_dc_apply (hΦ.add hψ), d1_dc_apply hΦ, fderiv2_add hΦ hψ]
  simp only [add_apply]
  rw [hp ξ η]; ring

omit [IsScalarTower ℝ ℂ V] in
/-- Pluriharmonicity only depends on the germ. -/
lemma IsPluriharmonicAt.congr {ψ ψ' : V → ℝ} {x : V} (hp : IsPluriharmonicAt ψ x)
    (he : ψ' =ᶠ[𝓝 x] ψ) : IsPluriharmonicAt ψ' x := by
  intro ξ η
  rw [he.fderiv.fderiv_eq]
  exact hp ξ η

/-- The real part of a holomorphic (near `x`) function, `C²` at `x`, is pluriharmonic. -/
theorem isPluriharmonicAt_re {h : V → ℂ} {x : V} (hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ h y)
    (h2 : ContDiffAt ℝ 2 h x) : IsPluriharmonicAt (fun y => (h y).re) x := by
  have hre2 : ContDiffAt ℝ 2 (fun y => (h y).re) x := reCLM.contDiff.contDiffAt.comp x h2
  have hD1 := differentiableAt_fderiv_of_contDiffAt h2
  -- second derivative of `re ∘ h`
  have hreD : ∀ a b, fderiv ℝ (fderiv ℝ (fun y => (h y).re)) x a b =
      (fderiv ℝ (fderiv ℝ h) x a b).re := by
    intro a b
    rw [← fderiv_eval1 (differentiableAt_fderiv_of_contDiffAt hre2)]
    have he : (fun y => fderiv ℝ (fun y => (h y).re) y b) =ᶠ[𝓝 x]
        fun y => reCLM (fderiv ℝ h y b) := by
      filter_upwards [eventually_differentiableAt (V := V) (f := fun y => (h y).re) hre2,
        (h2.eventually (by simp))] with y _ hy2
      have hy : DifferentiableAt ℝ h y := hy2.differentiableAt (by norm_num)
      have : HasFDerivAt (fun y => (h y).re) (reCLM.comp (fderiv ℝ h y)) y :=
        reCLM.hasFDerivAt.comp y hy.hasFDerivAt
      rw [this.fderiv]; rfl
    rw [he.fderiv_eq]
    have hb : DifferentiableAt ℝ (fun y => fderiv ℝ h y b) x := by fun_prop
    rw [show (fun y => reCLM (fderiv ℝ h y b)) = reCLM ∘ fun y => fderiv ℝ h y b from rfl,
      fderiv_comp x reCLM.differentiableAt hb, comp_apply, ContinuousLinearMap.fderiv,
      fderiv_evalH hD1, reCLM_apply]
  -- `ℂ`-linearity of `Dh` in the second slot propagates to `D²h`
  have hI : ∀ a b, fderiv ℝ (fderiv ℝ h) x a (I • b) = I * fderiv ℝ (fderiv ℝ h) x a b := by
    intro a b
    rw [← fderiv_evalH hD1, ← fderiv_evalH hD1]
    have he : (fun y => fderiv ℝ h y (I • b)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ h y b := by
      filter_upwards [hhol] with y hy
      rw [hy.fderiv_restrictScalars ℝ]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [he.fderiv_eq]
    have hb : DifferentiableAt ℝ (fun y => fderiv ℝ h y b) x := by fun_prop
    rw [fderiv_const_mul hb]; rfl
  intro ξ η
  rw [hreD, hreD, hI, hI, symm2 h2 η ξ]

/-- `log |g|²` is pluriharmonic where `g` is holomorphic, nonvanishing and `C²`. -/
theorem isPluriharmonicAt_log_normSq {g : V → ℂ} {x : V}
    (hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y) (h2 : ContDiffAt ℝ 2 g x) (hx : g x ≠ 0) :
    IsPluriharmonicAt (fun y => Real.log (normSq (g y))) x := by
  -- rotate `g x` to the positive real axis: `c = conj (g x)`
  set c : ℂ := conj (g x)
  have hc : c ≠ 0 := by simpa [c] using hx
  have hcg : c * g x = (normSq (g x) : ℂ) := by
    rw [mul_comm]; exact mul_conj (g x)
  have hslit : ∀ᶠ y in 𝓝 x, c * g y ∈ slitPlane := by
    have hcont : ContinuousAt (fun y => c * g y) x :=
      (continuousAt_const.mul (h2.continuousAt))
    have hmem : c * g x ∈ slitPlane := by
      rw [hcg]; exact ofReal_mem_slitPlane.mpr (normSq_pos.mpr hx)
    exact hcont.eventually (isOpen_slitPlane.mem_nhds hmem)
  set k : V → ℂ := fun y => 2 * log (c * g y) - (Real.log (normSq c) : ℂ)
  have hk : (fun y => Real.log (normSq (g y))) =ᶠ[𝓝 x] fun y => (k y).re := by
    filter_upwards [hslit] with y hy
    have hy0 : c * g y ≠ 0 := slitPlane_ne_zero hy
    have hgy : g y ≠ 0 := right_ne_zero_of_mul hy0
    simp only [k, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, zero_mul, sub_zero, log_re]
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgy),
      normSq_eq_norm_sq, normSq_eq_norm_sq, Real.log_pow, Real.log_pow]
    push_cast; ring
  refine IsPluriharmonicAt.congr ?_ hk
  refine isPluriharmonicAt_re ?_ ?_
  · filter_upwards [hhol, hslit] with y hy hys
    exact ((((differentiableAt_const c).mul hy).clog hys).const_mul 2).sub
      (differentiableAt_const _)
  · have hlog : ContDiffAt ℝ 2 (fun y => log (c * g y)) x := by
      have hm : c * g x ∈ slitPlane := hslit.self_of_nhds
      have hl : ContDiffAt ℂ 2 log (c * g x) := contDiffAt_log hm
      exact (hl.restrict_scalars ℝ).comp x (contDiffAt_const.mul h2)
    exact (contDiffAt_const.mul hlog).sub contDiffAt_const

/-! ### Sanity checks on `ℂ` -/

lemma normSq_add_smul (z u : ℂ) (t : ℝ) :
    normSq (z + t • u) = normSq z + 2 * t * (conj z * u).re + t ^ 2 * normSq u := by
  rw [normSq_add, real_smul, normSq_mul, normSq_ofReal]
  simp only [mul_re, mul_im, conj_re, conj_im, map_mul, conj_ofReal, ofReal_re, ofReal_im]
  ring

end SymplecticPacking.Return
