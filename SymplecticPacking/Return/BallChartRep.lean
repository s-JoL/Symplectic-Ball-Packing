import SymplecticPacking.Return.BallChart
import SymplecticPacking.Return.ReturnFlow

/-!
# The ball chart on representatives

`sec:rtc`, Lemma lem:rtc-ball-chart on representatives: for a smooth family `φ : E → ℂ³` of unit
vectors with `φ₀ ≠ 0`, `(b_ball ∘ φ)^* ω_std = φ^* ω_FS`.

* `omegaFS = dd^c log ‖Z‖²` on `ℂ³ ∖ 0` (the form `omegaS dn 0` of `ReturnFlow.lean`,
  `omegaS_zero`).
* `affE Z = (Z₁/Z₀, Z₂/Z₀) ∈ E4` (affine chart, via `c2ToE4`); `pull1_affE_lamFS`:
  `affE^* λ_FS = d^c log(1 + |z|²)`; `pull2_affE_lamFS`: `affE^* (dλ_FS) = ω_FS` where `Z₀ ≠ 0`
  (`log ‖Z‖² = log(1 + |z|²) + log |Z₀|²`, `log |Z₀|²` pluriharmonic).
* `ballChart_symplectic_rep`: combine with `ballChart_symplectic` (`ballAffine^* ω_std = dλ_FS`).
-/

noncomputable section

namespace SymplecticPacking.Return

open _root_.Complex ComplexConjugate ContinuousLinearMap Filter Topology
open SymplecticPacking.Forms (Form1 Form2 d1 pull1 pull2 pull1_apply pull2_apply pull2_d1_apply
  pull2_comp_apply)
open scoped Real ContDiff

/-- `ω_FS = dd^c log ‖Z‖²` on representatives (`= omegaS dn 0`). -/
def omegaFS : Form2 C3 := d1 (dc (fun Z => Real.log (nsq Z)))

lemma omegaS_zero (dn : ℝ) : omegaS dn 0 = omegaFS := by
  have : PhiS dn 0 = fun Z => Real.log (nsq Z) := by funext Z; simp [PhiS]
  simp only [omegaS, lamS, omegaFS, this]

/-! ### The affine chart -/

/-- `z = (Z₁/Z₀, Z₂/Z₀)`. -/
def affC (Z : C3) : ℂ × ℂ := (Z 1 / Z 0, Z 2 / Z 0)

/-- The affine chart as a map to `E4`. -/
def affE (Z : C3) : E4 := c2ToE4 (affC Z)

/-- `c2ToE4` as a real-linear map. -/
def c2CLM : ℂ × ℂ →L[ℝ] E4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![reCLM.comp (fst ℝ ℂ ℂ), reCLM.comp (snd ℝ ℂ ℂ),
      imCLM.comp (fst ℝ ℂ ℂ), imCLM.comp (snd ℝ ℂ ℂ)])

lemma c2CLM_apply (z : ℂ × ℂ) : c2CLM z = c2ToE4 z := by
  ext i; fin_cases i <;> simp [c2CLM, c2ToE4]

lemma contDiffAt_affC {Z : C3} (h0 : Z 0 ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℂ n affC Z :=
  ((contDiff_apply ℂ ℂ 1).contDiffAt.div (contDiff_apply ℂ ℂ 0).contDiffAt h0).prodMk
    ((contDiff_apply ℂ ℂ 2).contDiffAt.div (contDiff_apply ℂ ℂ 0).contDiffAt h0)

lemma affE_eq : affE = c2CLM ∘ affC := by funext Z; simp [affE, c2CLM_apply]

lemma contDiffAt_affE {Z : C3} (h0 : Z 0 ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n affE Z := by
  rw [affE_eq]
  exact c2CLM.contDiff.contDiffAt.comp Z ((contDiffAt_affC h0).restrict_scalars ℝ)

lemma differentiableAt_affC {Z : C3} (h0 : Z 0 ≠ 0) : DifferentiableAt ℂ affC Z :=
  (contDiffAt_affC h0 (n := 1)).differentiableAt one_ne_zero

lemma hasFDerivAt_affE {Z : C3} (h0 : Z 0 ≠ 0) :
    HasFDerivAt affE (c2CLM.comp ((fderiv ℂ affC Z).restrictScalars ℝ)) Z := by
  rw [affE_eq]
  exact c2CLM.hasFDerivAt.comp Z ((differentiableAt_affC h0).hasFDerivAt.restrictScalars ℝ)

lemma differentiableAt_lamFS (x : E4) : DifferentiableAt ℝ lamFS x := by
  have hs : DifferentiableAt ℝ (fun x : E4 => 1 / (2 * π * (1 + ‖x‖ ^ 2))) x := by
    have hn : DifferentiableAt ℝ (fun x : E4 => ‖x‖ ^ 2) x :=
      (contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero x
    have hd : DifferentiableAt ℝ (fun x : E4 => 2 * π * (1 + ‖x‖ ^ 2)) x :=
      (differentiableAt_const (2 * π)).mul ((differentiableAt_const (1 : ℝ)).add hn)
    have hne : 2 * π * (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    have := hd.inv hne
    convert this using 1
    funext y; simp [one_div]
  have hp : ∀ i j : Fin 4, DifferentiableAt ℝ
      (fun x : E4 => x i • (EuclideanSpace.proj j : E4 →L[ℝ] ℝ)) x := fun i j =>
    (EuclideanSpace.proj i : E4 →L[ℝ] ℝ).differentiableAt.smul_const _
  exact hs.smul ((((hp 0 2).sub (hp 2 0)).add (hp 1 3)).sub (hp 3 1))

/-- `affE^* λ_FS = d^c log(1 + |z|²)` where `Z₀ ≠ 0`. -/
theorem pull1_affE_lamFS {Y : C3} (h0 : Y 0 ≠ 0) :
    pull1 affE lamFS Y = dc (fun Y => Real.log (1 + ‖affE Y‖ ^ 2)) Y := by
  have hE := hasFDerivAt_affE h0
  have hpos : (1 : ℝ) + ‖affE Y‖ ^ 2 ≠ 0 := by positivity
  have hΦ := (hE.norm_sq.const_add 1).log hpos
  ext w
  rw [pull1_apply, hE.fderiv, dc_apply, hΦ.fderiv]
  simp only [comp_apply, smul_apply, coe_restrictScalars', map_smul, c2CLM_apply, smul_eq_mul,
    innerSL_apply_apply]
  rw [affE]
  generalize (fderiv ℂ affC Y) w = v
  generalize affC Y = z
  simp only [lamFS, smul_apply, add_apply, sub_apply, smul_eq_mul, PiLp.proj_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  have hN0 : 0 ≤ ‖c2ToE4 z‖ ^ 2 := by positivity
  generalize ‖c2ToE4 z‖ ^ 2 = N at hN0 ⊢
  have hN1 : 0 < 1 + N := by linarith
  simp [c2ToE4, dotProduct, Fin.sum_univ_four]
  field_simp
  ring

lemma log_affE_add {Y : C3} (h0 : Y 0 ≠ 0) :
    Real.log (1 + ‖affE Y‖ ^ 2) + Real.log (normSq (Y 0)) = Real.log (nsq Y) := by
  have hn0 : 0 < normSq (Y 0) := normSq_pos.mpr h0
  have h1 : (0 : ℝ) < 1 + ‖affE Y‖ ^ 2 := by positivity
  rw [← Real.log_mul h1.ne' hn0.ne', affE, norm_c2ToE4_sq]
  congr 1
  simp only [nsq2, affC, normSq_div, nsq, Fin.sum_univ_three]
  field_simp
  ring

/-- **`affE^* (dλ_FS) = ω_FS`** at representatives with `Z₀ ≠ 0`. -/
theorem pull2_affE_lamFS {Z : C3} (h0 : Z 0 ≠ 0) : pull2 affE (d1 lamFS) Z = omegaFS Z := by
  have hU : ∀ᶠ Y in 𝓝 Z, Y 0 ≠ 0 :=
    ((continuous_apply 0).continuousAt (x := Z)).eventually_ne h0
  set Φ : C3 → ℝ := fun Y => Real.log (1 + ‖affE Y‖ ^ 2)
  set ψ : C3 → ℝ := fun Y => Real.log (normSq (Y 0))
  have hΦ : ContDiffAt ℝ 2 Φ Z := by
    have h := (contDiffAt_affE h0 (n := 2))
    have hq : ContDiffAt ℝ 2 (fun Y => 1 + ‖affE Y‖ ^ 2) Z :=
      contDiffAt_const.add ((contDiff_norm_sq ℝ).contDiffAt.comp Z h)
    exact hq.log (by positivity)
  have hψ : ContDiffAt ℝ 2 ψ Z := by
    have hq : ContDiffAt ℝ 2 (fun Y : C3 => normSq (Y 0)) Z :=
      (contDiff_normSq' (n := 2)).contDiffAt.comp Z (contDiff_apply ℝ ℂ 0).contDiffAt
    exact hq.log (normSq_pos.mpr h0).ne'
  have hp : IsPluriharmonicAt ψ Z :=
    isPluriharmonicAt_log_normSq (g := fun Y : C3 => Y 0)
      (Eventually.of_forall fun Y => (contDiff_apply ℂ ℂ 0 (n := 1)).differentiable one_ne_zero Y)
      (contDiff_apply ℝ ℂ 0).contDiffAt h0
  -- germ identities
  have e1 : pull1 affE lamFS =ᶠ[𝓝 Z] dc Φ := by
    filter_upwards [hU] with Y hY using pull1_affE_lamFS hY
  have e2 : (fun Y => Φ Y + ψ Y) =ᶠ[𝓝 Z] fun Y => Real.log (nsq Y) := by
    filter_upwards [hU] with Y hY using log_affE_add hY
  have e3 : dc (fun Y => Φ Y + ψ Y) =ᶠ[𝓝 Z] dc (fun Y => Real.log (nsq Y)) := by
    filter_upwards [e2.eventuallyEq_nhds] with Y hY
    funext; simp only [dc, hY.fderiv_eq (𝕜 := ℝ)]
  rw [← pull2_d1_apply (contDiffAt_affE h0) (differentiableAt_lamFS _), omegaFS]
  have h1 : d1 (pull1 affE lamFS) Z = d1 (dc Φ) Z := by
    simp only [Forms.d1, e1.fderiv_eq (𝕜 := ℝ)]
  have h2 : d1 (dc (fun Y => Φ Y + ψ Y)) Z = d1 (dc (fun Y => Real.log (nsq Y))) Z := by
    simp only [Forms.d1, e3.fderiv_eq (𝕜 := ℝ)]
  rw [h1, ← h2, d1_dc_add_pluriharmonic hΦ hψ hp]

/-! ### Lemma lem:rtc-ball-chart on representatives -/

/-- **Lemma lem:rtc-ball-chart** (representatives): for a smooth family `φ` of unit vectors
with `φ₀ ≠ 0`, `(b_ball ∘ φ)^* ω_std = φ^* ω_FS`. -/
theorem ballChart_symplectic_rep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → C3} (hφ : ContDiff ℝ ∞ φ) (hZ : ∀ x, nsq (φ x) = 1) (h0 : ∀ x, φ x 0 ≠ 0) :
    pull2 (fun x => c2ToE4 (ballChart (φ x))) ωstd = pull2 φ omegaFS := by
  have he : (fun x => c2ToE4 (ballChart (φ x))) = ballAffine ∘ (affE ∘ φ) := by
    funext x
    simp only [Function.comp, affE, affC]
    rw [ballChart_affine _ (hZ x) (h0 x), ← ballAffine_c2ToE4]
  funext x
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have hA : DifferentiableAt ℝ affE (φ x) :=
    (contDiffAt_affE (h0 x) (n := 1)).differentiableAt one_ne_zero
  rw [he, pull2_comp_apply (hA.comp x hφd)
    ((contDiff_ballAffine (n := 1)).differentiable one_ne_zero _), ballChart_symplectic,
    pull2_comp_apply hφd hA]
  ext v w
  simp only [pull2_apply, pull2_affE_lamFS (h0 x)]

/-- The same with `ω_FS` written as `omegaS dn 0` (the form of `ReturnFlow.lean`). -/
theorem ballChart_symplectic_rep' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dn : ℝ) {φ : E → C3} (hφ : ContDiff ℝ ∞ φ) (hZ : ∀ x, nsq (φ x) = 1)
    (h0 : ∀ x, φ x 0 ≠ 0) :
    pull2 (fun x => c2ToE4 (ballChart (φ x))) ωstd = pull2 φ (omegaS dn 0) := by
  rw [omegaS_zero]; exact ballChart_symplectic_rep hφ hZ h0

end SymplecticPacking.Return
