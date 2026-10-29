import Mathlib
import SymplecticPacking.Explicit
import OAI.Geometry.BallPacking.BallMaps.QuadricRelativeShellFlow

/-!
# The explicit vector normal transfer (supplement `sec:vtr`: cons:vtr-injection, prop:vtr-transport,
prop:vtr-return, thm:vtr-transfer)

All stages are written in the affine chart `{Z_* ≠ 0} ≅ Affine q` of `CP^q` (`q = n − 1`
normal directions, ambient complex dimension `q + 1`), where the curve is
`locus a = {z_j² − z_0² + a_j = 0}` and the bundle `O(2)^{⊕q}` is trivialised by the section
`Z_*²`. A point of the total space is `(z, W) : Affine q × ℂ^q`; the unit lift is
`((1, z), W) / (1 + |z|²)^{1/2, 1}`, so the Hermitian norm is `u = |W|² / (1 + |z|²)²`.

* `bundlePot b` is the Kähler potential `log(1 + |z|²) + b log(1 + u)` of
  `Ω_b = ω_FS + b dd^c log(1 + u)` (lem:vtr-form), `ddcForm` its `dd^c`, with
  `d^c f (v) = −df(i v)/(4π)` (so `dd^c log(1 + |z|²)` is the FS form of line area one, the
  `affineFSForm (1/π)` of the OpenAI library).
* `radialInj b` is the radial injection `W = (1 + |z|²) √π w / √(b − π|w|²)` (cons:vtr-injection;
  in the unit lift with `Z_* > 0` this is `W_j = √π U_j / √(b − |p|)`, and the frame `U = w` is
  the frame of prop:vtr-handle(b)).
* `transportField a b T` is the `Ω_b`-orthogonal lift of `∂_T` to `X = {equations z = T W}`
  (prop:vtr-transport(c)): the unique `V` with `D_z(equations) V_z − T V_W = W` and
  `Ω_b(V, k) = 0` for every `k` tangent to `X_T`. It is the affine-chart form of
  `Ż = a⁻¹ J* S⁻¹ W, Ẇ = −T B⁻¹ S⁻¹ W`.
* `returnField a b s` is the Moser field of the path
  `ω_s = ω_FS + s b dd^c log(1 + |F|²)` (prop:vtr-return): the unique `Y` with
  `ω_s(Y, ·) = −b d^c log(1 + |F|²)`; `|F|² = |equations z|² / (1 + |z|²)²`.
* `flowI V t₀ y t`: the value at `t ∈ [0,1]` of the unique solution on `[0,1]` (constant
  outside) of `u' = V(s, u)` with `u(t₀) = y` (definite description `Explicit.the`).
* `transferMap a b = affineRadialTarget q (1/π) ∘ ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ radialInj b`, the ball chart
  `affineRadialTarget` being the explicit map `ζ ↦ ζ / √(π (1 + |ζ|²))`.

Everything is a formula, a derivative (`fderiv`), a definite description of a unique vector
(a linear solve) or of a unique ODE solution. The construction is generic in the number `q` of
equations and their constants `a` (it is reused in other dimensions).
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set
open OAI.PackingSufficiencySupport (Ambient openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics

/-! ### Complex structure, `d^c` and `dd^c` -/

section forms

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- Multiplication by `i`, as a real linear map. -/
def cxJ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] : F →L[ℝ] F :=
  (Complex.I • ContinuousLinearMap.id ℂ F).restrictScalars ℝ

@[simp] theorem cxJ_apply (v : F) : cxJ F v = Complex.I • v := rfl

/-- `d^c Φ = −dΦ ∘ i / (4π)`, i.e. `(2π)⁻¹ Im ∂Φ`. -/
def dcForm (Φ : F → ℝ) (y : F) : F →L[ℝ] ℝ :=
  (-(1 / (4 * Real.pi))) • (fderiv ℝ Φ y).comp (cxJ F)

/-- `dd^c Φ` (exterior derivative of `d^c Φ`). -/
def ddcForm (Φ : F → ℝ) (y : F) : F →L[ℝ] F →L[ℝ] ℝ :=
  euclideanExteriorOneForm (dcForm Φ) y

end forms

/-! ### Norms and potentials in the affine chart -/

/-- `|w|²` on `ℂ^q`. -/
def wsq {q : ℕ} (w : Fin q → ℂ) : ℝ := ∑ j, Complex.normSq (w j)

/-- `|z|²` on `Affine q = ℂ × ℂ^q`. -/
def nsq {q : ℕ} (z : Affine q) : ℝ := Complex.normSq z.1 + wsq z.2

/-- The total space of `O(2)^{⊕q}` over the affine chart, in the `Z_*²` trivialisation. -/
abbrev Tot (q : ℕ) := Affine q × (Fin q → ℂ)

/-- The Kähler potential of `Ω_b`: `log(1 + |z|²) + b log(1 + |W|²/(1 + |z|²)²)`. -/
def bundlePot {q : ℕ} (b : ℝ) (y : Tot q) : ℝ :=
  Real.log (1 + nsq y.1) + b * Real.log (1 + wsq y.2 / (1 + nsq y.1) ^ 2)

/-- `Ω_b = ω_FS + b dd^c log(1 + u)` on the total space. -/
def bundleForm {q : ℕ} (b : ℝ) : Tot q → Tot q →L[ℝ] Tot q →L[ℝ] ℝ :=
  ddcForm (bundlePot b)

/-- `log(1 + |F|²)`, `|F|² = |equations z|² / (1 + |z|²)²`. -/
def graphPot {q : ℕ} (a : Fin q → ℂ) (z : Affine q) : ℝ :=
  Real.log (1 + wsq (equations a z) / (1 + nsq z) ^ 2)

/-- The potential `log(1 + |z|²) + s b log(1 + |F|²)` of `ω_s`. -/
def returnPot {q : ℕ} (a : Fin q → ℂ) (b s : ℝ) (z : Affine q) : ℝ :=
  Real.log (1 + nsq z) + s * b * graphPot a z

/-! ### Flows on `[0,1]` -/

section flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `u` solves `u' = V(s, u)` on `[0,1]`, is constant outside `[0,1]`, and `u t₀ = y`. -/
def IsSolI (V : ℝ → E → E) (t₀ : ℝ) (y : E) (u : ℝ → E) : Prop :=
  u t₀ = y ∧ (∀ s, u s = u (max 0 (min 1 s))) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (V s (u s)) (Icc 0 1) s

open Classical in
/-- The value at `t` of the unique solution on `[0,1]` through `y` at time `t₀`
(definite description); `y` if there is none. -/
def flowI (V : ℝ → E → E) (t₀ : ℝ) (y : E) (t : ℝ) : E :=
  if hu : ∃! u : ℝ → E, IsSolI V t₀ y u then Explicit.the hu t else y

theorem flowI_eq {V : ℝ → E → E} {t₀ : ℝ} {y : E} {u : ℝ → E}
    (hu : ∃! u : ℝ → E, IsSolI V t₀ y u) (hsol : IsSolI V t₀ y u) (t : ℝ) :
    flowI V t₀ y t = u t := by
  classical
  simp only [flowI, dif_pos hu, Explicit.the_eq hu hsol]

end flow

/-! ### The four stages -/

variable {q : ℕ}

/-- The fibre coordinate `w_j = x_j + i y_j` of a point of `PlanePhase (Fin q)`. -/
def toC (x : PlanePhase (Fin q)) : Fin q → ℂ := fun j => ⟨(x j).1, (x j).2⟩

/-- The radial injection `ι_b` (cons:vtr-injection) in the `Z_*²` trivialisation:
`W = (1 + |z|²) √π w / √(b − π|w|²)`. -/
def radialInj (b : ℝ) (z : Affine q) (w : Fin q → ℂ) : Tot q :=
  (z, fun j => (((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq w) : ℝ) : ℂ) * w j)

open Classical in
/-- The `Ω_b`-orthogonal lift of `∂_T` to the family `X_T = {equations z = T W}`
(prop:vtr-transport(c)); `0` where the linear problem is not uniquely solvable. -/
def transportField (_a : Fin q → ℂ) (b : ℝ) (T : ℝ) (y : Tot q) : Tot q :=
  if h : ∃! v : Tot q, jacobian y.1 v.1 - (T : ℂ) • v.2 = y.2 ∧
      ∀ k : Tot q, jacobian y.1 k.1 - (T : ℂ) • k.2 = 0 → bundleForm b y v k = 0
  then Explicit.the h else 0

/-- The horizontal transport `τ = τ₁ : X_0 → X_1` (prop:vtr-transport(e)). -/
def transport (a : Fin q → ℂ) (b : ℝ) (y : Tot q) : Tot q :=
  flowI (transportField a b) 0 y 1

open Classical in
/-- The Moser field of `ω_s` (prop:vtr-return(c)): `ω_s(Y, ·) = −b d^c log(1 + |F|²)`. -/
def returnField (a : Fin q → ℂ) (b : ℝ) (s : ℝ) (z : Affine q) : Affine q :=
  if h : ∃! Y : Affine q, ∀ v, ddcForm (returnPot a b s) z Y v = -b * dcForm (graphPot a) z v
  then Explicit.the h else 0

/-- `ψ₁⁻¹`: the flow of the Moser field from `s = 1` back to `s = 0`. -/
def returnInv (a : Fin q → ℂ) (b : ℝ) (z : Affine q) : Affine q :=
  flowI (returnField a b) 1 z 0

/-- **The explicit vector transfer** on the model `locus a × PlanePhase (Fin q)`:
ball chart ∘ `ψ₁⁻¹` ∘ projection ∘ `τ₁` ∘ `ι_b`. -/
def transferMap (a : Fin q → ℂ) (b : ℝ) (x : Affine q × PlanePhase (Fin q)) :
    Ambient (q + 1) :=
  affineRadialTarget q (1 / Real.pi) (returnInv a b (transport a b (radialInj b x.1 (toC x.2))).1)

/-! ### Elementary identities -/

theorem wsq_nonneg (w : Fin q → ℂ) : 0 ≤ wsq w :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem nsq_nonneg (z : Affine q) : 0 ≤ nsq z :=
  add_nonneg (Complex.normSq_nonneg _) (wsq_nonneg _)

theorem one_add_nsq_pos (z : Affine q) : 0 < 1 + nsq z := by
  linarith [nsq_nonneg z]

/-- `π |w|²` is the total moment `|p| = Σ planeMoments`. -/
theorem pi_wsq_toC (x : PlanePhase (Fin q)) :
    Real.pi * wsq (toC x) = ∑ j, Real.pi * ((x j).1 ^ 2 + (x j).2 ^ 2) := by
  simp only [wsq, toC, Complex.normSq_mk, Finset.mul_sum, pow_two]

/-- The radial injection is the identity on the base. -/
@[simp] theorem radialInj_fst (b : ℝ) (z : Affine q) (w : Fin q → ℂ) :
    (radialInj b z w).1 = z := rfl

/-- The Hermitian norm of the radial image: `u = π|w|² / (b − π|w|²)` (lem:vtr-injection). -/
theorem radialInj_u {b : ℝ} (z : Affine q) (w : Fin q → ℂ) (hw : Real.pi * wsq w < b) :
    wsq (radialInj b z w).2 / (1 + nsq z) ^ 2 = Real.pi * wsq w / (b - Real.pi * wsq w) := by
  have hz := one_add_nsq_pos z
  have hb : 0 < b - Real.pi * wsq w := by linarith
  have hs : Real.sqrt (b - Real.pi * wsq w) ^ 2 = b - Real.pi * wsq w :=
    Real.sq_sqrt hb.le
  have hp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have he : wsq (radialInj b z w).2 =
      ((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq w)) ^ 2 * wsq w := by
    simp only [radialInj, wsq, Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum, pow_two]
  rw [he, div_pow, mul_pow, hs, hp]
  field_simp

/-- `transferMap` lands in the open ball of capacity one (the ball chart does). -/
theorem transferMap_mem (a : Fin q → ℂ) (b : ℝ) (x : Affine q × PlanePhase (Fin q)) :
    transferMap a b x ∈ openBall (q + 1) 1 := by
  have h := affineRadialTarget_mem q (one_div_pos.2 Real.pi_pos)
    (returnInv a b (transport a b (radialInj b x.1 (toC x.2))).1)
  rwa [mul_one_div_cancel Real.pi_ne_zero] at h

end SymplecticPacking.BranchSmall.VT
