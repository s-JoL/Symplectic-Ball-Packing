import SymplecticPacking.BranchLarge3.OAIOpen
import SymplecticPacking.Return.Flow
import SymplecticPacking.Handle.MoserFlow

/-!
# Step S8a: the explicit relative radial Moser map on the cone

Explicit version of the OpenAI theorem `Hamiltonian.exists_degree_relative_shell_maps`
(`Hopf/DegreeRelativeShell.lean`), with the shell `1/2 ≤ |z|² ≤ 2`.

On `ℂ^{n+1} = PlanePhase (Option ι)` let `Γ_s` be the cutoff degree cone primitive
`cutoffDegreePrimitive ℓ F c d χ s` (`F` = the real form of `P`, `χ` an explicit plateau, `= 1`
near the shell and compactly supported), `Ω_s = dΓ_s` and `α = Γ_1 - Γ_0 = ∂_s Γ_s`.
The explicit relative correction is
`h_t(z) = -ψ(|z_∞|²) · α(e b)(N_t(b, z_∞))`, `b = Pr z`,
where `N_t(b, u) = ι_∞ u + e y` is the `Ω_{τ t}(e b)`-orthogonal lift of the normal coordinate
`u` (`y` the unique solution of the restricted linear system, `Explicit.the`), `ψ` a plateau
equal to `1` near `0`, and `τ = smoothTransition`. The Moser field is
`V_t = τ'(t) · W_t`, `Ω_{τ t}(W_t, ·) = -(α + dh_t)` (unique solution, `Explicit.the`); it is
smooth, compactly supported, tangent to the spheres and to `{z_∞ = 0}`, and commutes with the
circle action. Its time-`1` flow `shellF` (inverse `shellG`, unique ODE solutions) pulls `Ω_1`
back to `Ω_0 = c ω₀`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3.TargetMoser

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open SymplecticPacking.Return (flow flowInv flowFrom IsSolFrom CSField plateau plateau_contDiff
  plateau_eq_one plateau_eq_zero_left plateau_eq_zero_right)
open scoped ContDiff Topology
open Function Set Filter

/-! ### Linear solves by definite description -/

section solve

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Classical in
/-- The unique `y` with `B y = l` (`0` if there is none or it is not unique). -/
def solveL (B : X →L[ℝ] X →L[ℝ] ℝ) (l : X →L[ℝ] ℝ) : X :=
  if h : ∃! y, B y = l then Explicit.the h else 0

theorem solveL_existsUnique {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) (l : X →L[ℝ] ℝ) :
    ∃! y, B y = l := by
  refine ⟨B.inverse l, hB.self_apply_inverse l, fun y hy => ?_⟩
  rw [← hy, hB.inverse_apply_self]

theorem solveL_spec {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) (l : X →L[ℝ] ℝ) :
    B (solveL B l) = l := by
  unfold solveL
  rw [dif_pos (solveL_existsUnique hB l)]
  exact Explicit.the_spec (P := fun y => B y = l) _

theorem solveL_eq {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) {l : X →L[ℝ] ℝ} {y : X}
    (hy : B y = l) : solveL B l = y :=
  (solveL_existsUnique hB l).unique (solveL_spec hB l) hy

theorem solveL_eq_inverse {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) (l : X →L[ℝ] ℝ) :
    solveL B l = B.inverse l :=
  solveL_eq hB (hB.self_apply_inverse l)

theorem solveL_zero {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) : solveL B 0 = 0 :=
  solveL_eq hB (map_zero B)

theorem solveL_smul {B : X →L[ℝ] X →L[ℝ] ℝ} (hB : B.IsInvertible) (r : ℝ) (l : X →L[ℝ] ℝ) :
    solveL B (r • l) = r • solveL B l :=
  solveL_eq hB (by rw [map_smul, solveL_spec hB])

theorem solveL_contDiff [CompleteSpace X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {B : Y → X →L[ℝ] X →L[ℝ] ℝ} {l : Y → X →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (hl : ContDiff ℝ ∞ l) (hi : ∀ y, (B y).IsInvertible) :
    ContDiff ℝ ∞ (fun y => solveL (B y) (l y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hs := ((hi y).contDiffAt_map_inverse.comp y hB.contDiffAt).clm_apply hl.contDiffAt
  apply hs.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => solveL_eq_inverse (hi z) (l z)

end solve

/-! ### Small calculus helpers -/

theorem fderiv_prod_right {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {G : ℝ × E → Y} {t : ℝ} {x : E}
    (hG : DifferentiableAt ℝ G (t, x)) (u : E) :
    fderiv ℝ G (t, x) (0, u) = fderiv ℝ (fun y => G (t, y)) x u := by
  have h : HasFDerivAt (fun y => G (t, y)) ((fderiv ℝ G (t, x)).comp
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) x :=
    hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [h.fderiv]
  simp

/-! ### Cutoffs -/

/-- Radial cutoff: `0` on `(-∞, 1/4]` and `[4, ∞)`, `1` on `[3/8, 3]`. -/
def mχ : ℝ → ℝ := plateau (1/4) (3/8) 3 4

/-- Normal cutoff: `1` on `[-1, 1]`, `0` on `[2, ∞)`. -/
def mψ : ℝ → ℝ := plateau (-2) (-1) 1 2

theorem plateau_mem {a' a b b' x : ℝ} : plateau a' a b b' x ∈ Icc (0:ℝ) 1 := by
  unfold plateau
  have h1 := Real.smoothTransition.nonneg ((x - a') / (a - a'))
  have h2 := Real.smoothTransition.le_one ((x - a') / (a - a'))
  have h3 := Real.smoothTransition.nonneg ((b' - x) / (b' - b))
  have h4 := Real.smoothTransition.le_one ((b' - x) / (b' - b))
  exact ⟨mul_nonneg h1 h3, by nlinarith⟩

theorem mχ_contDiff : ContDiff ℝ ∞ mχ := plateau_contDiff _ _ _ _

theorem mψ_contDiff : ContDiff ℝ ∞ mψ := plateau_contDiff _ _ _ _

theorem mχ_mem (x : ℝ) : mχ x ∈ Icc (0:ℝ) 1 := plateau_mem

theorem mχ_zero_near : mχ =ᶠ[𝓝 (0:ℝ)] 0 := by
  filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1/4 by norm_num)] with x hx
  exact plateau_eq_zero_left (by norm_num) (le_of_lt hx)

theorem mχ_one_near {x : ℝ} (hx : x ∈ Icc (1/2:ℝ) 2) : mχ =ᶠ[𝓝 x] 1 := by
  filter_upwards [Ioo_mem_nhds (show (3/8:ℝ) < x by linarith [hx.1])
    (show x < 3 by linarith [hx.2])] with y hy
  exact plateau_eq_one (by norm_num) (by norm_num) hy.1.le hy.2.le

theorem mχ_eq_zero_of_le {x : ℝ} (hx : 4 ≤ x) : mχ x = 0 :=
  plateau_eq_zero_right (by norm_num) hx

theorem mψ_zero : mψ 0 = 1 := plateau_eq_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem mψ_eq_zero_of_le {x : ℝ} (hx : 2 ≤ x) : mψ x = 0 :=
  plateau_eq_zero_right (by norm_num) hx

/-! ### The normal coordinate -/

section normal

variable {ι : Type} [Fintype ι]

/-- Squared length in the plane. -/
def nsq (u : ℝ × ℝ) : ℝ := u.1 * u.1 + u.2 * u.2

/-- Inclusion of the normal (`none`) coordinate. -/
def ιN : (ℝ × ℝ) →L[ℝ] PlanePhase (Option ι) :=
  (phaseOptionSplit (ι := ι)).toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)

@[simp] theorem ιN_none (u : ℝ × ℝ) : ιN (ι := ι) u none = u := rfl

@[simp] theorem ιN_some (u : ℝ × ℝ) (i : ι) : ιN (ι := ι) u (some i) = 0 := rfl

@[simp] theorem phaseInfinityProjection_apply' (z : PlanePhase (Option ι)) (i : ι) :
    phaseInfinityProjection z i = z (some i) := rfl

@[simp] theorem proj_ιN (u : ℝ × ℝ) : phaseInfinityProjection (ιN (ι := ι) u) = 0 := rfl

@[simp] theorem proj_incl (b : PlanePhase ι) :
    phaseInfinityProjection (phaseInfinityInclusion b) = b := rfl

theorem decomp (z : PlanePhase (Option ι)) :
    z = phaseInfinityInclusion (phaseInfinityProjection z) + ιN (z none) := by
  funext j
  cases j with
  | none => simp
  | some i => simp

/-- Planar rotation, the `none`-component of `phaseRotate`. -/
def rp (s : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := Real.cos s • u + Real.sin s • (-u.2, u.1)

theorem rotate_none (s : ℝ) (z : PlanePhase (Option ι)) :
    phaseRotate s z none = rp s (z none) := by
  simp [phaseRotate_apply, rp]

theorem rotate_ιN (s : ℝ) (u : ℝ × ℝ) : phaseRotate s (ιN (ι := ι) u) = ιN (rp s u) := by
  funext j
  cases j with
  | none => simp [phaseRotate_apply, rp]
  | some i => simp [phaseRotate_apply]

theorem rotate_incl (s : ℝ) (b : PlanePhase ι) :
    phaseRotate s (phaseInfinityInclusion b) = phaseInfinityInclusion (phaseRotate s b) := by
  funext j
  cases j with
  | none => simp [phaseRotate_apply]
  | some i => simp [phaseRotate_apply]

theorem proj_rotate (s : ℝ) (z : PlanePhase (Option ι)) :
    phaseInfinityProjection (phaseRotate s z) = phaseRotate s (phaseInfinityProjection z) := by
  funext i
  simp [phaseRotate_apply]

theorem nsq_rp (s : ℝ) (u : ℝ × ℝ) : nsq (rp s u) = nsq u := by
  simp only [nsq, rp, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (u.1 * u.1 + u.2 * u.2) * Real.sin_sq_add_cos_sq s

theorem rotate_neg_cancel (s : ℝ) {V : Type} [Fintype V] (z : PlanePhase V) :
    phaseRotate s (phaseRotate (-s) z) = z := by
  rw [← phaseRotate_add]; simp

end normal


/-! ### The explicit data -/

section defs

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ) (c d : ℝ)

/-- The cutoff degree cone primitive `Γ_s`. -/
def mΓ (s : ℝ) : PlanePhase (Option ι) → PlanePhase (Option ι) →L[ℝ] ℝ :=
  cutoffDegreePrimitive (ℓ : ℝ) (cartesianConjugate P) c d mχ s

/-- `α = ∂_s Γ_s = Γ_1 - Γ_0`. -/
def mα (z : PlanePhase (Option ι)) : PlanePhase (Option ι) →L[ℝ] ℝ :=
  mΓ P ℓ c d 1 z - mΓ P ℓ c d 0 z

/-- `Ω_s = dΓ_s`. -/
def mΩ (s : ℝ) (z : PlanePhase (Option ι)) :
    PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ :=
  euclideanExteriorOneForm (mΓ P ℓ c d s) z

/-- `Ω_{τ t}` restricted to the hyperplane at infinity `{z_∞ = 0}`, at `e b`. -/
def mRes (t : ℝ) (b : PlanePhase ι) : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  (mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b)).bilinearComp
    phaseInfinityInclusion phaseInfinityInclusion

/-- Tangential part of the `Ω_{τ t}(e b)`-orthogonal lift of the normal vector `u`. -/
def mY (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) : PlanePhase ι :=
  solveL (mRes P ℓ c d t b)
    (-((mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b) (ιN u)).comp
      phaseInfinityInclusion))

/-- The `Ω_{τ t}(e b)`-orthogonal lift of the normal vector `u`. -/
def mN (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) : PlanePhase (Option ι) :=
  ιN u + phaseInfinityInclusion (mY P ℓ c d t b u)

/-- The relative correction potential `h_t`. -/
def mh (t : ℝ) (z : PlanePhase (Option ι)) : ℝ :=
  -(mψ (nsq (z none)) * mα P ℓ c d (phaseInfinityInclusion (phaseInfinityProjection z))
      (mN P ℓ c d t (phaseInfinityProjection z) (z none)))

/-- The corrected primitive `β_t = α + dh_t`. -/
def mβ (t : ℝ) (z : PlanePhase (Option ι)) : PlanePhase (Option ι) →L[ℝ] ℝ :=
  mα P ℓ c d z + fderiv ℝ (mh P ℓ c d t) z

/-- The Moser vector `Ω_{τ t}(W, ·) = -β_t`. -/
def mW (t : ℝ) (z : PlanePhase (Option ι)) : PlanePhase (Option ι) :=
  solveL (mΩ P ℓ c d (Real.smoothTransition t) z) (-mβ P ℓ c d t z)

/-- The reparametrised Moser field `V_t = τ'(t) W_t`. -/
def mV (t : ℝ) (z : PlanePhase (Option ι)) : PlanePhase (Option ι) :=
  deriv Real.smoothTransition t • mW P ℓ c d t z

/-- The explicit relative radial Moser map (time-`1` flow). -/
def shellF : PlanePhase (Option ι) → PlanePhase (Option ι) := flow (mV P ℓ c d) 1

/-- Its inverse (time-`1` backward flow). -/
def shellG : PlanePhase (Option ι) → PlanePhase (Option ι) := flowInv (mV P ℓ c d) 1

end defs

/-! ### Hypotheses -/

structure Hyp {ι κ : Type} [Fintype ι] [Fintype κ] (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ)
    (c d : ℝ) : Prop where
  hP : ContDiff ℂ ∞ P
  hPn : ∀ z, z ≠ 0 → P z ≠ 0
  hPs : ∀ (ζ : ℂ) z, P (ζ • z) = ζ ^ ℓ • P z
  hc : 0 < c
  hd : 0 ≤ d
  hdℓ : (ℓ : ℝ) * d < 1

section basic

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

theorem Hyp.F_smooth : ContDiff ℝ ∞ (cartesianConjugate P) :=
  cartesianConjugate_smooth (H.hP.restrict_scalars ℝ)

theorem Hyp.F0 : ∀ z, z ≠ 0 → cartesianConjugate P z ≠ 0 :=
  fun _ hz => cartesianConjugate_nonzero H.hPn hz

theorem Hyp.FD : ∀ z, fderiv ℝ (cartesianConjugate P) z z = (ℓ : ℝ) • cartesianConjugate P z :=
  cartesianConjugate_euler H.hP H.hPs

theorem Hyp.FJ : ∀ z v, fderiv ℝ (cartesianConjugate P) z (phaseJ v) =
    phaseJ (fderiv ℝ (cartesianConjugate P) z v) :=
  cartesianConjugate_J H.hP

theorem Hyp.FDJ (z : PlanePhase (Option ι)) :
    fderiv ℝ (cartesianConjugate P) z (phaseJ z) = (ℓ : ℝ) • phaseJ (cartesianConjugate P z) := by
  rw [H.FJ, H.FD, map_smul]

theorem Hyp.Frot (s : ℝ) (z : PlanePhase (Option ι)) :
    cartesianConjugate P (phaseRotate s z) = phaseRotate ((ℓ : ℝ) * s) (cartesianConjugate P z) :=
  euler_circle_equivariant H.F_smooth H.FD H.FJ s z

theorem Hyp.Γ_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mΓ P ℓ c d p.1 p.2) :=
  cutoffDegreePrimitive_smooth H.F_smooth H.F0 mχ_contDiff mχ_zero_near _ c d

theorem Hyp.Γ_slice (s : ℝ) : ContDiff ℝ ∞ (mΓ P ℓ c d s) :=
  cutoffDegreePrimitive_slice_smooth H.F_smooth H.F0 mχ_contDiff mχ_zero_near _ c d s

theorem Hyp.α_smooth : ContDiff ℝ ∞ (mα P ℓ c d) := (H.Γ_slice 1).sub (H.Γ_slice 0)

omit H in
theorem mΓ_eq (s : ℝ) : mΓ P ℓ c d s = mΓ P ℓ c d 0 + s • mα P ℓ c d := by
  funext z
  simp only [mΓ, mα, cutoffDegreePrimitive, Pi.add_apply, Pi.smul_apply]
  module

theorem Hyp.Ω_eq (s : ℝ) (z : PlanePhase (Option ι)) :
    mΩ P ℓ c d s z = euclideanExteriorOneForm (mΓ P ℓ c d 0) z +
      s • euclideanExteriorOneForm (mα P ℓ c d) z := by
  have h0 := (H.Γ_slice 0).differentiable (by simp) z
  have h1 := (H.α_smooth).differentiable (by simp) z
  rw [mΩ, mΓ_eq, euclideanExteriorOneForm_add h0 (h1.const_smul s),
    euclideanExteriorOneForm_smul s h1]

theorem Hyp.Ω_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mΩ P ℓ c d p.1 p.2) := by
  have hf : ContDiff ℝ ∞ (fun x : (ℝ × PlanePhase (Option ι)) × PlanePhase (Option ι) =>
      mΓ P ℓ c d x.1.1 x.2) := by
    have h2 : ContDiff ℝ ∞ (fun x : (ℝ × PlanePhase (Option ι)) × PlanePhase (Option ι) =>
        (x.1.1, x.2)) := contDiff_fst.fst.prodMk contDiff_snd
    exact ContDiff.comp (g := fun p : ℝ × PlanePhase (Option ι) => mΓ P ℓ c d p.1 p.2)
      (f := fun x : (ℝ × PlanePhase (Option ι)) × PlanePhase (Option ι) => (x.1.1, x.2))
      H.Γ_smooth h2
  have hd : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => fderiv ℝ (mΓ P ℓ c d p.1) p.2) :=
    ContDiff.fderiv (m := ∞) (n := ∞)
      (f := fun (p : ℝ × PlanePhase (Option ι)) (y : PlanePhase (Option ι)) => mΓ P ℓ c d p.1 y)
      (g := Prod.snd) hf contDiff_snd (by simp)
  have hflip : ContDiff ℝ ∞ (fun L : PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ =>
      L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞)
      (E := PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ)
      (F := PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ)
      (ContinuousLinearMap.flipₗᵢ ℝ (PlanePhase (Option ι)) (PlanePhase (Option ι)) ℝ)
  exact hd.sub (hflip.comp hd)

theorem Hyp.Ω_inv {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (z : PlanePhase (Option ι)) :
    (mΩ P ℓ c d s z).IsInvertible :=
  cutoffDegreePrimitive_nondegenerate H.F_smooth H.F0 H.FD H.FJ mχ_contDiff mχ_zero_near mχ_mem
    H.hc H.hd (Nat.cast_nonneg ℓ) H.hdℓ hs z

omit H in
theorem τ_mem (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

theorem Hyp.Res_inv (t : ℝ) (b : PlanePhase ι) : (mRes P ℓ c d t b).IsInvertible := by
  have h := cutoffDegreeForm_subspace_nondegenerate H.F_smooth H.F0 H.FD H.FJ
    phaseInfinityInclusion phaseInfinity_dot phaseInfinity_area phaseInfinity_J mχ_contDiff
    mχ_zero_near mχ_mem H.hc H.hd (Nat.cast_nonneg ℓ) H.hdℓ (τ_mem t) b
  rw [vector_exteriorOneForm] at h
  exact h

end basic


/-! ### Smoothness of the data -/

theorem bilinearComp_contDiff {Y X Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {B : Y → X →L[ℝ] X →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B) (f : Z →L[ℝ] X) :
    ContDiff ℝ ∞ (fun y => (B y).bilinearComp f f) := by
  have he : (fun y => (B y).bilinearComp f f) =
      fun y => ((ContinuousLinearMap.compL ℝ Z X ℝ).flip f).comp ((B y).comp f) := by
    funext y; ext u v; rfl
  rw [he]
  exact contDiff_const.clm_comp (hB.clm_comp contDiff_const)

theorem nsq_contDiff : ContDiff ℝ ∞ nsq := by
  unfold nsq
  exact (contDiff_fst.mul contDiff_fst).add (contDiff_snd.mul contDiff_snd)

theorem cdc {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (g : Y → Z) (f : X → Y)
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => g (f x)) :=
  hg.comp hf

section smooth

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

theorem Hyp.Ωτ_smooth : ContDiff ℝ ∞
    (fun p : ℝ × PlanePhase (Option ι) => mΩ P ℓ c d (Real.smoothTransition p.1) p.2) :=
  cdc (fun p : ℝ × PlanePhase (Option ι) => mΩ P ℓ c d p.1 p.2)
    (fun p : ℝ × PlanePhase (Option ι) => (Real.smoothTransition p.1, p.2)) H.Ω_smooth
    ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)

theorem Hyp.Res_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => mRes P ℓ c d p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι =>
      mΩ P ℓ c d (Real.smoothTransition p.1) (phaseInfinityInclusion p.2)) :=
    cdc (fun p : ℝ × PlanePhase (Option ι) => mΩ P ℓ c d (Real.smoothTransition p.1) p.2)
      (fun p : ℝ × PlanePhase ι => (p.1, phaseInfinityInclusion p.2)) H.Ωτ_smooth
      (contDiff_fst.prodMk ((phaseInfinityInclusion (ι := ι)).contDiff.comp contDiff_snd))
  exact bilinearComp_contDiff h phaseInfinityInclusion

theorem Hyp.Y_smooth : ContDiff ℝ ∞
    (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => mY P ℓ c d p.1 p.2.1 p.2.2) := by
  have hB : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => mRes P ℓ c d p.1 p.2.1) :=
    cdc (fun p : ℝ × PlanePhase ι => mRes P ℓ c d p.1 p.2)
      (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => (p.1, p.2.1)) H.Res_smooth
      (contDiff_fst.prodMk contDiff_snd.fst)
  have hΩ : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) =>
      mΩ P ℓ c d (Real.smoothTransition p.1) (phaseInfinityInclusion p.2.1)) :=
    cdc (fun p : ℝ × PlanePhase (Option ι) => mΩ P ℓ c d (Real.smoothTransition p.1) p.2)
      (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => (p.1, phaseInfinityInclusion p.2.1)) H.Ωτ_smooth
      (contDiff_fst.prodMk ((phaseInfinityInclusion (ι := ι)).contDiff.comp contDiff_snd.fst))
  have hι : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => ιN (ι := ι) p.2.2) :=
    cdc (ιN (ι := ι)) (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => p.2.2) (ιN (ι := ι)).contDiff
      contDiff_snd.snd
  have hl : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) =>
      -((mΩ P ℓ c d (Real.smoothTransition p.1) (phaseInfinityInclusion p.2.1)
        (ιN p.2.2)).comp phaseInfinityInclusion)) :=
    ((hΩ.clm_apply hι).clm_comp contDiff_const).neg
  exact solveL_contDiff hB hl (fun p => H.Res_inv p.1 p.2.1)

theorem Hyp.N_smooth : ContDiff ℝ ∞
    (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => mN P ℓ c d p.1 p.2.1 p.2.2) := by
  have hι : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => ιN (ι := ι) p.2.2) :=
    cdc (ιN (ι := ι)) (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => p.2.2) (ιN (ι := ι)).contDiff
      contDiff_snd.snd
  have hY : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) =>
      phaseInfinityInclusion (mY P ℓ c d p.1 p.2.1 p.2.2)) :=
    cdc (phaseInfinityInclusion (ι := ι)) (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) =>
      mY P ℓ c d p.1 p.2.1 p.2.2) (phaseInfinityInclusion (ι := ι)).contDiff H.Y_smooth
  exact hι.add hY

theorem Hyp.h_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mh P ℓ c d p.1 p.2) := by
  have hnone : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => p.2 none) :=
    cdc (fun z : PlanePhase (Option ι) => z none) Prod.snd
      (contDiff_apply ℝ (ℝ × ℝ) (none : Option ι)) contDiff_snd
  have hpr : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => phaseInfinityProjection p.2) :=
    cdc (phaseInfinityProjection (ι := ι)) Prod.snd (phaseInfinityProjection (ι := ι)).contDiff
      contDiff_snd
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mψ (nsq (p.2 none))) :=
    cdc mψ (fun p : ℝ × PlanePhase (Option ι) => nsq (p.2 none)) mψ_contDiff
      (cdc nsq (fun p : ℝ × PlanePhase (Option ι) => p.2 none) nsq_contDiff hnone)
  have hα : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) =>
      mα P ℓ c d (phaseInfinityInclusion (phaseInfinityProjection p.2))) :=
    cdc (mα P ℓ c d) (fun p : ℝ × PlanePhase (Option ι) =>
      phaseInfinityInclusion (phaseInfinityProjection p.2)) H.α_smooth
      (cdc (phaseInfinityInclusion (ι := ι)) (fun p : ℝ × PlanePhase (Option ι) =>
        phaseInfinityProjection p.2) (phaseInfinityInclusion (ι := ι)).contDiff hpr)
  have hN : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) =>
      mN P ℓ c d p.1 (phaseInfinityProjection p.2) (p.2 none)) :=
    cdc (fun p : ℝ × PlanePhase ι × (ℝ × ℝ) => mN P ℓ c d p.1 p.2.1 p.2.2)
      (fun p : ℝ × PlanePhase (Option ι) => (p.1, phaseInfinityProjection p.2, p.2 none))
      H.N_smooth (contDiff_fst.prodMk (hpr.prodMk hnone))
  exact (hψ.mul (hα.clm_apply hN)).neg

theorem Hyp.h_slice (t : ℝ) : ContDiff ℝ ∞ (mh P ℓ c d t) :=
  cdc (fun p : ℝ × PlanePhase (Option ι) => mh P ℓ c d p.1 p.2)
    (fun z : PlanePhase (Option ι) => (t, z)) H.h_smooth (contDiff_const.prodMk contDiff_id)

theorem Hyp.β_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mβ P ℓ c d p.1 p.2) := by
  have hf : ContDiff ℝ ∞ (fun x : (ℝ × PlanePhase (Option ι)) × PlanePhase (Option ι) =>
      mh P ℓ c d x.1.1 x.2) :=
    cdc (fun p : ℝ × PlanePhase (Option ι) => mh P ℓ c d p.1 p.2)
      (fun x : (ℝ × PlanePhase (Option ι)) × PlanePhase (Option ι) => (x.1.1, x.2))
      H.h_smooth (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => fderiv ℝ (mh P ℓ c d p.1) p.2) :=
    ContDiff.fderiv (m := ∞) (n := ∞)
      (f := fun (p : ℝ × PlanePhase (Option ι)) (y : PlanePhase (Option ι)) => mh P ℓ c d p.1 y)
      (g := Prod.snd) hf contDiff_snd (by simp)
  have ha : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mα P ℓ c d p.2) :=
    cdc (mα P ℓ c d) Prod.snd H.α_smooth contDiff_snd
  exact ha.add hd

theorem Hyp.W_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mW P ℓ c d p.1 p.2) :=
  solveL_contDiff H.Ωτ_smooth H.β_smooth.neg (fun p => H.Ω_inv (τ_mem p.1) p.2)

omit H in
theorem τ'_smooth : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

theorem Hyp.V_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option ι) => mV P ℓ c d p.1 p.2) :=
  (cdc (deriv Real.smoothTransition) Prod.fst τ'_smooth contDiff_fst).smul H.W_smooth

end smooth


/-! ### Support and the Moser equation -/

section support

variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem phaseSq_split (z : PlanePhase (Option ι)) :
    phaseSq z = phaseSq (phaseInfinityProjection z) + nsq (z none) := by
  simp only [phaseSq, phaseDot_apply, Fintype.sum_option, nsq, phaseInfinityProjection_apply']
  ring

omit [Fintype κ] in
theorem phaseSq_incl (b : PlanePhase ι) : phaseSq (phaseInfinityInclusion b) = phaseSq b :=
  phaseInfinity_dot b b

variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ}

theorem mα_zero {z : PlanePhase (Option ι)} (hz : 4 ≤ phaseSq z) : mα P ℓ c d z = 0 := by
  simp only [mα, mΓ, cutoffDegreePrimitive, mχ_eq_zero_of_le hz, mul_zero, zero_smul, add_zero,
    sub_self]

theorem mh_zero (t : ℝ) {z : PlanePhase (Option ι)} (hz : 6 < phaseSq z) : mh P ℓ c d t z = 0 := by
  unfold mh
  by_cases hn : 2 ≤ nsq (z none)
  · rw [mψ_eq_zero_of_le hn, zero_mul, neg_zero]
  · have h4 : 4 ≤ phaseSq (phaseInfinityInclusion (phaseInfinityProjection z)) := by
      rw [phaseSq_incl]; rw [phaseSq_split] at hz; linarith
    rw [mα_zero h4]; simp

theorem mh_ev_zero (t : ℝ) {z : PlanePhase (Option ι)} (hz : 6 < phaseSq z) :
    mh P ℓ c d t =ᶠ[𝓝 z] 0 := by
  have ho : IsOpen {y : PlanePhase (Option ι) | 6 < phaseSq y} :=
    isOpen_lt continuous_const phaseSq_smooth.continuous
  filter_upwards [ho.mem_nhds hz] with y hy
  exact mh_zero t hy

theorem mβ_zero (t : ℝ) {z : PlanePhase (Option ι)} (hz : 6 < phaseSq z) : mβ P ℓ c d t z = 0 := by
  rw [mβ, mα_zero (by linarith), (mh_ev_zero t hz).fderiv_eq]
  simp

theorem τ'_zero {t : ℝ} (ht : t ∉ Icc (0:ℝ) 1) : deriv Real.smoothTransition t = 0 := by
  rcases not_and_or.mp ht with h | h
  · push Not at h
    have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [he.deriv_eq, deriv_const]
  · push Not at h
    have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [he.deriv_eq, deriv_const]

variable (H : Hyp P ℓ c d)
include H

theorem Hyp.W_zero (t : ℝ) {z : PlanePhase (Option ι)} (hz : 6 < phaseSq z) :
    mW P ℓ c d t z = 0 := by
  rw [mW, mβ_zero t hz, neg_zero, solveL_zero (H.Ω_inv (τ_mem t) z)]

theorem Hyp.V_zero {t : ℝ} {z : PlanePhase (Option ι)}
    (h : t ∉ Icc (0:ℝ) 1 ∨ 6 < phaseSq z) : mV P ℓ c d t z = 0 := by
  rcases h with h | h
  · rw [mV, τ'_zero h, zero_smul]
  · rw [mV, H.W_zero t h, smul_zero]

theorem Hyp.V_cs : CSField (mV P ℓ c d) := by
  refine ⟨H.V_smooth, HasCompactSupport.intro ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod (phaseShell_isCompact 0 6)) ?_⟩
  intro p hp
  apply H.V_zero
  by_contra hc
  push Not at hc
  exact hp ⟨hc.1, phaseSq_nonneg p.2, hc.2⟩

theorem Hyp.V_lfield : SymplecticPacking.Handle.LField (mV P ℓ c d) :=
  ⟨H.V_smooth, H.V_cs.lipschitz, H.V_cs.time_bound⟩

/-- The Moser equation `Ω_{τ t}(W_t, ·) = -β_t`. -/
theorem Hyp.W_eq (t : ℝ) (z : PlanePhase (Option ι)) :
    mΩ P ℓ c d (Real.smoothTransition t) z (mW P ℓ c d t z) = -mβ P ℓ c d t z :=
  solveL_spec (H.Ω_inv (τ_mem t) z) _

end support


/-! ### The transport equation and form preservation -/

/-- The time-dependent form `(t, x) ↦ Ω_{τ t}(x)`. -/
def Ωt {ι κ : Type} [Fintype ι] [Fintype κ] (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ) (c d : ℝ)
    (q : ℝ × PlanePhase (Option ι)) :
    PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ :=
  mΩ P ℓ c d (Real.smoothTransition q.1) q.2

/-- The time-dependent primitive `(t, x) ↦ τ'(t) β_t(x)`. -/
def αt {ι κ : Type} [Fintype ι] [Fintype κ] (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ) (c d : ℝ)
    (q : ℝ × PlanePhase (Option ι)) : PlanePhase (Option ι) →L[ℝ] ℝ :=
  deriv Real.smoothTransition q.1 • mβ P ℓ c d q.1 q.2

section transport

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

omit H in
theorem mΩ_skew (s : ℝ) (z u v : PlanePhase (Option ι)) :
    mΩ P ℓ c d s z u v = -mΩ P ℓ c d s z v u := by
  simp only [mΩ, euclideanExteriorOneForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem Hyp.β_slice (t : ℝ) : ContDiff ℝ ∞ (mβ P ℓ c d t) :=
  cdc (fun p : ℝ × PlanePhase (Option ι) => mβ P ℓ c d p.1 p.2)
    (fun z : PlanePhase (Option ι) => (t, z)) H.β_smooth (contDiff_const.prodMk contDiff_id)

theorem Hyp.Ωτ_time (t : ℝ) (x v w : PlanePhase (Option ι)) :
    HasDerivAt (fun s => mΩ P ℓ c d (Real.smoothTransition s) x v w)
      (deriv Real.smoothTransition t * euclideanExteriorOneForm (mα P ℓ c d) x v w) t := by
  have he : (fun s => mΩ P ℓ c d (Real.smoothTransition s) x v w) = fun s =>
      euclideanExteriorOneForm (mΓ P ℓ c d 0) x v w +
        Real.smoothTransition s * euclideanExteriorOneForm (mα P ℓ c d) x v w := by
    funext s
    rw [H.Ω_eq]
    rfl
  rw [he]
  have hτ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) t).hasDerivAt
  exact (hτ.mul_const (euclideanExteriorOneForm (mα P ℓ c d) x v w)).const_add
    (euclideanExteriorOneForm (mΓ P ℓ c d 0) x v w)

theorem Hyp.PDE (p : ℝ × PlanePhase (Option ι)) (v w : PlanePhase (Option ι)) :
    fderiv ℝ (Ωt P ℓ c d) p (1, mV P ℓ c d p.1 p.2) v w +
      Ωt P ℓ c d p (fderiv ℝ (fun q : ℝ × PlanePhase (Option ι) => mV P ℓ c d q.1 q.2) p (0, v)) w +
      Ωt P ℓ c d p v
        (fderiv ℝ (fun q : ℝ × PlanePhase (Option ι) => mV P ℓ c d q.1 q.2) p (0, w)) = 0 := by
  obtain ⟨t, x⟩ := p
  have hΩd : DifferentiableAt ℝ (Ωt P ℓ c d) (t, x) :=
    H.Ωτ_smooth.differentiable (by simp) _
  have hαs : ContDiff ℝ ∞ (αt P ℓ c d) :=
    (cdc (deriv Real.smoothTransition) Prod.fst τ'_smooth contDiff_fst).smul H.β_smooth
  have hαd : DifferentiableAt ℝ (αt P ℓ c d) (t, x) := hαs.differentiable (by simp) _
  have hXd : DifferentiableAt ℝ (fun q : ℝ × PlanePhase (Option ι) => mV P ℓ c d q.1 q.2) (t, x) :=
    H.V_smooth.differentiable (by simp) _
  apply local_moser_transport_equation hΩd hαd hXd
  · refine Eventually.of_forall fun q => ?_
    simp only [Ωt, αt, mV, map_smul, H.W_eq, smul_neg]
  · intro u v; exact mΩ_skew _ _ _ _
  · intro u v w
    have key : ∀ u, fderiv ℝ (Ωt P ℓ c d) (t, x) (0, u) =
        fderiv ℝ (fun y => Ωt P ℓ c d (t, y)) x u :=
      fun u => fderiv_prod_right
        (Y := PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ) (G := Ωt P ℓ c d) hΩd u
    erw [key u, key v, key w]
    exact euclideanExteriorOneForm_closed (H.Γ_slice (Real.smoothTransition t)) x u v w
  · intro v w
    have h1 : HasDerivAt (fun s => Ωt P ℓ c d (s, x)) (fderiv ℝ (Ωt P ℓ c d) (t, x) (1, 0)) t :=
      HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ × PlanePhase (Option ι))
        (E := PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ)
        (l := Ωt P ℓ c d) (f := fun s : ℝ => (s, x)) (x := t) hΩd.hasFDerivAt
        ((hasDerivAt_id' (x := t)).prodMk (hasDerivAt_const t x))
    have h2 : HasDerivAt (fun s => Ωt P ℓ c d (s, x) v w)
        (fderiv ℝ (Ωt P ℓ c d) (t, x) (1, 0) v w) t := by
      have h := (h1.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
      simpa using h
    have h3 : fderiv ℝ (Ωt P ℓ c d) (t, x) (1, 0) v w =
        deriv Real.smoothTransition t * euclideanExteriorOneForm (mα P ℓ c d) x v w :=
      h2.unique (H.Ωτ_time t x v w)
    have key : ∀ u, fderiv ℝ (αt P ℓ c d) (t, x) (0, u) =
        fderiv ℝ (fun y => αt P ℓ c d (t, y)) x u :=
      fun u => fderiv_prod_right (Y := PlanePhase (Option ι) →L[ℝ] ℝ) (G := αt P ℓ c d) hαd u
    erw [h3, key v, key w]
    have hβd : DifferentiableAt ℝ (mβ P ℓ c d t) x := (H.β_slice t).differentiable (by simp) x
    have hαd' : DifferentiableAt ℝ (mα P ℓ c d) x := H.α_smooth.differentiable (by simp) x
    have hhd : DifferentiableAt ℝ (fderiv ℝ (mh P ℓ c d t)) x :=
      ((H.h_slice t).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hfs : (fun y => αt P ℓ c d (t, y)) =
        fun y => deriv Real.smoothTransition t • mβ P ℓ c d t y := rfl
    rw [hfs, fderiv_fun_const_smul hβd]
    have hβe : mβ P ℓ c d t = fun y => mα P ℓ c d y + fderiv ℝ (mh P ℓ c d t) y := rfl
    rw [hβe, fderiv_fun_add hαd' hhd]
    have hs := ((H.h_slice t).contDiffAt (x := x)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
      euclideanExteriorOneForm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply]
    rw [hs.eq v w]
    ring

/-- `φ_t^* Ω_{τ t} = Ω_0` for the explicit flow. -/
theorem Hyp.flow_form (t : ℝ) (x v w : PlanePhase (Option ι)) :
    mΩ P ℓ c d (Real.smoothTransition t) (flow (mV P ℓ c d) t x)
        (fderiv ℝ (flow (mV P ℓ c d) t) x v) (fderiv ℝ (flow (mV P ℓ c d) t) x w) =
      mΩ P ℓ c d (Real.smoothTransition 0) x v w :=
  H.V_lfield.flow_preserves_form (Ωt P ℓ c d) H.Ωτ_smooth (fun p v w => H.PDE p v w) t x v w

end transport


/-! ### Circle invariance -/

section circle

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

theorem Hyp.Γ_rot (s r : ℝ) (z v : PlanePhase (Option ι)) :
    mΓ P ℓ c d s (phaseRotate r z) (phaseRotate r v) = mΓ P ℓ c d s z v :=
  cutoffDegreePrimitive_rotate H.F_smooth H.Frot c d mχ s r z v

theorem Hyp.α_rot (r : ℝ) (z v : PlanePhase (Option ι)) :
    mα P ℓ c d (phaseRotate r z) (phaseRotate r v) = mα P ℓ c d z v := by
  simp only [mα, ContinuousLinearMap.sub_apply, H.Γ_rot]

theorem Hyp.Ω_rot (s r : ℝ) (z v w : PlanePhase (Option ι)) :
    mΩ P ℓ c d s (phaseRotate r z) (phaseRotate r v) (phaseRotate r w) = mΩ P ℓ c d s z v w :=
  exterior_linear_invariant (α := mΓ P ℓ c d s) (z := z) (phaseRotate r)
    ((H.Γ_slice s).contDiffAt) (fun x v => H.Γ_rot s r x v) v w

theorem Hyp.Y_rot (t r : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) :
    mY P ℓ c d t (phaseRotate r b) (rp r u) = phaseRotate r (mY P ℓ c d t b u) := by
  apply solveL_eq (H.Res_inv t _)
  have hy := solveL_spec (H.Res_inv t b)
    (-((mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b) (ιN u)).comp
      phaseInfinityInclusion))
  ext y'
  have h1 := congrArg (fun L => L (phaseRotate (-r) y')) hy
  simp only [mRes, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply] at h1 ⊢
  have hy' : y' = phaseRotate r (phaseRotate (-r) y') := (rotate_neg_cancel r y').symm
  rw [hy', ← rotate_incl r (phaseRotate (-r) y'), ← rotate_incl r b,
    ← rotate_incl r (mY P ℓ c d t b u), ← rotate_ιN, H.Ω_rot, H.Ω_rot]
  exact h1

theorem Hyp.N_rot (t r : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) :
    mN P ℓ c d t (phaseRotate r b) (rp r u) = phaseRotate r (mN P ℓ c d t b u) := by
  simp only [mN, H.Y_rot, map_add, rotate_ιN, rotate_incl]

theorem Hyp.h_rot (t r : ℝ) (z : PlanePhase (Option ι)) :
    mh P ℓ c d t (phaseRotate r z) = mh P ℓ c d t z := by
  have hN := H.N_rot t r (phaseInfinityProjection z) (z none)
  simp only [mh, rotate_none, nsq_rp, proj_rotate, hN, ← rotate_incl, H.α_rot]

theorem Hyp.dh_rot (t r : ℝ) (z v : PlanePhase (Option ι)) :
    fderiv ℝ (mh P ℓ c d t) (phaseRotate r z) (phaseRotate r v) = fderiv ℝ (mh P ℓ c d t) z v := by
  have hfun : (mh P ℓ c d t) ∘ (phaseRotate r) = mh P ℓ c d t := funext (H.h_rot t r)
  have hd := (H.h_slice t).differentiable (by simp) (phaseRotate r z)
  have hc := fderiv_comp z hd (phaseRotate r).differentiableAt
  rw [hfun, (phaseRotate r).fderiv] at hc
  rw [hc]
  rfl

theorem Hyp.β_rot (t r : ℝ) (z v : PlanePhase (Option ι)) :
    mβ P ℓ c d t (phaseRotate r z) (phaseRotate r v) = mβ P ℓ c d t z v := by
  simp only [mβ, ContinuousLinearMap.add_apply, H.α_rot, H.dh_rot]

theorem Hyp.W_rot (t r : ℝ) (z : PlanePhase (Option ι)) :
    mW P ℓ c d t (phaseRotate r z) = phaseRotate r (mW P ℓ c d t z) := by
  apply solveL_eq (H.Ω_inv (τ_mem t) _)
  ext w
  have h1 := congrArg (fun L => L (phaseRotate (-r) w)) (H.W_eq t z)
  simp only [ContinuousLinearMap.neg_apply] at h1 ⊢
  have hw : w = phaseRotate r (phaseRotate (-r) w) := (rotate_neg_cancel r w).symm
  rw [hw, H.Ω_rot, H.β_rot]
  exact h1

theorem Hyp.V_rot (t r : ℝ) (z : PlanePhase (Option ι)) :
    mV P ℓ c d t (phaseRotate r z) = phaseRotate r (mV P ℓ c d t z) := by
  simp only [mV, H.W_rot, map_smul]

/-! ### Tangency to the spheres -/

theorem Hyp.α_J (z : PlanePhase (Option ι)) : mα P ℓ c d z (phaseJ z) = 0 := by
  by_cases hz : z = 0
  · subst hz; simp
  · simp [mα, mΓ, cutoffDegreePrimitive, degreeHopfDifference_circle hz (H.F0 z hz) (H.FDJ z) c]

theorem Hyp.dh_J (t : ℝ) (z : PlanePhase (Option ι)) :
    fderiv ℝ (mh P ℓ c d t) z (phaseJ z) = 0 := by
  have hd := (H.h_slice t).differentiable (by simp) z
  have hl : HasFDerivAt (mh P ℓ c d t) (fderiv ℝ (mh P ℓ c d t) z) (phaseRotate 0 z) := by
    rw [phaseRotate_zero]; exact hd.hasFDerivAt
  have h1 := HasFDerivAt.comp_hasDerivAt (l := mh P ℓ c d t) (f := fun s => phaseRotate s z)
    (x := (0:ℝ)) hl (phaseRotate_hasDerivAt 0 z)
  rw [phaseRotate_zero] at h1
  have h2 : HasDerivAt ((mh P ℓ c d t) ∘ fun s => phaseRotate s z) 0 0 := by
    have he : ((mh P ℓ c d t) ∘ fun s => phaseRotate s z) = fun _ => mh P ℓ c d t z :=
      funext fun s => H.h_rot t s z
    rw [he]; exact hasDerivAt_const 0 _
  exact h1.unique h2

theorem Hyp.β_J (t : ℝ) (z : PlanePhase (Option ι)) : mβ P ℓ c d t z (phaseJ z) = 0 := by
  simp only [mβ, ContinuousLinearMap.add_apply, H.α_J, H.dh_J, add_zero]

theorem Hyp.Ω_J (s : ℝ) (z v : PlanePhase (Option ι)) :
    mΩ P ℓ c d s z v (phaseJ z) = c * phaseDot z v := by
  have h := cutoffDegreePrimitive_circle_contraction H.F_smooth H.F0 H.FDJ mχ_contDiff c d s z v
  rw [vector_exteriorOneForm] at h
  exact h

theorem Hyp.W_dot (t : ℝ) (z : PlanePhase (Option ι)) : phaseDot z (mW P ℓ c d t z) = 0 := by
  have h := H.Ω_J (Real.smoothTransition t) z (mW P ℓ c d t z)
  rw [H.W_eq, ContinuousLinearMap.neg_apply, H.β_J, neg_zero] at h
  rcases mul_eq_zero.mp h.symm with h' | h'
  · exact absurd h' H.hc.ne'
  · exact h'

theorem Hyp.V_dot (t : ℝ) (z : PlanePhase (Option ι)) : phaseDot z (mV P ℓ c d t z) = 0 := by
  rw [mV, map_smul, H.W_dot, smul_zero]

theorem Hyp.flow_sq (t : ℝ) (x : PlanePhase (Option ι)) :
    phaseSq (flow (mV P ℓ c d) t x) = phaseSq x :=
  H.V_cs.flow_firstIntegral (Q := phaseSq) (Q' := fun y => (2:ℝ) • phaseDot y)
    phaseSq_hasFDerivAt (fun t y => by rw [ContinuousLinearMap.smul_apply, H.V_dot, smul_zero]) t x

theorem Hyp.flowInv_sq (t : ℝ) (x : PlanePhase (Option ι)) :
    phaseSq (flowInv (mV P ℓ c d) t x) = phaseSq x :=
  H.V_cs.flowInv_firstIntegral (Q := phaseSq) (Q' := fun y => (2:ℝ) • phaseDot y)
    phaseSq_hasFDerivAt (fun t y => by rw [ContinuousLinearMap.smul_apply, H.V_dot, smul_zero]) t x

end circle


/-! ### Tangency to the hyperplane at infinity -/

section range

variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- Linear algebra: a solution of `Ω₀ W = -β`, with `β` vanishing on the `Ω₀`-orthogonal lifts
`N u` of the normal directions, is tangent to the hyperplane at infinity. -/
theorem tangent_of_annih {Ω0 : PlanePhase (Option ι) →L[ℝ] PlanePhase (Option ι) →L[ℝ] ℝ}
    (hΩ : Ω0.IsInvertible) (hskew : ∀ u v, Ω0 u v = -Ω0 v u)
    (N : ℝ × ℝ → PlanePhase (Option ι)) (Y : ℝ × ℝ → PlanePhase ι)
    (hN : ∀ u, N u = ιN u + phaseInfinityInclusion (Y u))
    (hperp : ∀ u y, Ω0 (N u) (phaseInfinityInclusion y) = 0)
    {β : PlanePhase (Option ι) →L[ℝ] ℝ} (hβ : ∀ u, β (N u) = 0) {W : PlanePhase (Option ι)}
    (hW : Ω0 W = -β) : W none = 0 := by
  have dec : ∀ w : PlanePhase (Option ι),
      w = phaseInfinityInclusion (phaseInfinityProjection w - Y (w none)) + N (w none) := by
    intro w
    calc w = phaseInfinityInclusion (phaseInfinityProjection w) + ιN (w none) := decomp w
      _ = _ := by rw [hN, map_sub]; abel
  have hn0 : Ω0 (N (W none)) = 0 := by
    ext x
    rw [ContinuousLinearMap.zero_apply, dec x, map_add, hperp, zero_add]
    have hn : N (W none) =
        W - phaseInfinityInclusion (phaseInfinityProjection W - Y (W none)) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact (dec W).symm
    rw [hn, map_sub, ContinuousLinearMap.sub_apply, hW, ContinuousLinearMap.neg_apply, hβ,
      hskew (phaseInfinityInclusion _) (N _), hperp]
    simp
  have hz : N (W none) = 0 := by
    have h := hΩ.inverse_apply_self (N (W none))
    rw [hn0, map_zero] at h
    exact h.symm
  have h1 := congrFun hz none
  rw [hN] at h1
  simpa using h1

variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

theorem Hyp.Y_spec (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) (y : PlanePhase ι) :
    mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b)
        (phaseInfinityInclusion (mY P ℓ c d t b u)) (phaseInfinityInclusion y) =
      -(mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b) (ιN u)
        (phaseInfinityInclusion y)) := by
  have h := congrArg (fun L => L y) (solveL_spec (H.Res_inv t b)
    (-((mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b) (ιN u)).comp
      phaseInfinityInclusion)))
  simp only [mRes, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply] at h
  exact h

theorem Hyp.N_perp (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) (y : PlanePhase ι) :
    mΩ P ℓ c d (Real.smoothTransition t) (phaseInfinityInclusion b) (mN P ℓ c d t b u)
      (phaseInfinityInclusion y) = 0 := by
  rw [mN, map_add, ContinuousLinearMap.add_apply, H.Y_spec]
  ring

theorem Hyp.Y_smul (t : ℝ) (b : PlanePhase ι) (r : ℝ) (u : ℝ × ℝ) :
    mY P ℓ c d t b (r • u) = r • mY P ℓ c d t b u := by
  unfold mY
  rw [map_smul, map_smul, ContinuousLinearMap.smul_comp, ← solveL_smul (H.Res_inv t b)]
  congr 1
  exact (smul_neg r _).symm

theorem Hyp.N_smul (t : ℝ) (b : PlanePhase ι) (r : ℝ) (u : ℝ × ℝ) :
    mN P ℓ c d t b (r • u) = r • mN P ℓ c d t b u := by
  simp only [mN, H.Y_smul, map_smul, smul_add]

theorem Hyp.h_incl (t : ℝ) (b : PlanePhase ι) : mh P ℓ c d t (phaseInfinityInclusion b) = 0 := by
  have h0 : mN P ℓ c d t b 0 = 0 := by
    have h := H.N_smul t b 0 0
    simpa using h
  simp [mh, h0]

theorem Hyp.dh_tan (t : ℝ) (b y : PlanePhase ι) :
    fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b) (phaseInfinityInclusion y) = 0 := by
  have hfun : (mh P ℓ c d t) ∘ (phaseInfinityInclusion (ι := ι)) = fun _ => 0 :=
    funext (H.h_incl t)
  have hd := (H.h_slice t).differentiable (by simp) (phaseInfinityInclusion b)
  have hc := fderiv_comp b hd (phaseInfinityInclusion (ι := ι)).differentiableAt
  rw [hfun, (phaseInfinityInclusion (ι := ι)).fderiv] at hc
  have h := congrArg (fun L => L y) hc
  simpa using h.symm

theorem Hyp.dh_normal (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) :
    fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b) (ιN u) =
      -(mα P ℓ c d (phaseInfinityInclusion b) (mN P ℓ c d t b u)) := by
  have hline : (fun r : ℝ => mh P ℓ c d t (phaseInfinityInclusion b + r • ιN u)) = fun r =>
      -(mψ (nsq (r • u)) *
        (r * mα P ℓ c d (phaseInfinityInclusion b) (mN P ℓ c d t b u))) := by
    funext r
    have h1 : phaseInfinityProjection (phaseInfinityInclusion b + r • ιN u) = b := by
      rw [map_add, map_smul, proj_incl, proj_ιN, smul_zero, add_zero]
    have h2 : (phaseInfinityInclusion b + r • ιN (ι := ι) u) none = r • u := by simp
    rw [mh, h1, h2, H.N_smul, map_smul, smul_eq_mul]
  have hd := (H.h_slice t).differentiable (by simp) (phaseInfinityInclusion b)
  have hg : HasDerivAt (fun r : ℝ => phaseInfinityInclusion b + r • ιN (ι := ι) u) (ιN u) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ιN (ι := ι) u)).const_add
      (phaseInfinityInclusion b)
  have hl : HasFDerivAt (mh P ℓ c d t) (fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b))
      (phaseInfinityInclusion b + (0:ℝ) • ιN u) := by
    simpa using hd.hasFDerivAt
  have h1 := HasFDerivAt.comp_hasDerivAt (l := mh P ℓ c d t)
    (f := fun r : ℝ => phaseInfinityInclusion b + r • ιN (ι := ι) u) (x := (0:ℝ)) hl hg
  have hψd : HasDerivAt (fun r : ℝ => mψ (nsq (r • u)))
      (deriv (fun r : ℝ => mψ (nsq (r • u))) 0) 0 := by
    have hs : ContDiff ℝ ∞ (fun r : ℝ => mψ (nsq (r • u))) :=
      cdc mψ (fun r : ℝ => nsq (r • u)) mψ_contDiff
        (cdc nsq (fun r : ℝ => r • u) nsq_contDiff (contDiff_id.smul contDiff_const))
    exact (hs.differentiable (by simp) 0).hasDerivAt
  have h2 := (hψd.mul ((hasDerivAt_id' (x := (0:ℝ))).mul_const
    (mα P ℓ c d (phaseInfinityInclusion b) (mN P ℓ c d t b u)))).neg
  have h1' : HasDerivAt (fun r : ℝ => -(mψ (nsq (r • u)) *
      (r * mα P ℓ c d (phaseInfinityInclusion b) (mN P ℓ c d t b u))))
      (fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b) (ιN u)) 0 := by
    rw [← hline]; exact h1
  rw [h1'.unique h2]
  simp [mψ_zero, nsq]

theorem Hyp.β_annih (t : ℝ) (b : PlanePhase ι) (u : ℝ × ℝ) :
    mβ P ℓ c d t (phaseInfinityInclusion b) (mN P ℓ c d t b u) = 0 := by
  have e1 : fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b) (mN P ℓ c d t b u) =
      fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b) (ιN u) +
        fderiv ℝ (mh P ℓ c d t) (phaseInfinityInclusion b)
          (phaseInfinityInclusion (mY P ℓ c d t b u)) := map_add _ _ _
  rw [mβ, ContinuousLinearMap.add_apply, e1, H.dh_normal, H.dh_tan]
  ring

theorem Hyp.W_tan (t : ℝ) (b : PlanePhase ι) :
    mW P ℓ c d t (phaseInfinityInclusion b) none = 0 :=
  tangent_of_annih (H.Ω_inv (τ_mem t) _) (mΩ_skew _ _) (mN P ℓ c d t b) (mY P ℓ c d t b)
    (fun _ => rfl) (H.N_perp t b) (H.β_annih t b) (H.W_eq t _)

theorem Hyp.V_incl (t : ℝ) (b : PlanePhase ι) :
    phaseInfinityInclusion (phaseInfinityProjection (mV P ℓ c d t (phaseInfinityInclusion b))) =
      mV P ℓ c d t (phaseInfinityInclusion b) := by
  have hn : mV P ℓ c d t (phaseInfinityInclusion b) none = 0 := by
    simp [mV, H.W_tan]
  conv_rhs => rw [decomp (mV P ℓ c d t (phaseInfinityInclusion b)), hn]
  simp

/-- The field restricted to the hyperplane at infinity. -/
def mVF (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ) (c d : ℝ) (t : ℝ) (b : PlanePhase ι) :
    PlanePhase ι :=
  phaseInfinityProjection (mV P ℓ c d t (phaseInfinityInclusion b))

theorem Hyp.VF_cs : CSField (mVF P ℓ c d) := by
  refine ⟨?_, HasCompactSupport.intro
    ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod (phaseShell_isCompact 0 6)) ?_⟩
  · exact cdc (phaseInfinityProjection (ι := ι)) (fun p : ℝ × PlanePhase ι =>
      mV P ℓ c d p.1 (phaseInfinityInclusion p.2)) (phaseInfinityProjection (ι := ι)).contDiff
      (cdc (fun p : ℝ × PlanePhase (Option ι) => mV P ℓ c d p.1 p.2)
        (fun p : ℝ × PlanePhase ι => (p.1, phaseInfinityInclusion p.2)) H.V_smooth
        (contDiff_fst.prodMk ((phaseInfinityInclusion (ι := ι)).contDiff.comp contDiff_snd)))
  · intro p hp
    change phaseInfinityProjection (mV P ℓ c d p.1 (phaseInfinityInclusion p.2)) = 0
    rw [H.V_zero, map_zero]
    by_contra hc
    push Not at hc
    rw [phaseSq_incl] at hc
    exact hp ⟨hc.1, phaseSq_nonneg p.2, hc.2⟩

theorem Hyp.flowFrom_incl (t₀ : ℝ) (b : PlanePhase ι) (s : ℝ) :
    flowFrom (mV P ℓ c d) t₀ (phaseInfinityInclusion b) s =
      phaseInfinityInclusion (flowFrom (mVF P ℓ c d) t₀ b s) := by
  refine H.V_cs.flowFrom_eq (u := fun s => phaseInfinityInclusion (flowFrom (mVF P ℓ c d) t₀ b s))
    ⟨by simp only [H.VF_cs.flowFrom_self], fun s => ?_⟩ s
  have h := (phaseInfinityInclusion (ι := ι)).hasFDerivAt.comp_hasDerivAt s
    (H.VF_cs.flowFrom_hasDerivAt t₀ b s)
  convert h using 1 <;> first | rfl | exact (H.V_incl s _).symm

theorem Hyp.shellF_range (z : PlanePhase (Option ι)) :
    shellF P ℓ c d z ∈ range (phaseInfinityInclusion (ι := ι)) ↔
      z ∈ range (phaseInfinityInclusion (ι := ι)) := by
  constructor
  · rintro ⟨b, hb⟩
    have hz : z = flowInv (mV P ℓ c d) 1 (shellF P ℓ c d z) := (H.V_cs.flowInv_flow 1 z).symm
    rw [hz, ← hb, flowInv, H.flowFrom_incl]
    exact mem_range_self _
  · rintro ⟨b, rfl⟩
    rw [shellF, flow, H.flowFrom_incl]
    exact mem_range_self _

theorem Hyp.shellG_range (z : PlanePhase (Option ι)) :
    shellG P ℓ c d z ∈ range (phaseInfinityInclusion (ι := ι)) ↔
      z ∈ range (phaseInfinityInclusion (ι := ι)) := by
  constructor
  · rintro ⟨b, hb⟩
    have hz : z = flow (mV P ℓ c d) 1 (shellG P ℓ c d z) := (H.V_cs.flow_flowInv 1 z).symm
    rw [hz, ← hb, flow, H.flowFrom_incl]
    exact mem_range_self _
  · rintro ⟨b, rfl⟩
    rw [shellG, flowInv, H.flowFrom_incl]
    exact mem_range_self _

end range

/-! ### The shell maps -/

section shell

variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P : (Option ι → ℂ) → (κ → ℂ)} {ℓ : ℕ} {c d : ℝ} (H : Hyp P ℓ c d)
include H

theorem Hyp.shellF_smooth : ContDiff ℝ ∞ (shellF P ℓ c d) := H.V_cs.flow_slice_smooth 1

theorem Hyp.shellG_smooth : ContDiff ℝ ∞ (shellG P ℓ c d) := H.V_cs.flowInv_slice_smooth 1

theorem Hyp.shell_left : LeftInverse (shellG P ℓ c d) (shellF P ℓ c d) :=
  H.V_cs.flowInv_flow 1

theorem Hyp.shell_right : RightInverse (shellG P ℓ c d) (shellF P ℓ c d) :=
  H.V_cs.flow_flowInv 1

theorem Hyp.shellF_sq (z : PlanePhase (Option ι)) : phaseSq (shellF P ℓ c d z) = phaseSq z :=
  H.flow_sq 1 z

theorem Hyp.shellG_sq (z : PlanePhase (Option ι)) : phaseSq (shellG P ℓ c d z) = phaseSq z :=
  H.flowInv_sq 1 z

theorem Hyp.shellF_rot (r : ℝ) (z : PlanePhase (Option ι)) :
    shellF P ℓ c d (phaseRotate r z) = phaseRotate r (shellF P ℓ c d z) :=
  H.V_cs.flow_map (L := phaseRotate r) (fun t y => H.V_rot t r y) 1 z

theorem Hyp.shellG_rot (r : ℝ) (z : PlanePhase (Option ι)) :
    shellG P ℓ c d (phaseRotate r z) = phaseRotate r (shellG P ℓ c d z) :=
  H.V_cs.flowInv_map (L := phaseRotate r) (fun t y => H.V_rot t r y) 1 z

/-- On the unit sphere the explicit shell map pulls the degree cone form back to `c ω₀`. -/
theorem Hyp.shell_form (z : PlanePhase (Option ι)) (hz : phaseSq z = 1)
    (v w : PlanePhase (Option ι)) :
    euclideanExteriorOneForm (degreeConePrimitive (ℓ : ℝ) (cartesianConjugate P) c d)
        (shellF P ℓ c d z) (fderiv ℝ (shellF P ℓ c d) z v) (fderiv ℝ (shellF P ℓ c d) z w) =
      euclideanExteriorOneForm (degreeConePrimitive (ℓ : ℝ) (cartesianConjugate P) c 0) z v w := by
  have h := H.flow_form 1 z v w
  rw [Real.smoothTransition.one, Real.smoothTransition.zero] at h
  have hf1 : phaseSq (shellF P ℓ c d z) = 1 := (H.shellF_sq z).trans hz
  have e1 : mΩ P ℓ c d 1 (shellF P ℓ c d z) =
      euclideanExteriorOneForm (degreeConePrimitive (ℓ : ℝ) (cartesianConjugate P) c d)
        (shellF P ℓ c d z) :=
    cutoffDegreeForm_shell (mχ_one_near (by rw [hf1]; norm_num)) _ c d
  have e0 : mΓ P ℓ c d 0 = degreeConePrimitive (ℓ : ℝ) (cartesianConjugate P) c 0 := by
    funext y
    rw [degreeConePrimitive_zero]
    simp [mΓ, cutoffDegreePrimitive]
  rw [← e1]
  change _ = euclideanExteriorOneForm (degreeConePrimitive (ℓ : ℝ) (cartesianConjugate P) c 0) z v w
  rw [← e0]
  exact h

end shell

end SymplecticPacking.BranchLarge3.TargetMoser
