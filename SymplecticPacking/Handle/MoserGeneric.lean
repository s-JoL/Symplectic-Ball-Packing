import Mathlib
import SymplecticPacking.Handle.MoserFlow
import SymplecticPacking.Bundle.OmegaT

/-!
# The explicit inverse of a skew form, and the cutoffs of the Moser field

`sec:shd-four` (`cons:shd4-moser`): ingredients of the handle Moser field `Y_t = −Ω_t⁻¹ a_t`
on the universal cover `E4 = ℝ⁴` with coordinates `(x, y, u, v)` (indices `0,1,2,3`),
`p = π(x² + y²)` (`Bundle.pE`).

* `solve4 B β`: the explicit solution of `B v = β` for a skew form `B` on `E4` with Pfaffian
  `pf B ≠ 0` (adjugate formula); `solve4_spec`, `solve4_unique`, and smooth dependence on
  parameters (`contDiffAt_solve4`);
* `MoserParams`: the fibre rotation field `R`, the toric threshold `P_tor < h`, the margin
  `δ > 0` and the set `F` (the three fibres) where the primitives vanish;
* the cutoff `cutoffChi M` (`1` for `p ≤ h + 3δ/2`, `0` for `p ≥ h + 7δ/4`) and the weight
  `weightG M` (`1` for `p ≤ h + δ`, `0` for `p ≥ h + 5δ/4`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Filter Topology Set Metric ContinuousLinearMap
open SymplecticPacking.Forms (e dc pf Form1 Form2 d1 d1_apply IsClosed2 E4_eq_sum
  pf_ne_zero_nondeg hasDerivAt_time fderiv_space)
open SymplecticPacking.Bundle (pE dpE hasFDerivAt_pE)
open SymplecticPacking.Return (flowFrom flow flowInv)
open scoped ContDiff NNReal Real

/-! ### The explicit inverse of a nondegenerate skew form on `E4` -/

/-- The solution `v` of `B v = β` for a skew form `B` on `E4` with Pfaffian `pf B ≠ 0`
(explicit adjugate formula). -/
def solve4 (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) (β : E4 →L[ℝ] ℝ) : E4 :=
  (pf B)⁻¹ •
    ((B (e 2) (e 3) * β (e 1) - B (e 1) (e 3) * β (e 2) + B (e 1) (e 2) * β (e 3)) • e 0 +
     (-(B (e 2) (e 3) * β (e 0)) + B (e 0) (e 3) * β (e 2) - B (e 0) (e 2) * β (e 3)) • e 1 +
     (B (e 1) (e 3) * β (e 0) - B (e 0) (e 3) * β (e 1) + B (e 0) (e 1) * β (e 3)) • e 2 +
     (-(B (e 1) (e 2) * β (e 0)) + B (e 0) (e 2) * β (e 1) - B (e 0) (e 1) * β (e 2)) • e 3)

@[simp] lemma solve4_zero (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) : solve4 B 0 = 0 := by
  simp [solve4]

lemma clm_ext_E4 {f g : E4 →L[ℝ] ℝ} (h : ∀ j, f (e j) = g (e j)) : f = g := by
  ext w
  rw [E4_eq_sum w]
  simp only [map_add, map_smul, smul_eq_mul, h]

theorem solve4_spec {B : E4 →L[ℝ] E4 →L[ℝ] ℝ} (hskew : ∀ v w, B v w = -B w v)
    (hpf : pf B ≠ 0) (β : E4 →L[ℝ] ℝ) : B (solve4 B β) = β := by
  have h00 : B (e 0) (e 0) = 0 := by linarith [hskew (e 0) (e 0)]
  have h11 : B (e 1) (e 1) = 0 := by linarith [hskew (e 1) (e 1)]
  have h22 : B (e 2) (e 2) = 0 := by linarith [hskew (e 2) (e 2)]
  have h33 : B (e 3) (e 3) = 0 := by linarith [hskew (e 3) (e 3)]
  have h10 := hskew (e 1) (e 0); have h20 := hskew (e 2) (e 0); have h30 := hskew (e 3) (e 0)
  have h21 := hskew (e 2) (e 1); have h31 := hskew (e 3) (e 1); have h32 := hskew (e 3) (e 2)
  apply clm_ext_E4
  intro j
  unfold solve4
  rw [map_smul, smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hpf]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h00, h11, h22, h33, h10, h20, h30, h21,
      h31, h32] <;> simp only [pf] <;> ring

theorem solve4_unique {B : E4 →L[ℝ] E4 →L[ℝ] ℝ} (hskew : ∀ v w, B v w = -B w v)
    (hpf : pf B ≠ 0) {β : E4 →L[ℝ] ℝ} {v : E4} (hv : B v = β) : v = solve4 B β := by
  have h := pf_ne_zero_nondeg hskew hpf (v - solve4 B β) (fun w => by
    rw [map_sub, sub_apply, hv, solve4_spec hskew hpf, sub_self])
  exact sub_eq_zero.mp h

theorem contDiffAt_solve4 {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {B : Q → E4 →L[ℝ] E4 →L[ℝ] ℝ} {β : Q → E4 →L[ℝ] ℝ} {q : Q} (hB : ContDiffAt ℝ ∞ B q)
    (hβ : ContDiffAt ℝ ∞ β q) (hpf : pf (B q) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => solve4 (B q) (β q)) q := by
  have b : ∀ i j, ContDiffAt ℝ ∞ (fun q => B q (e i) (e j)) q := fun i j =>
    (hB.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have c : ∀ i, ContDiffAt ℝ ∞ (fun q => β q (e i)) q := fun i => hβ.clm_apply contDiffAt_const
  have hp : ContDiffAt ℝ ∞ (fun q => pf (B q)) q := by
    unfold pf
    exact (((b 0 1).mul (b 2 3)).sub ((b 0 2).mul (b 1 3))).add ((b 0 3).mul (b 1 2))
  have s : ∀ (f : Q → ℝ) (i : Fin 4), ContDiffAt ℝ ∞ f q →
      ContDiffAt ℝ ∞ (fun q => f q • e i) q :=
    fun f i hf => hf.smul contDiffAt_const
  have hsum := (((s _ 0 ((((b 2 3).mul (c 1)).sub ((b 1 3).mul (c 2))).add ((b 1 2).mul (c 3)))).add
    (s _ 1 (((((b 2 3).mul (c 0)).neg).add ((b 0 3).mul (c 2))).sub ((b 0 2).mul (c 3))))).add
    (s _ 2 ((((b 1 3).mul (c 0)).sub ((b 0 3).mul (c 1))).add ((b 0 1).mul (c 3))))).add
    (s _ 3 (((((b 1 2).mul (c 0)).neg).add ((b 0 2).mul (c 1))).sub ((b 0 1).mul (c 2))))
  exact (hp.inv hpf).smul hsum

/-! ### Elementary facts about `p` -/

lemma contDiff_pE : ContDiff ℝ ∞ pE := by
  unfold pE
  exact contDiff_const.mul (((dc 0).contDiff.pow 2).add ((dc 1).contDiff.pow 2))

lemma continuous_pE : Continuous pE := contDiff_pE.continuous

@[simp] lemma pE_add_e2 (x : E4) : pE (x + e 2) = pE x := by simp [pE]
@[simp] lemma pE_add_e3 (x : E4) : pE (x + e 3) = pE x := by simp [pE]

lemma norm_E4_le (y : E4) : ‖y‖ ≤ |y 0| + |y 1| + |y 2| + |y 3| := by
  have hs := E4_eq_sum y
  have he : ∀ i, ‖e i‖ = 1 := fun i => by simp
  calc ‖y‖ = ‖y 0 • e 0 + y 1 • e 1 + y 2 • e 2 + y 3 • e 3‖ := by rw [← hs]
    _ ≤ ‖y 0 • e 0‖ + ‖y 1 • e 1‖ + ‖y 2 • e 2‖ + ‖y 3 • e 3‖ := norm_add₄_le
    _ = _ := by simp only [norm_smul, he, mul_one, Real.norm_eq_abs]

/-! ### Moser data -/

/-- The parameters of the handle Moser problem: the fibre rotation field `R`, the toric threshold
`P_tor < h`, the margin `δ > 0` (so the forms are nondegenerate on `{p < h + 2δ}` and we flow on
`{p ≤ h + δ}`), and the set `F` (the three fibres) where the primitives vanish. -/
structure MoserParams where
  R : E4 → E4
  Ptor : ℝ
  h : ℝ
  δ : ℝ
  F : Set E4
  Ptor_lt : Ptor < h
  δ_pos : 0 < δ

/-- **Moser data** (hypotheses of `cons:shd4-moser`, see the module docstring). -/
structure MoserData (M : MoserParams) where
  Om : ℝ → Form2 E4
  a : ℝ → Form1 E4
  smooth_Om : ContDiff ℝ ∞ (fun q : ℝ × E4 => Om q.1 q.2)
  smooth_a : ContDiff ℝ ∞ (fun q : ℝ × E4 => a q.1 q.2)
  skew : ∀ t x v w, Om t x v w = -Om t x w v
  closed : ∀ t, IsClosed2 (Om t)
  dt : ∀ t x v w, HasDerivAt (fun s => Om s x v w) (d1 (a t) x v w) t
  nondeg : ∀ t x, pE x < M.h + 2 * M.δ → pf (Om t x) ≠ 0
  toric : ∀ t x, M.Ptor < pE x → pE x < M.h + 2 * M.δ → Om t x (M.R x) = -dpE x
  toric_a : ∀ t x, M.Ptor < pE x → pE x < M.h + 2 * M.δ → a t x (M.R x) = 0
  fibre : ∀ t x, x ∈ M.F → a t x = 0
  time_supp : ∀ t, t ∉ Icc (0 : ℝ) 1 → a t = 0
  per_Om : ∀ t x, Om t (x + e 2) = Om t x ∧ Om t (x + e 3) = Om t x
  per_a : ∀ t x, a t (x + e 2) = a t x ∧ a t (x + e 3) = a t x

variable {M : MoserParams}

/-! ### The Moser field -/

/-- The cutoff `χ(p)`: `1` for `p ≤ h + 3δ/2`, `0` for `p ≥ h + 7δ/4`. -/
def cutoffChi (M : MoserParams) (p : ℝ) : ℝ :=
  Real.smoothTransition ((M.h + 7 / 4 * M.δ - p) / (M.δ / 4))

/-- The uncut Moser field `Y_t = −Ω_t⁻¹ a_t`, i.e. `ι_{Y_t} Ω_t = −a_t`
(cons:shd4-moser); meaningful on `{p < h + 2δ}`. -/
def moserBase (D : MoserData M) (t : ℝ) (x : E4) : E4 := solve4 (D.Om t x) (-(D.a t x))

/-- **The Moser field** (`cons:shd4-moser`), cut off outside `{p ≤ h + 3δ/2}`. -/
def moserField (D : MoserData M) (t : ℝ) (x : E4) : E4 := cutoffChi M (pE x) • moserBase D t x

/-- **The Moser flow** `Ψ_t` (from time `0`). -/
def moserFlow (D : MoserData M) (t : ℝ) (x : E4) : E4 := flow (moserField D) t x

/-- The inverse `Ψ_t⁻¹` (backward flow from time `t` to `0`). -/
def moserFlowInv (D : MoserData M) (t : ℝ) (y : E4) : E4 := flowInv (moserField D) t y

/-- **The handle Moser map** `Φ = Ψ_1`. -/
def Phi (D : MoserData M) : E4 → E4 := moserFlow D 1

/-- Its inverse. -/
def PhiInv (D : MoserData M) : E4 → E4 := moserFlowInv D 1

lemma cutoffChi_one {p : ℝ} (hp : p ≤ M.h + 3 / 2 * M.δ) : cutoffChi M p = 1 := by
  have := M.δ_pos
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]; linarith

lemma cutoffChi_zero {p : ℝ} (hp : M.h + 7 / 4 * M.δ ≤ p) : cutoffChi M p = 0 := by
  have := M.δ_pos
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma contDiff_cutoffChi : ContDiff ℝ ∞ (cutoffChi M) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

section field

variable (D : MoserData M)

/-! ### The Moser field is a globally Lipschitz field -/

/-! ### Invariance of the moment sublevels -/

lemma deriv_eq_zero_of_eventually_const {G : ℝ → ℝ} {p c : ℝ} (h : ∀ᶠ q in 𝓝 p, G q = c) :
    deriv G p = 0 := by
  have h' : G =ᶠ[𝓝 p] fun _ => c := h
  rw [h'.deriv_eq]
  simp

/-! ### Fibres, deck maps -/

/-! ### The transport equation and the Moser identity -/

lemma diff_eval2 {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {A : Q → E4 →L[ℝ] E4 →L[ℝ] ℝ} {q : Q} (h : DifferentiableAt ℝ A q) (a b : E4) :
    DifferentiableAt ℝ (fun q' => A q' a b) q := by
  fun_prop

lemma fderiv_eval2' {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {A : Q → E4 →L[ℝ] E4 →L[ℝ] ℝ} {q : Q} (h : DifferentiableAt ℝ A q) (z : Q) (a b : E4) :
    fderiv ℝ (fun q' => A q' a b) q z = fderiv ℝ A q z a b := by
  have h1 : DifferentiableAt ℝ (fun q' => A q' a) q := by fun_prop
  rw [fderiv_clm_apply h1 (differentiableAt_const b)]
  simp
  rw [fderiv_clm_apply h (differentiableAt_const a)]
  simp

/-- The weight `g(p)`: `1` for `p ≤ h + δ`, `0` for `p ≥ h + 5δ/4`. -/
def weightG (M : MoserParams) (p : ℝ) : ℝ :=
  Real.smoothTransition ((M.h + 5 / 4 * M.δ - p) / (M.δ / 4))

lemma weightG_one {p : ℝ} (hp : p ≤ M.h + M.δ) : weightG M p = 1 := by
  have := M.δ_pos
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]; linarith

lemma weightG_zero {p : ℝ} (hp : M.h + 5 / 4 * M.δ ≤ p) : weightG M p = 0 := by
  have := M.δ_pos
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma contDiff_weightG : ContDiff ℝ ∞ (weightG M) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

end field

/-! ### The handle Moser map -/

end SymplecticPacking.Handle
