import Mathlib
import SymplecticPacking.E4
import SymplecticPacking.Forms.Cartan
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy

/-!
# Calculus of base forms on the torus cover

`sec:fer` (calculus layer for `sec:fer-torus`–`sec:fer-positivity`): base forms on the torus in
the universal-cover coordinates `(u, v) ∈ ℝ²`, with an extra fibre parameter `p`.

Representation.
* A *coefficient* is a function `f : ℝ → ℝ → ℝ → ℝ`, `(u, v, p) ↦ f u v p` (`Coef`).
* A base one-form `a du + b dv` (with coefficients depending on `p`) is `BForm` with fields
  `cu = a`, `cv = b`; a base two-form is a coefficient `k` (meaning `k ν`, `ν = du ∧ dv`).
* Partial derivatives `pu`, `pv` are `deriv` of the slices; `d_C (a du + b dv) = ∂_u b − ∂_v a`
  (`BForm.dC`), `d_C F = ∂_u F du + ∂_v F dv` (`dCf`).
* Smoothness is always stated for the `(u, v)`-slice `sl f p : ℝ × ℝ → ℝ` at fixed `p`.
* Torus objects are `1`-periodic in `u` and `v`; integrals over the torus are iterated interval
  integrals `∫₀¹∫₀¹ … du dv` (`torusInt`).

Also: smoothness of `g ∘ fract` for `g` supported inside `(0, 1)` (`contDiff_comp_fract`,
`contDiff_comp_fract₂`), smooth primitives `x ↦ ∫₀^{s x} g(t, x) dt` (`contDiff_primitive`) and
differentiation under the integral sign (`hasDerivAt_integral_param`).
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Set Filter Topology MeasureTheory
open scoped ContDiff

/-! ### Coefficients, partial derivatives, base forms -/

/-- A real coefficient function of `(u, v, p)`. -/
abbrev Coef := ℝ → ℝ → ℝ → ℝ

/-- The `(u, v)`-slice of a coefficient at fixed `p`, as a function on `ℝ × ℝ`. -/
def sl (f : Coef) (p : ℝ) : ℝ × ℝ → ℝ := fun x => f x.1 x.2 p

/-- `∂_u f`. -/
def pu (f : Coef) : Coef := fun u v p => deriv (fun s => f s v p) u

/-- `∂_v f`. -/
def pv (f : Coef) : Coef := fun u v p => deriv (fun t => f u t p) v

/-- `∂_p f`. -/
def pp (f : Coef) : Coef := fun u v p => deriv (fun q => f u v q) p

/-- A `p`-independent coefficient. -/
def ofUV (g : ℝ → ℝ → ℝ) : Coef := fun u v _ => g u v

/-- A base one-form `cu du + cv dv` on the cover (coefficients depending on `p`). -/
structure BForm where
  cu : Coef
  cv : Coef

namespace BForm

instance : Add BForm := ⟨fun α β => ⟨α.cu + β.cu, α.cv + β.cv⟩⟩
instance : Sub BForm := ⟨fun α β => ⟨α.cu - β.cu, α.cv - β.cv⟩⟩

@[simp] lemma add_cu (α β : BForm) : (α + β).cu = α.cu + β.cu := rfl
@[simp] lemma add_cv (α β : BForm) : (α + β).cv = α.cv + β.cv := rfl
@[simp] lemma sub_cu (α β : BForm) : (α - β).cu = α.cu - β.cu := rfl
@[simp] lemma sub_cv (α β : BForm) : (α - β).cv = α.cv - β.cv := rfl

/-- `d_C (a du + b dv) = (∂_u b − ∂_v a) ν`. -/
def dC (α : BForm) : Coef := fun u v p => pu α.cv u v p - pv α.cu u v p

/-- Coefficient-wise multiplication by a function of `p`. -/
def pmul (c : ℝ → ℝ) (α : BForm) : BForm := ⟨fun u v p => c p * α.cu u v p,
  fun u v p => c p * α.cv u v p⟩

/-- `1`-periodicity in `u` and `v` (a one-form on the torus). -/
def Periodic (α : BForm) : Prop :=
  ∀ u v p, α.cu (u + 1) v p = α.cu u v p ∧ α.cv (u + 1) v p = α.cv u v p ∧
    α.cu u (v + 1) p = α.cu u v p ∧ α.cv u (v + 1) p = α.cv u v p

end BForm

/-- `d_C F = ∂_u F du + ∂_v F dv`. -/
def dCf (F : Coef) : BForm := ⟨pu F, pv F⟩

/-- `1`-periodicity of a coefficient in `u` and `v`. -/
def CoefPeriodic (f : Coef) : Prop := ∀ u v p, f (u + 1) v p = f u v p ∧ f u (v + 1) p = f u v p

/-- Integral over the torus: `∫₀¹ ∫₀¹ g(u, v) du dv`. -/
def torusInt (g : ℝ → ℝ → ℝ) : ℝ := ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, g u v

/-! ### Slices -/

lemma hasDerivAt_sl_u {g : ℝ × ℝ → ℝ} {u v : ℝ} (h : DifferentiableAt ℝ g (u, v)) :
    HasDerivAt (fun s => g (s, v)) (fderiv ℝ g (u, v) (1, 0)) u := by
  have hl : HasDerivAt (fun s : ℝ => ((s, v) : ℝ × ℝ)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  exact h.hasFDerivAt.comp_hasDerivAt u hl

lemma hasDerivAt_sl_v {g : ℝ × ℝ → ℝ} {u v : ℝ} (h : DifferentiableAt ℝ g (u, v)) :
    HasDerivAt (fun t => g (u, t)) (fderiv ℝ g (u, v) (0, 1)) v := by
  have hl : HasDerivAt (fun t : ℝ => ((u, t) : ℝ × ℝ)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
  exact h.hasFDerivAt.comp_hasDerivAt v hl

lemma pu_eq {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    pu f u v p = fderiv ℝ (sl f p) (u, v) (1, 0) :=
  (hasDerivAt_sl_u h).deriv

lemma pv_eq {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    pv f u v p = fderiv ℝ (sl f p) (u, v) (0, 1) :=
  (hasDerivAt_sl_v h).deriv

lemma hasDerivAt_pu {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    HasDerivAt (fun s => f s v p) (pu f u v p) u := by
  rw [pu_eq h]; exact hasDerivAt_sl_u h

lemma hasDerivAt_pv {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    HasDerivAt (fun t => f u t p) (pv f u v p) v := by
  rw [pv_eq h]; exact hasDerivAt_sl_v h

/-- Near a point where `f` is `C^{n+1}`, `∂_u f` agrees with `y ↦ Df(y)(1,0)`. -/
lemma sl_pu_eventuallyEq {f : Coef} {p : ℝ} {x : ℝ × ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n + 1) (sl f p) x) :
    sl (pu f) p =ᶠ[𝓝 x] fun y => fderiv ℝ (sl f p) y (1, 0) := by
  filter_upwards [h.eventually (by simp)] with y hy
  exact pu_eq (hy.differentiableAt (by simp))

lemma sl_pv_eventuallyEq {f : Coef} {p : ℝ} {x : ℝ × ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n + 1) (sl f p) x) :
    sl (pv f) p =ᶠ[𝓝 x] fun y => fderiv ℝ (sl f p) y (0, 1) := by
  filter_upwards [h.eventually (by simp)] with y hy
  exact pv_eq (hy.differentiableAt (by simp))

lemma contDiffAt_pu {f : Coef} {p : ℝ} {x : ℝ × ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n + 1) (sl f p) x) : ContDiffAt ℝ n (sl (pu f) p) x := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (sl_pu_eventuallyEq h)
  exact (h.fderiv_right (m := n) le_rfl).clm_apply contDiffAt_const

lemma contDiffAt_pv {f : Coef} {p : ℝ} {x : ℝ × ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n + 1) (sl f p) x) : ContDiffAt ℝ n (sl (pv f) p) x := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (sl_pv_eventuallyEq h)
  exact (h.fderiv_right (m := n) le_rfl).clm_apply contDiffAt_const

lemma contDiffAt_pu_infty {f : Coef} {p : ℝ} {x : ℝ × ℝ} (h : ContDiffAt ℝ ∞ (sl f p) x) :
    ContDiffAt ℝ ∞ (sl (pu f) p) x := by
  rw [contDiffAt_infty] at h ⊢
  intro n
  exact contDiffAt_pu (by exact_mod_cast h (n + 1))

lemma contDiffAt_pv_infty {f : Coef} {p : ℝ} {x : ℝ × ℝ} (h : ContDiffAt ℝ ∞ (sl f p) x) :
    ContDiffAt ℝ ∞ (sl (pv f) p) x := by
  rw [contDiffAt_infty] at h ⊢
  intro n
  exact contDiffAt_pv (by exact_mod_cast h (n + 1))

/-- **Symmetry of mixed partials**: `∂_u ∂_v f = ∂_v ∂_u f` at a `C²` point. -/
lemma pu_pv_comm {f : Coef} {u v p : ℝ} (h : ContDiffAt ℝ 2 (sl f p) (u, v)) :
    pu (pv f) u v p = pv (pu f) u v p := by
  have hD := Forms.differentiableAt_fderiv_of_contDiffAt h
  have e1 := sl_pv_eventuallyEq (n := 1) h
  have e2 := sl_pu_eventuallyEq (n := 1) h
  have hG1 : DifferentiableAt ℝ (fun y => fderiv ℝ (sl f p) y (0, 1)) (u, v) := by fun_prop
  have hG2 : DifferentiableAt ℝ (fun y => fderiv ℝ (sl f p) y (1, 0)) (u, v) := by fun_prop
  have d1 : DifferentiableAt ℝ (sl (pv f) p) (u, v) := hG1.congr_of_eventuallyEq e1
  have d2 : DifferentiableAt ℝ (sl (pu f) p) (u, v) := hG2.congr_of_eventuallyEq e2
  rw [pu_eq d1, pv_eq d2, e1.fderiv_eq, e2.fderiv_eq, Forms.fderiv_eval1 hD,
    Forms.fderiv_eval1 hD]
  exact Forms.symm2 h _ _

/-- `d_C d_C F = 0` at a `C²` point. -/
theorem dC_dCf {F : Coef} {u v p : ℝ} (h : ContDiffAt ℝ 2 (sl F p) (u, v)) :
    (dCf F).dC u v p = 0 := by
  simp only [BForm.dC, dCf]
  rw [pu_pv_comm h, sub_self]

/-! ### Slice differentiability helpers -/

lemma differentiableAt_sl_u {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    DifferentiableAt ℝ (fun s => f s v p) u := (hasDerivAt_pu h).differentiableAt

lemma differentiableAt_sl_v {f : Coef} {u v p : ℝ} (h : DifferentiableAt ℝ (sl f p) (u, v)) :
    DifferentiableAt ℝ (fun t => f u t p) v := (hasDerivAt_pv h).differentiableAt

/-! ### Periodic extension of functions supported in `(0, 1)` -/

lemma fract_eventually_of_not_int {x₀ : ℝ} (h : Int.fract x₀ ≠ 0) :
    ∀ᶠ x : ℝ in 𝓝 x₀, Int.fract x = x - ⌊x₀⌋ := by
  have h0 : (⌊x₀⌋ : ℝ) < x₀ := by
    rcases (Int.floor_le x₀).lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (by rw [← h1]; exact Int.fract_intCast _) h
  have h1 : x₀ < ⌊x₀⌋ + 1 := Int.lt_floor_add_one x₀
  filter_upwards [Ioo_mem_nhds h0 h1] with x hx
  have : ⌊x⌋ = ⌊x₀⌋ := by
    rw [Int.floor_eq_iff]; exact ⟨hx.1.le, hx.2⟩
  rw [Int.fract, this]

/-- Near an integer, `fract x` lies in `[0, δ) ∪ (1 − δ, 1)`. -/
lemma fract_eventually_near_int {x₀ : ℝ} (h : Int.fract x₀ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in 𝓝 x₀, Int.fract x < δ ∨ 1 - δ < Int.fract x := by
  have hx₀ : x₀ = ⌊x₀⌋ := by
    have := Int.fract_add_floor x₀; rw [h, zero_add] at this; exact this.symm
  set n := ⌊x₀⌋
  filter_upwards [Ioo_mem_nhds (show x₀ - min δ 1 < x₀ by have := lt_min hδ one_pos; linarith)
    (show x₀ < x₀ + min δ 1 by have := lt_min hδ one_pos; linarith)] with x hx
  have hm1 := min_le_left δ 1
  have hm2 := min_le_right δ 1
  rcases le_or_gt x₀ x with hle | hlt
  · left
    have hfl : ⌊x⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [hx.2]
    rw [Int.fract, hfl]; linarith [hx.2]
  · right
    have hfl : ⌊x⌋ = n - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hx.1]
    rw [Int.fract, hfl]; push_cast; linarith [hx.1]

/-- If `G` is smooth and `G (s, t) = 0` whenever `s ∉ [a, b] ⊂ (0, 1)` or `t ∉ [a, b]`, then
`(u, v) ↦ G (fract u, fract v)` is smooth. -/
theorem contDiff_comp_fract₂ {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {a b : ℝ} (ha : 0 < a)
    (hb : b < 1) (h0 : ∀ s t, (s ∉ Icc a b ∨ t ∉ Icc a b) → G (s, t) = 0) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => G (Int.fract x.1, Int.fract x.2)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hδ : 0 < min a (1 - b) := lt_min ha (by linarith)
  have zero_of : ∀ s, (s < min a (1 - b) ∨ 1 - min a (1 - b) < s) → s ∉ Icc a b := by
    intro s hs hs'
    rcases hs with hs | hs
    · linarith [min_le_left a (1 - b), hs'.1]
    · linarith [min_le_right a (1 - b), hs'.2]
  by_cases h1 : Int.fract x.1 = 0
  · have hev : (fun x : ℝ × ℝ => G (Int.fract x.1, Int.fract x.2)) =ᶠ[𝓝 x] fun _ => 0 := by
      have := (continuous_fst.tendsto x).eventually (fract_eventually_near_int h1 hδ)
      filter_upwards [this] with y hy
      exact h0 _ _ (Or.inl (zero_of _ hy))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  by_cases h2 : Int.fract x.2 = 0
  · have hev : (fun x : ℝ × ℝ => G (Int.fract x.1, Int.fract x.2)) =ᶠ[𝓝 x] fun _ => 0 := by
      have := (continuous_snd.tendsto x).eventually (fract_eventually_near_int h2 hδ)
      filter_upwards [this] with y hy
      exact h0 _ _ (Or.inr (zero_of _ hy))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  have hev : (fun x : ℝ × ℝ => G (Int.fract x.1, Int.fract x.2)) =ᶠ[𝓝 x]
      fun y => G (y.1 - ⌊x.1⌋, y.2 - ⌊x.2⌋) := by
    have e1 := (continuous_fst.tendsto x).eventually (fract_eventually_of_not_int h1)
    have e2 := (continuous_snd.tendsto x).eventually (fract_eventually_of_not_int h2)
    filter_upwards [e1, e2] with y hy1 hy2
    rw [hy1, hy2]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact hG.contDiffAt.comp x
    (((contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.sub contDiff_const)).contDiffAt)

/-- One-variable version: `g ∘ fract` is smooth if `g` is smooth and vanishes off `[a, b] ⊂ (0,1)`. -/
theorem contDiff_comp_fract {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (h0 : ∀ s, s ∉ Icc a b → g s = 0) : ContDiff ℝ ∞ (fun x => g (Int.fract x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hδ : 0 < min a (1 - b) := lt_min ha (by linarith)
  by_cases h1 : Int.fract x = 0
  · have hev : (fun x : ℝ => g (Int.fract x)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [fract_eventually_near_int h1 hδ] with y hy
      refine h0 _ fun hs' => ?_
      rcases hy with hs | hs
      · linarith [min_le_left a (1 - b), hs'.1]
      · linarith [min_le_right a (1 - b), hs'.2]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : (fun x : ℝ => g (Int.fract x)) =ᶠ[𝓝 x] fun y => g (y - ⌊x⌋) := by
      filter_upwards [fract_eventually_of_not_int h1] with y hy
      rw [hy]
    exact (hg.contDiffAt.comp x (contDiff_id.sub contDiff_const).contDiffAt).congr_of_eventuallyEq
      hev

/-! ### Parametric integrals -/

/-- Smooth primitives: `x ↦ ∫₀^{s x} g (t, x) dt` is smooth if `g` and `s` are. -/
theorem contDiff_primitive {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {g : ℝ × P → ℝ} (hg : ContDiff ℝ ∞ g) {s : P → ℝ}
    (hs : ContDiff ℝ ∞ s) : ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..s x, g (t, x)) := by
  have he : (fun x => ∫ t in (0 : ℝ)..s x, g (t, x)) =
      fun x => s x * ∫ t in (0 : ℝ)..1, g (s x * t, x) := by
    funext x
    have := intervalIntegral.smul_integral_comp_mul_left (fun t => g (t, x)) (s x)
      (a := 0) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at this
    exact this.symm
  rw [he]
  refine hs.mul ?_
  exact OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral
    (f := fun q : ℝ × P => g (s q.2 * q.1, q.2)) <| hg.comp (((hs.comp contDiff_snd).mul contDiff_fst).prodMk contDiff_snd)

/-- Fixed-interval version on an arbitrary interval. -/
theorem contDiff_integral_const {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {g : ℝ × P → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, g (t, x)) := by
  have h1 := contDiff_primitive hg (s := fun _ => b) contDiff_const
  have h2 := contDiff_primitive hg (s := fun _ => a) contDiff_const
  have he : (fun x => ∫ t in a..b, g (t, x)) =
      fun x => (∫ t in (0 : ℝ)..b, g (t, x)) - ∫ t in (0 : ℝ)..a, g (t, x) := by
    funext x
    rw [intervalIntegral.integral_interval_sub_left]
    · exact (hg.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (hg.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  rw [he]; exact h1.sub h2

/-- **Differentiation under the integral sign** for `g` that is `C¹` on `U × ℝ`, `U` open. -/
theorem hasDerivAt_integral_param {g : ℝ × ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ univ)) {s₀ : ℝ} (hs₀ : s₀ ∈ U) (a b : ℝ) :
    HasDerivAt (fun s => ∫ w in a..b, g (s, w))
      (∫ w in a..b, fderiv ℝ g (s₀, w) (1, 0)) s₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  set δ' := δ / 2
  have hδ' : 0 < δ' := by positivity
  have hcb : Metric.closedBall s₀ δ' ⊆ U := fun x hx =>
    hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by simp only [δ']; linarith))
  have hO : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hdiff : ∀ y ∈ U ×ˢ (univ : Set ℝ), DifferentiableAt ℝ g y := fun y hy =>
    (hg.differentiableOn one_ne_zero y hy).differentiableAt (hO.mem_nhds hy)
  have hcont' : ContinuousOn (fun y => fderiv ℝ g y (1, 0)) (U ×ˢ univ) :=
    ((hg.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const)
  have hK : IsCompact (Metric.closedBall s₀ δ' ×ˢ uIcc a b) :=
    (isCompact_closedBall _ _).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hcont'.mono (prod_mono hcb (subset_univ _)))
  have hgcont : ContinuousOn g (U ×ˢ univ) := hg.continuousOn
  have hslice : ∀ s ∈ U, Continuous (fun w => g (s, w)) := fun s hs =>
    hgcont.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨hs, mem_univ _⟩)
  have hslice' : Continuous (fun w => fderiv ℝ g (s₀, w) (1, 0)) :=
    hcont'.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨hs₀, mem_univ _⟩)
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (F := fun s w => g (s, w))
    (F' := fun s w => fderiv ℝ g (s, w) (1, 0)) (x₀ := s₀) (bound := fun _ => C)
    (s := Metric.ball s₀ δ') (Metric.ball_mem_nhds _ hδ')
    (Filter.eventually_of_mem (hU.mem_nhds hs₀) fun s hs => (hslice s hs).aestronglyMeasurable)
    ((hslice s₀ hs₀).intervalIntegrable _ _)
    hslice'.aestronglyMeasurable ?_ intervalIntegrable_const ?_
  · exact this.2
  · refine Filter.Eventually.of_forall fun w hw s hs => ?_
    have hw' : w ∈ uIcc a b := uIoc_subset_uIcc hw
    have hs' : s ∈ Metric.closedBall s₀ δ' := Metric.ball_subset_closedBall hs
    exact hC _ ⟨hs', hw'⟩
  · refine Filter.Eventually.of_forall fun w _ s hs => ?_
    have hsU : s ∈ U := hcb (Metric.ball_subset_closedBall hs)
    exact hasDerivAt_sl_u (hdiff _ ⟨hsU, mem_univ _⟩)

end SymplecticPacking.Bundle
