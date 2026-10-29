import SymplecticPacking.Handle.SecondStage
import SymplecticPacking.Strip.Ball

/-!
# The time coordinate of the layers

`sec:str-layer-coords` (`cons:str-layer-coords`, `lem:str-layer-form`): parameter-free parts of
the layer coordinates; the layer coordinates `(x_i, T)` for cubic data are in
`Branch2/Model/Cubic/Strip/Layer.lean`.

Coordinates on `E4` are the local `𝒜⁺`-frame coordinates `(x, y, s, t)` of the handle
(`Handle/Twist.lean`): `w = x + iy = wL X`, `s = X 2`, `v = t = X 3`, `p = pE X`.

* `contDiffAt_of_leftInverse`: a left inverse of a `C^∞` map with injective derivative is `C^∞`.
* `Tcoord v = ∫_{1/8}^v b`, an increasing bijection of `(1/8, 5/24)` onto `(0, 1)` with
  `dT = β`; `vOfT` is its inverse (a definite description, `Explicit.the`).
* `OmegaFlat = ω_V + dx ∧ dT`, the flat layer form.
-/

noncomputable section

namespace SymplecticPacking.Strip

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE bB contDiff_bB bB_pos bB_eq_zero bB_nonneg u0 u1)
open SymplecticPacking.Handle (mk mkL wL omegaV Gf aLayer rhoLayer layerLeft layerRight
  OmegaPre OmegaPreG gsmE GbE)
open scoped ContDiff Real

/-! ### A generic inverse-function lemma -/

/-- If `g ∘ f = id` on an open set `U ∋ g y`, `f (g y) = y`, and `f` is `C^∞` at `g y` with
injective derivative, then `g` is `C^∞` at `y`. -/
theorem contDiffAt_of_leftInverse {f g : E4 → E4} {U : Set E4} (hU : IsOpen U) {y : E4}
    (hgy : g y ∈ U) (hfg : f (g y) = y) (hgf : ∀ x ∈ U, g (f x) = x)
    (hf : ContDiffAt ℝ ∞ f (g y)) (hinj : Function.Injective (fderiv ℝ f (g y))) :
    ContDiffAt ℝ ∞ g y := by
  set a := g y
  set L := fderiv ℝ f a
  set E : E4 ≃L[ℝ] E4 :=
    (LinearEquiv.ofInjectiveEndo (L : E4 →ₗ[ℝ] E4) hinj).toContinuousLinearEquiv
  have hE : (E : E4 →L[ℝ] E4) = L := by ext v; rfl
  have hf' : HasFDerivAt f (E : E4 →L[ℝ] E4) a := by
    rw [hE]; exact (hf.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Ψ := hf.localInverse hf' hn
  have hΨs : ContDiffAt ℝ ∞ Ψ (f a) := hf.to_localInverse hf' hn
  have hstrict := hf.hasStrictFDerivAt' hf' hn
  have hright : ∀ᶠ p in 𝓝 (f a), f (Ψ p) = p := hstrict.eventually_right_inverse
  have hΨa : Ψ (f a) = a := hstrict.localInverse_apply_image
  have hcont : ContinuousAt Ψ (f a) := hΨs.continuousAt
  have hU' : ∀ᶠ p in 𝓝 (f a), Ψ p ∈ U := hcont.preimage_mem_nhds (by rw [hΨa]; exact hU.mem_nhds hgy)
  rw [hfg] at hΨs hright hU'
  apply hΨs.congr_of_eventuallyEq
  filter_upwards [hright, hU'] with p hp hpU
  rw [← hgf _ hpU, hp]

/-! ### The coordinate `T` (`cons:str-layer-coords`) -/

/-- **`T(v) = ∫_{1/8}^v b`.** -/
def Tcoord (v : ℝ) : ℝ := ∫ t in (1 / 8 : ℝ)..v, bB t

theorem hasDerivAt_Tcoord (v : ℝ) : HasDerivAt Tcoord (bB v) v :=
  (contDiff_bB.continuous.integral_hasStrictDerivAt _ _).hasDerivAt

theorem contDiff_Tcoord : ContDiff ℝ ∞ Tcoord := by
  have hd : Differentiable ℝ Tcoord := fun v => (hasDerivAt_Tcoord v).differentiableAt
  have hD : deriv Tcoord = bB := funext fun v => (hasDerivAt_Tcoord v).deriv
  exact contDiff_infty_iff_deriv.mpr ⟨hd, hD ▸ contDiff_bB⟩

lemma Tcoord_left : Tcoord (1 / 8) = 0 := by simp [Tcoord]

lemma bB_zero_of_Icc {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hv' : v ∉ Ioo (1 / 8 : ℝ) (5 / 24)) :
    bB v = 0 := by
  apply bB_eq_zero
  rcases eq_or_lt_of_le hv.2 with h | h
  · rw [h]; simp
  · rw [Bundle.fract_of_mem_Ico ⟨hv.1, h⟩]; exact hv'

lemma Tcoord_right : Tcoord (5 / 24) = 1 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable bB MeasureTheory.volume a b := fun a b =>
    contDiff_bB.continuous.intervalIntegrable a b
  have h1 : ∫ t in (0 : ℝ)..(1 / 8), bB t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact bB_zero_of_Icc ⟨ht.1, by linarith [ht.2]⟩ (fun h => by linarith [h.1, ht.2])
  have h3 : ∫ t in (5 / 24 : ℝ)..1, bB t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact bB_zero_of_Icc ⟨by linarith [ht.1], ht.2⟩ (fun h => by linarith [h.2, ht.1])
  have hall := Bundle.integral_bB
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / 8)) (hint (1 / 8) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (1 / 8) (5 / 24)) (hint (5 / 24) 1),
    h1, h3] at hall
  simpa [Tcoord] using hall

theorem Tcoord_strictMonoOn : StrictMonoOn Tcoord (Icc (1 / 8) (5 / 24)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) contDiff_Tcoord.continuous.continuousOn
  intro v hv
  rw [interior_Icc] at hv
  rw [(hasDerivAt_Tcoord v).deriv]; exact bB_pos hv

theorem Tcoord_mem {v : ℝ} (hv : v ∈ Ioo (1 / 8 : ℝ) (5 / 24)) : Tcoord v ∈ Ioo (0 : ℝ) 1 := by
  have hm := Tcoord_strictMonoOn
  constructor
  · rw [← Tcoord_left]
    exact hm ⟨le_rfl, by norm_num⟩ ⟨hv.1.le, hv.2.le⟩ hv.1
  · rw [← Tcoord_right]
    exact hm ⟨hv.1.le, hv.2.le⟩ ⟨by norm_num, le_rfl⟩ hv.2

theorem Tcoord_existsUnique {T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) :
    ∃! v, v ∈ Ioo (1 / 8 : ℝ) (5 / 24) ∧ Tcoord v = T := by
  have hsurj := intermediate_value_Ioo (by norm_num : (1 / 8 : ℝ) ≤ 5 / 24)
    contDiff_Tcoord.continuous.continuousOn
  rw [Tcoord_left, Tcoord_right] at hsurj
  obtain ⟨v, hv, hvT⟩ := hsurj hT
  refine ⟨v, ⟨hv, hvT⟩, fun v' ⟨hv', hv'T⟩ => ?_⟩
  exact Tcoord_strictMonoOn.injOn ⟨hv'.1.le, hv'.2.le⟩ ⟨hv.1.le, hv.2.le⟩ (hv'T.trans hvT.symm)

open Classical in
/-- **`v(T)`**, the inverse of `T` on `(1/8, 5/24)` (the definite description of the unique
`v ∈ (1/8, 5/24)` with `T(v) = T`; `0` if there is none). -/
def vOfT (T : ℝ) : ℝ :=
  if h : ∃! v, v ∈ Ioo (1 / 8 : ℝ) (5 / 24) ∧ Tcoord v = T then Explicit.the h else 0

theorem vOfT_spec {T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) :
    vOfT T ∈ Ioo (1 / 8 : ℝ) (5 / 24) ∧ Tcoord (vOfT T) = T := by
  have h := Tcoord_existsUnique hT
  rw [vOfT, dif_pos h]; exact Explicit.the_spec h

theorem vOfT_Tcoord {v : ℝ} (hv : v ∈ Ioo (1 / 8 : ℝ) (5 / 24)) : vOfT (Tcoord v) = v := by
  have h := Tcoord_existsUnique (Tcoord_mem hv)
  rw [vOfT, dif_pos h]; exact Explicit.the_eq h ⟨hv, rfl⟩

/-! ### `ℓ`, `L` and `x_i` -/

variable (P : Params)

/-- **`ℓ(s, T) = e_h / b(v(T))`** (independent of `s`). -/
def ell (T : ℝ) : ℝ := P.eh / bB (vOfT T)

/-- **`L(s, T) = ∫_{s_i^-}^s ℓ = (s − s_i^-) ℓ(T)`.** -/
def Lint (i : ℕ) (s T : ℝ) : ℝ := (s - layerLeft P i) * ell P T

/-- **`x_i(s, T, p) = L(s, T) + ρ_i(s) h_i(p)`.** -/
def layerX (i : ℕ) (s T p : ℝ) : ℝ := Lint P i s T + rhoLayer P i s * P.hi p

/-! ### The layer root (`lem:str-layer-root`) -/

open Classical in
/-- **The layer root** `σ_i(x, T, p)`: the unique `s ∈ I_i` with `x_i(s, T, p) = x`
(definite description; `s_i^-` if there is none). -/
def layerRoot (i : ℕ) (x T p : ℝ) : ℝ :=
  if h : ∃! s, s ∈ Ioo (layerLeft P i) (layerRight P i) ∧ layerX P i s T p = x then
    Explicit.the h else layerLeft P i

/-! ### The layer coordinate map and its inverse -/

lemma continuous_pE : Continuous pE := by unfold pE; fun_prop

/-- **The layer coordinates** `(w, s, v) ↦ (w, x_i(s, T(v), p), T(v))`. -/
def layerCoord (i : ℕ) (X : E4) : E4 :=
  mk (wL X) (layerX P i (X 2) (Tcoord (X 3)) (pE X)) (Tcoord (X 3))

/-- **Their inverse** `(w, x, T) ↦ (w, σ_i(x, T, p), v(T))`. -/
def layerChart (i : ℕ) (Y : E4) : E4 :=
  mk (wL Y) (layerRoot P i (Y 2) (Y 3) (pE Y)) (vOfT (Y 3))

@[simp] lemma pE_layerCoord (i : ℕ) (X : E4) : pE (layerCoord P i X) = pE X := by
  rw [layerCoord, Handle.pE_mk, Handle.pE_eq]

@[simp] lemma pE_layerChart (i : ℕ) (Y : E4) : pE (layerChart P i Y) = pE Y := by
  rw [layerChart, Handle.pE_mk, Handle.pE_eq]

/-! ### Derivative of the layer coordinates -/

lemma hasFDerivAt_comp2 {g : ℝ → ℝ} {g' : ℝ} {X : E4} (hg : HasDerivAt g g' (X 2)) :
    HasFDerivAt (fun Y : E4 => g (Y 2)) (g' • dc 2) X :=
  hg.comp_hasFDerivAt X (dc 2).hasFDerivAt

lemma hasFDerivAt_comp3 {g : ℝ → ℝ} {g' : ℝ} {X : E4} (hg : HasDerivAt g g' (X 3)) :
    HasFDerivAt (fun Y : E4 => g (Y 3)) (g' • dc 3) X :=
  hg.comp_hasFDerivAt X (dc 3).hasFDerivAt

lemma hasFDerivAt_compP {g : ℝ → ℝ} {g' : ℝ} {X : E4} (hg : HasDerivAt g g' (pE X)) :
    HasFDerivAt (fun Y : E4 => g (pE Y)) (g' • dpE X) X :=
  hg.comp_hasFDerivAt X (Bundle.hasFDerivAt_pE X)

lemma hasDerivAt_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    HasDerivAt g (deriv g t) t :=
  (hg.differentiable (by simp) t).hasDerivAt

/-! ### The form on a layer (`lem:str-layer-form`) -/

/-- **The flat layer form** `ω_V + dx ∧ dT` (after the shear). -/
def OmegaFlat : Form2 E4 := fun Y => omegaV Y + wedge (dc 2) (dc 3)

/-! ### Smoothness of the layer chart (`lem:str-layer-root`, `σ_i` smooth) -/

end SymplecticPacking.Strip
