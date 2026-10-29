import SymplecticPacking.Strip.Layer
import SymplecticPacking.Branch2.Model.Cubic.Handle.SecondStage
import SymplecticPacking.Branch2.Model.Cubic.Strip.Ball

/-!
# Layer coordinates and the form on a layer

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Strip.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:str-layer-coords` (`cons:str-layer-coords`, `lem:str-layer-form`, `lem:str-layer-root`): the layer
coordinates `(x_i, T)` on the `i`-th layer `Λ_i` and the form `Ω_pre` in them.

Coordinates on `E4` are the local `𝒜⁺`-frame coordinates `(x, y, s, t)` of the handle
(`Handle/Twist.lean`): `w = x + iy = wL X`, `s = X 2`, `v = t = X 3`, `p = pE X`.
In the *layer coordinates* a point is `mk w x T` (`Y 2 = x`, `Y 3 = T`, same fibre point).

* `Tcoord v = ∫_{1/8}^v b`, an increasing bijection of `(1/8, 5/24)` onto `(0, 1)` with
  `dT = β`; `vOfT` is its inverse (a definite description, `Explicit.the`).
* `ell P T = e_h / b(v(T))`, `Lint P i s T = (s − s_i^-) ℓ = ∫_{s_i^-}^s ℓ`,
  `layerX P i s T p = L + ρ_i(s) h_i(p)`.
* `layerRoot P i x T p = σ_i(x, T, p)`, the unique root `s ∈ I_i` of `x_i(s, T, p) = x`.
* `layerCoord P i : (w, s, v) ↦ (w, x_i(s, T(v), p), T(v))` and its inverse
  `layerChart P i : (w, x, T) ↦ (w, σ_i(x, T, p), v(T))`; `layerChart_smooth`.
* `layer_form`: `Ω_pre = layerCoord^*(ω_V + dx ∧ dT + da_i ∧ dT)` on `Λ_i`.
-/

noncomputable section

namespace SymplecticPacking.Strip.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 e)
open SymplecticPacking.Bundle (pE dpE bB contDiff_bB bB_pos bB_eq_zero bB_nonneg u0 u1)
open SymplecticPacking.Handle (mk mkL wL omegaV GbE)
open SymplecticPacking.Handle.Cubic (Gf aLayer rhoLayer layerLeft layerRight OmegaPre OmegaPreG gsmE)
open scoped ContDiff Real

/-! ### A generic inverse-function lemma -/

/-! ### The coordinate `T` (`cons:str-layer-coords`) -/

/-! ### `ℓ`, `L` and `x_i` -/

variable (P : Branch2.VCubic)

/-- **`ℓ(s, T) = e_h / b(v(T))`** (independent of `s`). -/
def ell (T : ℝ) : ℝ := P.eh / bB (vOfT T)

/-- **`L(s, T) = ∫_{s_i^-}^s ℓ = (s − s_i^-) ℓ(T)`.** -/
def Lint (i : ℕ) (s T : ℝ) : ℝ := (s - layerLeft P i) * ell P T

/-- **`x_i(s, T, p) = L(s, T) + ρ_i(s) h_i(p)`.** -/
def layerX (i : ℕ) (s T p : ℝ) : ℝ := Lint P i s T + rhoLayer P i s * P.hi i p

lemma eh_pos : 0 < P.eh := by unfold Branch2.CubicData.eh; linarith [P.g_pos]

theorem ell_pos {T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) : 0 < ell P T :=
  div_pos (eh_pos P) (bB_pos (vOfT_spec hT).1)

theorem ell_Tcoord {v : ℝ} (hv : v ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    ell P (Tcoord v) = P.eh / bB v := by rw [ell, vOfT_Tcoord hv]

/-! ### The layer root (`lem:str-layer-root`) -/

lemma rhoLayer_left (i : ℕ) : rhoLayer P i (layerLeft P i) = 0 :=
  Handle.Cubic.rhoLayer_eq_zero P le_rfl

lemma rhoLayer_right (i : ℕ) : rhoLayer P i (layerRight P i) = 1 :=
  Handle.Cubic.rhoLayer_eq_one P le_rfl

theorem layerX_left (i : ℕ) (T p : ℝ) : layerX P i (layerLeft P i) T p = 0 := by
  simp [layerX, Lint, rhoLayer_left]

lemma layerLeft_lt_right (i : ℕ) : layerLeft P i < layerRight P i := by
  have := Handle.Cubic.layerRight_sub_left P i; have := Handle.Cubic.ells_pos P; linarith

theorem layerX_right (i : ℕ) {T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) (p : ℝ) :
    layerX P i (layerRight P i) T p = Lint P i (layerRight P i) T + P.hi i p ∧
      P.hi i p < layerX P i (layerRight P i) T p := by
  have h1 : layerX P i (layerRight P i) T p = Lint P i (layerRight P i) T + P.hi i p := by
    simp [layerX, rhoLayer_right]
  refine ⟨h1, ?_⟩
  rw [h1]
  have : 0 < Lint P i (layerRight P i) T :=
    mul_pos (sub_pos.mpr (layerLeft_lt_right P i)) (ell_pos P hT)
  linarith

/-- **`∂_s x_i = ℓ + ρ_i' h_i ≥ ℓ > 0`.** -/
theorem layerX_deriv (i : ℕ) (s T p : ℝ) :
    HasDerivAt (fun σ => layerX P i σ T p) (ell P T + deriv (rhoLayer P i) s * P.hi i p) s ∧
      ell P T ≤ ell P T + deriv (rhoLayer P i) s * P.hi i p := by
  constructor
  · have h1 : HasDerivAt (fun σ => Lint P i σ T) (ell P T) s := by
      have := ((hasDerivAt_id s).sub_const (layerLeft P i)).mul_const (ell P T)
      simpa [Lint] using this
    exact h1.add ((Handle.Cubic.hasDerivAt_rhoLayer P i s).mul_const _)
  · have hd : 0 ≤ deriv (rhoLayer P i) s :=
      (Handle.Cubic.monotone_rhoLayer P i).deriv_nonneg
    have := mul_nonneg hd (Handle.Cubic.hi_pos P i p).le
    linarith

theorem layerX_strictMono (i : ℕ) {T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) (p : ℝ) :
    StrictMono (fun s => layerX P i s T p) := by
  intro a b hab
  have h1 := Handle.Cubic.monotone_rhoLayer P i hab.le
  have h2 := ell_pos P hT
  have h3 := Handle.Cubic.hi_pos P i p
  simp only [layerX, Lint]
  nlinarith

theorem continuous_layerX (i : ℕ) (T p : ℝ) : Continuous (fun s => layerX P i s T p) := by
  unfold layerX Lint
  exact ((continuous_id.sub continuous_const).mul continuous_const).add
    ((Handle.Cubic.contDiff_rhoLayer P i).continuous.mul continuous_const)

theorem layerRoot_existsUnique (i : ℕ) {x T p : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) (hx0 : 0 < x)
    (hx1 : x < layerX P i (layerRight P i) T p) :
    ∃! s, s ∈ Ioo (layerLeft P i) (layerRight P i) ∧ layerX P i s T p = x := by
  have hsurj := intermediate_value_Ioo (layerLeft_lt_right P i).le
    (continuous_layerX P i T p).continuousOn
  rw [layerX_left] at hsurj
  obtain ⟨s, hs, hsx⟩ := hsurj ⟨hx0, hx1⟩
  exact ⟨s, ⟨hs, hsx⟩, fun s' ⟨_, hs'x⟩ =>
    (layerX_strictMono P i hT p).injective (hs'x.trans hsx.symm)⟩

open Classical in
/-- **The layer root** `σ_i(x, T, p)`: the unique `s ∈ I_i` with `x_i(s, T, p) = x`
(definite description; `s_i^-` if there is none). -/
def layerRoot (i : ℕ) (x T p : ℝ) : ℝ :=
  if h : ∃! s, s ∈ Ioo (layerLeft P i) (layerRight P i) ∧ layerX P i s T p = x then
    Explicit.the h else layerLeft P i

/-- **`lem:str-layer-root`.** For `0 < T < 1` and `0 < x < x_i(s_i^+, T, p)` (in particular
for `0 < x < h_i(p)`), `σ_i(x, T, p) ∈ I_i` and `x_i(σ_i, T, p) = x`. -/
theorem layerRoot_mem (i : ℕ) {x T p : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) (hx0 : 0 < x)
    (hx1 : x < layerX P i (layerRight P i) T p) :
    layerRoot P i x T p ∈ Ioo (layerLeft P i) (layerRight P i) ∧
      layerX P i (layerRoot P i x T p) T p = x := by
  have h := layerRoot_existsUnique P i hT hx0 hx1
  rw [layerRoot, dif_pos h]; exact Explicit.the_spec h

theorem layerRoot_mem_of_lt_hi (i : ℕ) {x T p : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1) (hx0 : 0 < x)
    (hx1 : x < P.hi i p) :
    layerRoot P i x T p ∈ Ioo (layerLeft P i) (layerRight P i) ∧
      layerX P i (layerRoot P i x T p) T p = x :=
  layerRoot_mem P i hT hx0 (hx1.trans (layerX_right P i hT p).2)

theorem layerRoot_layerX (i : ℕ) {s T : ℝ} (hT : T ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (layerLeft P i) (layerRight P i)) (p : ℝ) :
    layerRoot P i (layerX P i s T p) T p = s := by
  have hm := layerX_strictMono P i hT p
  have hx0 : 0 < layerX P i s T p := by
    have := hm hs.1; simp only at this; rwa [layerX_left] at this
  have hx1 : layerX P i s T p < layerX P i (layerRight P i) T p := hm hs.2
  have h := layerRoot_existsUnique P i hT hx0 hx1
  rw [layerRoot, dif_pos h]; exact Explicit.the_eq h ⟨hs, rfl⟩

/-! ### The layer coordinate map and its inverse -/

/-- The layer `Λ_i` without the condition `p < h`: `s ∈ I_i`, `1/8 < v < 5/24`. -/
def layerDomain (i : ℕ) : Set E4 :=
  {X | X 2 ∈ Ioo (layerLeft P i) (layerRight P i) ∧ X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)}

/-- The layer `Λ_i = {s ∈ I_i, 1/8 < v < 5/24, p < h}`. -/
def layerSet (i : ℕ) : Set E4 := layerDomain P i ∩ {X | pE X < P.h}

/-- The image region `{0 < x < h_i(p), 0 < T < 1}` in layer coordinates. -/
def layerTarget (i : ℕ) : Set E4 := {Y | 0 < Y 2 ∧ Y 2 < P.hi i (pE Y) ∧ Y 3 ∈ Ioo (0 : ℝ) 1}

theorem isOpen_layerDomain (i : ℕ) : IsOpen (layerDomain P i) :=
  (isOpen_Ioo.preimage (dc 2).continuous).inter (isOpen_Ioo.preimage (dc 3).continuous)

theorem isOpen_layerTarget (i : ℕ) : IsOpen (layerTarget P i) := by
  have hh : Continuous (fun Y : E4 => P.hi i (pE Y)) :=
    (Handle.Cubic.contDiff_hi P i).continuous.comp continuous_pE
  exact (isOpen_lt continuous_const (dc 2).continuous).inter
    ((isOpen_lt (dc 2).continuous hh).inter (isOpen_Ioo.preimage (dc 3).continuous))

/-- **The layer coordinates** `(w, s, v) ↦ (w, x_i(s, T(v), p), T(v))`. -/
def layerCoord (i : ℕ) (X : E4) : E4 :=
  mk (wL X) (layerX P i (X 2) (Tcoord (X 3)) (pE X)) (Tcoord (X 3))

/-- **Their inverse** `(w, x, T) ↦ (w, σ_i(x, T, p), v(T))`. -/
def layerChart (i : ℕ) (Y : E4) : E4 :=
  mk (wL Y) (layerRoot P i (Y 2) (Y 3) (pE Y)) (vOfT (Y 3))

/-- The explicit local form of `layerCoord` (on `1/8 < v < 5/24`). -/
def layerCoordLoc (i : ℕ) (X : E4) : E4 :=
  mk (wL X) ((X 2 - layerLeft P i) * (P.eh / bB (X 3)) + rhoLayer P i (X 2) * P.hi i (pE X))
    (Tcoord (X 3))

theorem layerCoord_eq_loc (i : ℕ) {X : E4} (hX : X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    layerCoord P i X = layerCoordLoc P i X := by
  simp only [layerCoord, layerCoordLoc, layerX, Lint, ell_Tcoord P hX]

theorem layerCoord_eventually (i : ℕ) {X : E4} (hX : X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    layerCoord P i =ᶠ[𝓝 X] layerCoordLoc P i := by
  have : ∀ᶠ Y in 𝓝 X, Y 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24) :=
    (dc 3).continuous.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hX)
  filter_upwards [this] with Y hY using layerCoord_eq_loc P i hY

@[simp] lemma pE_layerCoord (i : ℕ) (X : E4) : pE (layerCoord P i X) = pE X := by
  rw [layerCoord, Handle.pE_mk, Handle.pE_eq]

@[simp] lemma pE_layerChart (i : ℕ) (Y : E4) : pE (layerChart P i Y) = pE Y := by
  rw [layerChart, Handle.pE_mk, Handle.pE_eq]

theorem layerChart_layerCoord (i : ℕ) {X : E4} (hX : X ∈ layerDomain P i) :
    layerChart P i (layerCoord P i X) = X := by
  have hT := Tcoord_mem hX.2
  conv_rhs => rw [← Handle.mk_wL X]
  simp only [layerChart, layerCoord, Handle.wL_mk, Handle.mk_apply2, Handle.mk_apply3,
    Handle.pE_mk, ← Handle.pE_eq, layerRoot_layerX P i hT hX.1, vOfT_Tcoord hX.2]

theorem layerCoord_layerChart (i : ℕ) {Y : E4} (hY : Y ∈ layerTarget P i) :
    layerCoord P i (layerChart P i Y) = Y := by
  obtain ⟨h0, h1, hT⟩ := hY
  have hr := layerRoot_mem_of_lt_hi P i hT h0 h1
  conv_rhs => rw [← Handle.mk_wL Y]
  simp only [layerChart, layerCoord, Handle.wL_mk, Handle.mk_apply2, Handle.mk_apply3,
    Handle.pE_mk, ← Handle.pE_eq, (vOfT_spec hT).2, hr.2]

theorem layerChart_mem (i : ℕ) {Y : E4} (hY : Y ∈ layerTarget P i) :
    layerChart P i Y ∈ layerDomain P i := by
  obtain ⟨h0, h1, hT⟩ := hY
  exact ⟨by simpa [layerChart] using (layerRoot_mem_of_lt_hi P i hT h0 h1).1,
    by simpa [layerChart] using (vOfT_spec hT).1⟩

/-! ### Derivative of the layer coordinates -/

/-- The `x`-coordinate of `layerCoordLoc` and its derivative. -/
def xLoc (i : ℕ) (Y : E4) : ℝ :=
  (Y 2 - layerLeft P i) * (P.eh / bB (Y 3)) + rhoLayer P i (Y 2) * P.hi i (pE Y)

theorem hasFDerivAt_xLoc (i : ℕ) {X : E4} (hb : bB (X 3) ≠ 0) :
    ∃ q : ℝ, HasFDerivAt (xLoc P i) ((P.eh / bB (X 3) + deriv (rhoLayer P i) (X 2) *
      P.hi i (pE X)) • dc 2 + q • dc 3 +
      (rhoLayer P i (X 2) * deriv (P.hi i) (pE X)) • dpE X) X := by
  have hbd : HasDerivAt (fun t => P.eh / bB t) (deriv (fun t => P.eh / bB t) (X 3)) (X 3) :=
    ((hasDerivAt_const _ P.eh).div (hasDerivAt_of_contDiff contDiff_bB (X 3)) hb).differentiableAt
      |>.hasDerivAt
  have h1 : HasFDerivAt (fun Y : E4 => Y 2 - layerLeft P i) (dc 2) X :=
    (dc 2).hasFDerivAt.sub_const _
  have h2 := hasFDerivAt_comp3 (X := X) hbd
  have h3 := hasFDerivAt_comp2 (X := X) (hasDerivAt_of_contDiff (Handle.Cubic.contDiff_rhoLayer P i) (X 2))
  have h4 := hasFDerivAt_compP (X := X) (hasDerivAt_of_contDiff (Handle.Cubic.contDiff_hi P i) (pE X))
  refine ⟨(X 2 - layerLeft P i) * deriv (fun t => P.eh / bB t) (X 3), ?_⟩
  have h := (h1.mul h2).add (h3.mul h4)
  refine h.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul, Handle.dc_apply]
  ring

theorem fderiv_layerCoord_apply (i : ℕ) {X : E4} (hX : X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    ∃ q : ℝ, ∀ v : E4, fderiv ℝ (layerCoord P i) X v =
      mk (wL v) ((P.eh / bB (X 3) + deriv (rhoLayer P i) (X 2) * P.hi i (pE X)) * v 2 + q * v 3 +
        rhoLayer P i (X 2) * deriv (P.hi i) (pE X) * dpE X v) (bB (X 3) * v 3) := by
  obtain ⟨q, hx⟩ := hasFDerivAt_xLoc P i (bB_pos hX).ne'
  have hT := hasFDerivAt_comp3 (X := X) (hasDerivAt_Tcoord (X 3))
  have hall := mkL.hasFDerivAt.comp X (wL.hasFDerivAt.prodMk (hx.prodMk hT))
  refine ⟨q, fun v => ?_⟩
  rw [(layerCoord_eventually P i hX).fderiv_eq]
  rw [show layerCoordLoc P i = (mkL ∘ fun Y => (wL Y, xLoc P i Y, Tcoord (Y 3))) from rfl,
    hall.fderiv]
  simp only [comp_apply, prod_apply, add_apply, smul_apply, smul_eq_mul, Handle.dc_apply, Handle.mk]

/-! ### The form on a layer (`lem:str-layer-form`) -/

lemma contDiff_aLayer (i : ℕ) : ContDiff ℝ ∞ (aLayer P i) := by
  unfold aLayer
  exact (Handle.Cubic.contDiff_J P).add (ContDiff.sum fun j _ => Handle.Cubic.contDiff_hi P j)

/-- **`lem:str-layer-form`, `G_f`.** On `I_i × ℂ`, `G_f = a_i(p) + ρ_i(s) h_i(p)`. -/
theorem Gf_on_layer {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {s : ℝ}
    (hs : s ∈ Ioo (layerLeft P i) (layerRight P i)) (w : ℂ) :
    Gf P s w = aLayer P i (π * ‖w‖ ^ 2) + rhoLayer P i s * P.hi i (π * ‖w‖ ^ 2) :=
  Handle.Cubic.Gf_layer P hi1 hik hs w

/-- **The layer model form** `ω_V + dx ∧ dT + da_i ∧ dT` in layer coordinates `(w, x, T)`. -/
def OmegaLayer (i : ℕ) : Form2 E4 := fun Y =>
  omegaV Y + wedge (dc 2) (dc 3) + wedge (deriv (aLayer P i) (pE Y) • dpE Y) (dc 3)

/-- **`lem:str-layer-form`.** On `Λ_i` (`1 ≤ i ≤ k`), in the layer coordinates
`(x, T) = (x_i, T)` and the fibre point, `Ω_pre = ω_V + dx ∧ dT + da_i ∧ dT`, i.e.
`Ω_pre = layerCoord^* OmegaLayer`. -/
theorem layer_form {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ layerDomain P i) :
    OmegaPre P X = pull2 (layerCoord P i) (OmegaLayer P i) X := by
  obtain ⟨q, hD⟩ := fderiv_layerCoord_apply P i hX.2
  set c : E4 → ℝ := fun Y =>
    (aLayer P i (pE Y) + rhoLayer P i (Y 2) * P.hi i (pE Y)) * bB (Y 3) with hcdef
  have ha := hasFDerivAt_compP (X := X) (hasDerivAt_of_contDiff (contDiff_aLayer P i) (pE X))
  have hρ := hasFDerivAt_comp2 (X := X)
    (hasDerivAt_of_contDiff (Handle.Cubic.contDiff_rhoLayer P i) (X 2))
  have hh := hasFDerivAt_compP (X := X) (hasDerivAt_of_contDiff (Handle.Cubic.contDiff_hi P i) (pE X))
  have hb := hasFDerivAt_comp3 (X := X) (hasDerivAt_of_contDiff contDiff_bB (X 3))
  have hc : HasFDerivAt c _ X := (ha.add (hρ.mul hh)).mul hb
  have hev : GbE (Gf P) =ᶠ[𝓝 X] fun Y => c Y • dc 3 := by
    have : ∀ᶠ Y in 𝓝 X, Y 2 ∈ Ioo (layerLeft P i) (layerRight P i) :=
      (dc 2).continuous.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hX.1)
    filter_upwards [this] with Y hY
    simp only [GbE, hcdef, Gf_on_layer P hi1 hik hY, ← Handle.pE_eq]
  have hG : d1 (GbE (Gf P)) X = wedge (fderiv ℝ c X) (dc 3) := by
    rw [Handle.d1_congr hev, Handle.d1_smul_const_form hc.differentiableAt]
  have hbX := (bB_pos hX.2).ne'
  have h0 : layerCoord P i X 0 = X 0 := by simp [layerCoord]
  have h1 : layerCoord P i X 1 = X 1 := by simp [layerCoord]
  ext v w
  rw [OmegaPre, OmegaPreG]
  simp only [add_apply, Handle.Cubic.d1_gsmE, hG, hc.fderiv, Forms.pull2_apply, OmegaLayer, hD,
    smul_apply, wedge_apply, Handle.omegaV_apply, Handle.wL_mk, Handle.mk_apply2,
    Handle.mk_apply3, pE_layerCoord, smul_eq_mul, Handle.dc_apply, dpE, h0, h1,
    Handle.mk_apply0, Handle.mk_apply1, Handle.wL_re, Handle.wL_im, Pi.add_apply, Pi.mul_apply]
  field_simp
  ring

/-! ### Smoothness of the layer chart (`lem:str-layer-root`, `σ_i` smooth) -/

theorem fderiv_layerCoord_injective (i : ℕ) {X : E4} (hX : X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    Function.Injective (fderiv ℝ (layerCoord P i) X) := by
  obtain ⟨q, hD⟩ := fderiv_layerCoord_apply P i hX
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  rw [hD] at hv
  have e0 := congrArg (fun Z : E4 => Z 0) hv
  have e1 := congrArg (fun Z : E4 => Z 1) hv
  have e2 := congrArg (fun Z : E4 => Z 2) hv
  have e3 := congrArg (fun Z : E4 => Z 3) hv
  simp only [Handle.mk_apply0, Handle.mk_apply1, Handle.mk_apply2, Handle.mk_apply3,
    Handle.wL_re, Handle.wL_im, PiLp.zero_apply] at e0 e1 e2 e3
  have hb := bB_pos hX
  have v3 : v 3 = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd h hb.ne'
    · exact h
  have hdp : dpE X v = 0 := by simp [dpE, Handle.dc_apply, e0, e1]
  have hA : 0 < P.eh / bB (X 3) + deriv (rhoLayer P i) (X 2) * P.hi i (pE X) := by
    have := (layerX_deriv P i (X 2) (Tcoord (X 3)) (pE X)).2
    have h1 : 0 < P.eh / bB (X 3) := div_pos (eh_pos P) hb
    have h2 : 0 ≤ deriv (rhoLayer P i) (X 2) * P.hi i (pE X) :=
      mul_nonneg ((Handle.Cubic.monotone_rhoLayer P i).deriv_nonneg) (Handle.Cubic.hi_pos P i _).le
    linarith
  have v2 : v 2 = 0 := by
    rw [v3, hdp] at e2
    simp only [mul_zero, add_zero] at e2
    rcases mul_eq_zero.mp e2 with h | h
    · exact absurd h hA.ne'
    · exact h
  ext j; fin_cases j <;> simp [e0, e1, v2, v3]

theorem contDiffAt_layerCoord (i : ℕ) {X : E4} (hX : X 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    ContDiffAt ℝ ∞ (layerCoord P i) X := by
  have hb := (bB_pos hX).ne'
  have hx : ContDiffAt ℝ ∞ (xLoc P i) X := by
    unfold xLoc
    refine ((((dc 2).contDiff.sub contDiff_const).contDiffAt).mul
      (contDiffAt_const.div (contDiff_bB.comp (dc 3).contDiff).contDiffAt hb)).add
      ((((Handle.Cubic.contDiff_rhoLayer P i).comp (dc 2).contDiff).mul
        ((Handle.Cubic.contDiff_hi P i).comp Handle.contDiff_pE)).contDiffAt)
  have h : ContDiffAt ℝ ∞ (mkL ∘ fun Y => (wL Y, xLoc P i Y, Tcoord (Y 3))) X :=
    mkL.contDiff.contDiffAt.comp X (wL.contDiff.contDiffAt.prodMk
      (hx.prodMk (contDiff_Tcoord.comp (dc 3).contDiff).contDiffAt))
  exact h.congr_of_eventuallyEq (layerCoord_eventually P i hX)

/-- **`lem:str-layer-root`, smoothness**: the inverse of the layer coordinates (hence the root
`σ_i` and `v(T)`) is `C^∞` on `{0 < x < h_i(p), 0 < T < 1}`. -/
theorem layerChart_smooth (i : ℕ) {Y : E4} (hY : Y ∈ layerTarget P i) :
    ContDiffAt ℝ ∞ (layerChart P i) Y := by
  have hm := layerChart_mem P i hY
  exact contDiffAt_of_leftInverse (isOpen_layerDomain P i) hm (layerCoord_layerChart P i hY)
    (fun X hX => layerChart_layerCoord P i hX) (contDiffAt_layerCoord P i hm.2)
    (fderiv_layerCoord_injective P i hm.2)

/-- **`lem:str-layer-root`, diffeomorphism**: `layerCoord ∘ layerChart = id` near every point of
`{0 < x < h_i(p), 0 < T < 1}`. -/
theorem layerCoord_layerChart_eventually (i : ℕ) {Y : E4} (hY : Y ∈ layerTarget P i) :
    (layerCoord P i ∘ layerChart P i) =ᶠ[𝓝 Y] id := by
  filter_upwards [(isOpen_layerTarget P i).mem_nhds hY] with Z hZ
  exact layerCoord_layerChart P i hZ

end SymplecticPacking.Strip.Cubic
