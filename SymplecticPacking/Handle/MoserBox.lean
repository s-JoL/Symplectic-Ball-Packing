import Mathlib
import SymplecticPacking.Handle.MoserGeneric

/-!
# The handle Moser map with a box cutoff

`sec:shd-four` (`cons:shd4-moser`): the handle Moser map with a **box cutoff** and **deck maps with
phases** (Supplement, four-dimensional handle).

Data (parameters `MoserParams`, `Handle/MoserGeneric.lean`):
* `MoserBoxData M`: a path of 2-forms `Ω_t` and 1-forms `a_t` (`t ∈ ℝ`), jointly `C^∞`, with
  `Ω_t` skew and closed, `∂_t Ω_t = d a_t`, `Ω_t` nondegenerate on `{p < h + 2δ}`, toric on the
  band `{P_tor < p < h + 2δ}` (`ι_R Ω_t = −dp`, `a_t(R) = 0`), `a_t = 0` on `F` and for
  `t ∉ [0, 1]`;
* `DeckCore`: an explicit smooth diffeomorphism `T` of `E4` (with explicit inverse) shifting
  `(u, v)` by integers `(m, n)` and preserving `p`; `T.Preserves Om a`: `T^*Ω_t = Ω_t`,
  `T^*a_t = a_t`; `DeckCore.symm` is the inverse deck map;
* `DeckGens D`: two such maps with shifts `(1, 0)`, `(0, 1)`.

Construction.  `Y_t = −Ω_t⁻¹ a_t` (`boxBase`), cut off in `p` (`boxFieldP`, smooth on `ℝ × E4`,
equivariant under deck maps: `boxFieldP_map`).  Its base components are bounded by
`Cb D = sSup` over the compact fundamental block (`boxFieldP_base_le`, via deck reduction
`deck_reduce`).  The **box cutoff** `boxCut L` (`= 1` on `[−L, L]²`) makes the field
`boxField D L = boxCut L · boxFieldP D` compactly supported, hence an `LField`.  With
`L = boxL D A = A + Cb + 2`, trajectories starting in the block `|u|, |v| ≤ A` stay where the box
cutoff is `1`, so they are trajectories of the uncut field.

Results for `PhiB D A = flow (boxField D (boxL D A)) 1` (`handle_moser_box`):
* smooth, with smooth inverse `PhiBInv D A`;
* `Φ^*Ω_1 = Ω_0` at every `x` with `|u|, |v| ≤ A`, `p ≤ h + δ` (`boxFlow_pullback`; proof: OAI
  `timeSteps_preserves_form` for the weighted form `F g(p) Ω_t`, `F = boxCut A ∘ Ψ_t⁻¹` transported
  by the flow);
* invariance of `{p ≤ c}`, `{p < c}`, `{p = c}` (`c > P_tor`), fixed points `F`;
* deck compatibility `Φ(T x) = T Φ(x)` for `x`, `T x` in the block (`boxPhi_deck`), and
  injectivity modulo deck (`boxPhi_inj_mod_deck`): for `x, y ∈ [0,1]²`-fibres and `A ≥ 2Cb + 2`,
  `Φ x = T (Φ y) ⟹ x = T y`.

Global version (`handle_moser_global`): the flows for different boxes agree on their blocks
(`flowFrom_box_eq`), so `PhiG D x = PhiB D (|u|+|v|) x`, `PhiGInv D` are global `C^∞` inverse maps
with `Φ^*Ω_1 = Ω_0` on all of `{p ≤ h + δ}` and `Φ ∘ T = T ∘ Φ`, `Φ⁻¹ ∘ T = T ∘ Φ⁻¹` for every
data-preserving deck map `T`, everywhere.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Filter Topology Set Metric ContinuousLinearMap
open SymplecticPacking.Forms (e dc pf Form1 Form2 d1 d1_apply IsClosed2 E4_eq_sum
  pf_ne_zero_nondeg hasDerivAt_time fderiv_space)
open SymplecticPacking.Bundle (pE dpE hasFDerivAt_pE)
open SymplecticPacking.Return (flowFrom flow flowInv IsSolFrom)
open scoped ContDiff NNReal Real

/-! ### Nondegeneracy implies nonzero Pfaffian -/

/-- The numerator vector of `solve4`. -/
def numV (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) (β : E4 →L[ℝ] ℝ) : E4 :=
  (B (e 2) (e 3) * β (e 1) - B (e 1) (e 3) * β (e 2) + B (e 1) (e 2) * β (e 3)) • e 0 +
  (-(B (e 2) (e 3) * β (e 0)) + B (e 0) (e 3) * β (e 2) - B (e 0) (e 2) * β (e 3)) • e 1 +
  (B (e 1) (e 3) * β (e 0) - B (e 0) (e 3) * β (e 1) + B (e 0) (e 1) * β (e 3)) • e 2 +
  (-(B (e 1) (e 2) * β (e 0)) + B (e 0) (e 2) * β (e 1) - B (e 0) (e 1) * β (e 2)) • e 3

lemma numV_spec {B : E4 →L[ℝ] E4 →L[ℝ] ℝ} (hskew : ∀ v w, B v w = -B w v)
    (β : E4 →L[ℝ] ℝ) (j : Fin 4) : B (numV B β) (e j) = pf B * β (e j) := by
  have h00 : B (e 0) (e 0) = 0 := by linarith [hskew (e 0) (e 0)]
  have h11 : B (e 1) (e 1) = 0 := by linarith [hskew (e 1) (e 1)]
  have h22 : B (e 2) (e 2) = 0 := by linarith [hskew (e 2) (e 2)]
  have h33 : B (e 3) (e 3) = 0 := by linarith [hskew (e 3) (e 3)]
  have h10 := hskew (e 1) (e 0); have h20 := hskew (e 2) (e 0); have h30 := hskew (e 3) (e 0)
  have h21 := hskew (e 2) (e 1); have h31 := hskew (e 3) (e 1); have h32 := hskew (e 3) (e 2)
  unfold numV
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h00, h11, h22, h33, h10, h20, h30, h21,
      h31, h32] <;> simp only [pf] <;> ring

/-- **A nondegenerate skew form on `E4` has nonzero Pfaffian** (converse of
`pf_ne_zero_nondeg`). -/
theorem pf_ne_zero_of_nondeg {B : E4 →L[ℝ] E4 →L[ℝ] ℝ} (hskew : ∀ v w, B v w = -B w v)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) : pf B ≠ 0 := by
  intro hpf
  have hz : ∀ β : E4 →L[ℝ] ℝ, numV B β = 0 := fun β => hnd _ fun w => by
    rw [E4_eq_sum w]
    simp only [map_add, map_smul, smul_eq_mul, numV_spec hskew, hpf, zero_mul, mul_zero,
      add_zero]
  have c : ∀ (β : E4 →L[ℝ] ℝ) (i : Fin 4), numV B β i = 0 := fun β i => by rw [hz β]; rfl
  have k1 := c (dc 1) 0; have k2 := c (dc 1) 2; have k3 := c (dc 1) 3
  have k4 := c (dc 0) 2; have k5 := c (dc 0) 3; have k6 := c (dc 2) 3
  simp [numV] at k1 k2 k3 k4 k5 k6
  have h00 : B (e 0) (e 0) = 0 := by linarith [hskew (e 0) (e 0)]
  have hB0 : ∀ w, B (e 0) w = 0 := fun w => by
    rw [E4_eq_sum w]
    simp only [map_add, map_smul, smul_eq_mul, h00, k2, k3, k6, mul_zero, add_zero]
  have := hnd (e 0) hB0
  have h1 : (e 0 : E4) 0 = 1 := by simp
  rw [this] at h1
  simp at h1

/-! ### Bumps and the box cutoff -/

/-- `bump1 L s`: `1` for `|s| ≤ L`, `0` for `|s| ≥ L + 1`. -/
def bump1 (L s : ℝ) : ℝ := Real.smoothTransition (s + L + 1) * Real.smoothTransition (L + 1 - s)

/-- **The box cutoff** `boxCut L x = bump1 L (u) · bump1 L (v)`: `1` on `|u|, |v| ≤ L`, `0` if
`|u| ≥ L + 1` or `|v| ≥ L + 1`. -/
def boxCut (L : ℝ) (x : E4) : ℝ := bump1 L (x 2) * bump1 L (x 3)

lemma contDiff_bump1 (L : ℝ) : ContDiff ℝ ∞ (bump1 L) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

lemma contDiff_boxCut (L : ℝ) : ContDiff ℝ ∞ (boxCut L) :=
  ((contDiff_bump1 L).comp (dc 2).contDiff).mul ((contDiff_bump1 L).comp (dc 3).contDiff)

lemma bump1_one {L s : ℝ} (h : |s| ≤ L) : bump1 L s = 1 := by
  have := abs_le.mp h
  rw [bump1, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

lemma bump1_zero {L s : ℝ} (h : L + 1 ≤ |s|) : bump1 L s = 0 := by
  rcases le_abs'.mp h with h | h
  · rw [bump1, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [bump1, Real.smoothTransition.zero_of_nonpos (x := L + 1 - s) (by linarith), mul_zero]

lemma bump1_nonneg (L s : ℝ) : 0 ≤ bump1 L s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma bump1_le_one (L s : ℝ) : bump1 L s ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (s + L + 1)
  have h2 := Real.smoothTransition.nonneg (L + 1 - s)
  have h3 := Real.smoothTransition.le_one (L + 1 - s)
  have h4 := Real.smoothTransition.nonneg (s + L + 1)
  unfold bump1; nlinarith

lemma boxCut_one {L : ℝ} {x : E4} (h2 : |x 2| ≤ L) (h3 : |x 3| ≤ L) : boxCut L x = 1 := by
  rw [boxCut, bump1_one h2, bump1_one h3, one_mul]

lemma boxCut_ne_zero {L : ℝ} {x : E4} (h : boxCut L x ≠ 0) : |x 2| < L + 1 ∧ |x 3| < L + 1 := by
  constructor
  · by_contra h'
    exact h (by rw [boxCut, bump1_zero (not_lt.mp h'), zero_mul])
  · by_contra h'
    exact h (by rw [boxCut, bump1_zero (not_lt.mp h'), mul_zero])

lemma boxCut_nonneg (L : ℝ) (x : E4) : 0 ≤ boxCut L x :=
  mul_nonneg (bump1_nonneg _ _) (bump1_nonneg _ _)

lemma boxCut_le_one (L : ℝ) (x : E4) : boxCut L x ≤ 1 := by
  have h1 := bump1_le_one L (x 2); have h2 := bump1_nonneg L (x 3)
  have h3 := bump1_le_one L (x 3); have h4 := bump1_nonneg L (x 2)
  unfold boxCut; nlinarith

/-- The block size used at a point: `|u| + |v|`. -/
def Aof (x : E4) : ℝ := |x 2| + |x 3|

lemma le_Aof2 (x : E4) : |x 2| ≤ Aof x := by unfold Aof; linarith [abs_nonneg (x 3)]
lemma le_Aof3 (x : E4) : |x 3| ≤ Aof x := by unfold Aof; linarith [abs_nonneg (x 2)]

lemma nhds_block (x : E4) : {Y : E4 | |Y 2| < |x 2| + 1 ∧ |Y 3| < |x 3| + 1} ∈ 𝓝 x :=
  ((isOpen_lt (dc 2).continuous.abs continuous_const).inter
    (isOpen_lt (dc 3).continuous.abs continuous_const)).mem_nhds
    ⟨show |x 2| < |x 2| + 1 by linarith, show |x 3| < |x 3| + 1 by linarith⟩

/-! ### Moser data without periodicity -/

/-- **Moser data** (hypotheses of `cons:shd4-moser`) without any periodicity. -/
structure MoserBoxData (M : MoserParams) where
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

/-! ### Deck maps -/

/-- **A deck map**: an explicit `C^∞` diffeomorphism of `E4` (explicit inverse) shifting
`(u, v)` by the integers `(m, n)` and preserving `p`. -/
structure DeckCore where
  T : E4 → E4
  Tinv : E4 → E4
  smooth : ContDiff ℝ ∞ T
  smooth_inv : ContDiff ℝ ∞ Tinv
  left : ∀ x, Tinv (T x) = x
  right : ∀ x, T (Tinv x) = x
  m : ℤ
  n : ℤ
  shift2 : ∀ x, T x 2 = x 2 + m
  shift3 : ∀ x, T x 3 = x 3 + n
  pE_eq : ∀ x, pE (T x) = pE x

/-- `T` preserves the path of forms and primitives: `T^*Ω_t = Ω_t`, `T^*a_t = a_t`. -/
def DeckCore.Preserves (T : DeckCore) (Om : ℝ → Form2 E4) (a : ℝ → Form1 E4) : Prop :=
  (∀ t x v w, Om t (T.T x) (fderiv ℝ T.T x v) (fderiv ℝ T.T x w) = Om t x v w) ∧
    (∀ t x v, a t (T.T x) (fderiv ℝ T.T x v) = a t x v)

namespace DeckCore

variable (T : DeckCore)

lemma diff : Differentiable ℝ T.T := T.smooth.differentiable (by simp)
lemma diff_inv : Differentiable ℝ T.Tinv := T.smooth_inv.differentiable (by simp)

lemma dT_dTinv (y v : E4) : fderiv ℝ T.T (T.Tinv y) (fderiv ℝ T.Tinv y v) = v := by
  have h := ((T.diff (T.Tinv y)).hasFDerivAt.comp y (T.diff_inv y).hasFDerivAt)
  have he : (T.T ∘ T.Tinv) = id := funext T.right
  rw [he] at h
  have := congrArg (fun L : E4 →L[ℝ] E4 => L v) (h.unique (hasFDerivAt_id y))
  simpa using this

lemma dT_surj (x : E4) : Function.Surjective (fderiv ℝ T.T x) := fun v =>
  ⟨fderiv ℝ T.Tinv (T.T x) v, by
    have := T.dT_dTinv (T.T x) v
    rwa [T.left] at this⟩

/-- The differential preserves the base components. -/
lemma dT_base (x v : E4) : fderiv ℝ T.T x v 2 = v 2 ∧ fderiv ℝ T.T x v 3 = v 3 := by
  have key : ∀ (i : Fin 4) (c : ℝ), (∀ y, T.T y i = y i + c) → fderiv ℝ T.T x v i = v i := by
    intro i c hc
    have h1 := ((dc i).hasFDerivAt (x := T.T x)).comp x (T.diff x).hasFDerivAt
    have he : (fun y => dc i (T.T y)) = fun y => dc i y + c := funext fun y => hc y
    have h2 : HasFDerivAt (fun y => dc i y + c) (dc i) x := (dc i).hasFDerivAt.add_const c
    rw [show ((dc i) ∘ T.T) = fun y => dc i (T.T y) from rfl, he] at h1
    have := congrArg (fun L : E4 →L[ℝ] ℝ => L v) (h1.unique h2)
    simpa using this
  exact ⟨key 2 T.m T.shift2, key 3 T.n T.shift3⟩

/-- The inverse deck map. -/
def symm : DeckCore where
  T := T.Tinv
  Tinv := T.T
  smooth := T.smooth_inv
  smooth_inv := T.smooth
  left := T.right
  right := T.left
  m := -T.m
  n := -T.n
  shift2 x := by have := T.shift2 (T.Tinv x); rw [T.right] at this; push_cast; linarith
  shift3 x := by have := T.shift3 (T.Tinv x); rw [T.right] at this; push_cast; linarith
  pE_eq x := by rw [← T.pE_eq (T.Tinv x), T.right]

lemma Preserves.symm {T : DeckCore} {Om : ℝ → Form2 E4} {a : ℝ → Form1 E4}
    (h : T.Preserves Om a) : T.symm.Preserves Om a := by
  refine ⟨fun t x v w => ?_, fun t x v => ?_⟩
  · change Om t (T.Tinv x) (fderiv ℝ T.Tinv x v) (fderiv ℝ T.Tinv x w) = Om t x v w
    have := h.1 t (T.Tinv x) (fderiv ℝ T.Tinv x v) (fderiv ℝ T.Tinv x w)
    rw [T.dT_dTinv, T.dT_dTinv, T.right] at this
    exact this.symm
  · change a t (T.Tinv x) (fderiv ℝ T.Tinv x v) = a t x v
    have := h.2 t (T.Tinv x) (fderiv ℝ T.Tinv x v)
    rw [T.dT_dTinv, T.right] at this
    exact this.symm

end DeckCore

/-- **Generators of the deck group**: deck maps with shifts `(1, 0)` and `(0, 1)`. -/
structure DeckGens (Om : ℝ → Form2 E4) (a : ℝ → Form1 E4) where
  Tu : DeckCore
  Tv : DeckCore
  hu : Tu.m = 1 ∧ Tu.n = 0
  hv : Tv.m = 0 ∧ Tv.n = 1
  pres_u : Tu.Preserves Om a
  pres_v : Tv.Preserves Om a

/-- **Deck reduction**: a property invariant under the generators and their inverses that holds
over the fundamental block `[0, 1)²` holds everywhere. -/
theorem deck_reduce {Om : ℝ → Form2 E4} {a : ℝ → Form1 E4} (G : DeckGens Om a) {Q : E4 → Prop}
    (hQ : ∀ T : DeckCore, T.Preserves Om a → ∀ x, Q x → Q (T.T x))
    (h0 : ∀ x : E4, x 2 ∈ Ico (0 : ℝ) 1 → x 3 ∈ Ico (0 : ℝ) 1 → Q x) (x : E4) : Q x := by
  have iff : ∀ T : DeckCore, T.Preserves Om a → ∀ x, Q (T.T x) ↔ Q x := fun T hT x =>
    ⟨fun h => by have := hQ T.symm hT.symm _ h; rwa [show T.symm.T (T.T x) = x from T.left x]
      at this, hQ T hT x⟩
  have su : ∀ k : ℤ, ∀ x : E4, ∃ y : E4, y 2 = x 2 + k ∧ y 3 = x 3 ∧ (Q y ↔ Q x) := by
    intro k
    induction k using Int.induction_on with
    | zero => exact fun x => ⟨x, by simp, rfl, Iff.rfl⟩
    | succ k ih =>
      intro x
      obtain ⟨y, h2, h3, hy⟩ := ih x
      refine ⟨G.Tu.T y, ?_, ?_, (iff G.Tu G.pres_u y).trans hy⟩
      · rw [G.Tu.shift2, G.hu.1, h2]; push_cast; ring
      · rw [G.Tu.shift3, G.hu.2, h3]; simp
    | pred k ih =>
      intro x
      obtain ⟨y, h2, h3, hy⟩ := ih x
      refine ⟨G.Tu.symm.T y, ?_, ?_, (iff G.Tu.symm G.pres_u.symm y).trans hy⟩
      · rw [G.Tu.symm.shift2, show G.Tu.symm.m = -G.Tu.m from rfl, G.hu.1, h2]; push_cast; ring
      · rw [G.Tu.symm.shift3, show G.Tu.symm.n = -G.Tu.n from rfl, G.hu.2, h3]; simp
  have sv : ∀ k : ℤ, ∀ x : E4, ∃ y : E4, y 2 = x 2 ∧ y 3 = x 3 + k ∧ (Q y ↔ Q x) := by
    intro k
    induction k using Int.induction_on with
    | zero => exact fun x => ⟨x, rfl, by simp, Iff.rfl⟩
    | succ k ih =>
      intro x
      obtain ⟨y, h2, h3, hy⟩ := ih x
      refine ⟨G.Tv.T y, ?_, ?_, (iff G.Tv G.pres_v y).trans hy⟩
      · rw [G.Tv.shift2, G.hv.1, h2]; simp
      · rw [G.Tv.shift3, G.hv.2, h3]; push_cast; ring
    | pred k ih =>
      intro x
      obtain ⟨y, h2, h3, hy⟩ := ih x
      refine ⟨G.Tv.symm.T y, ?_, ?_, (iff G.Tv.symm G.pres_v.symm y).trans hy⟩
      · rw [G.Tv.symm.shift2, show G.Tv.symm.m = -G.Tv.m from rfl, G.hv.1, h2]; simp
      · rw [G.Tv.symm.shift3, show G.Tv.symm.n = -G.Tv.n from rfl, G.hv.2, h3]; push_cast; ring
  obtain ⟨y, hy2, hy3, hy⟩ := su (-⌊x 2⌋) x
  obtain ⟨z, hz2, hz3, hz⟩ := sv (-⌊y 3⌋) y
  refine hy.mp (hz.mp (h0 z ?_ ?_))
  · rw [hz2, hy2]; push_cast
    exact ⟨by linarith [Int.floor_le (x 2)], by linarith [Int.lt_floor_add_one (x 2)]⟩
  · rw [hz3]; push_cast
    exact ⟨by linarith [Int.floor_le (y 3)], by linarith [Int.lt_floor_add_one (y 3)]⟩

/-! ### The Moser field, cut off in `p` -/

variable {M : MoserParams}

section field

variable (D : MoserBoxData M)

/-- The uncut Moser field `Y_t = −Ω_t⁻¹ a_t` (explicit inverse `solve4`). -/
def boxBase (t : ℝ) (x : E4) : E4 := solve4 (D.Om t x) (-(D.a t x))

/-- The Moser field cut off outside `{p ≤ h + 3δ/2}` (no box cutoff). -/
def boxFieldP (t : ℝ) (x : E4) : E4 := cutoffChi M (pE x) • boxBase D t x

theorem boxBase_spec {t : ℝ} {x : E4} (hx : pE x < M.h + 2 * M.δ) :
    D.Om t x (boxBase D t x) = -D.a t x :=
  solve4_spec (D.skew t x) (D.nondeg t x hx) _

theorem boxBase_unique {t : ℝ} {x : E4} (hx : pE x < M.h + 2 * M.δ) {v : E4}
    (hv : D.Om t x v = -D.a t x) : v = boxBase D t x :=
  solve4_unique (D.skew t x) (D.nondeg t x hx) hv

theorem boxBase_dp {t : ℝ} {x : E4} (h1 : M.Ptor < pE x) (h2 : pE x < M.h + 2 * M.δ) :
    dpE x (boxBase D t x) = 0 := by
  have hs := congrArg (fun f : E4 →L[ℝ] ℝ => f (M.R x)) (boxBase_spec D (t := t) h2)
  simp only [neg_apply, D.toric_a t x h1 h2, neg_zero] at hs
  have hr := congrArg (fun f : E4 →L[ℝ] ℝ => f (boxBase D t x)) (D.toric t x h1 h2)
  simp only [neg_apply] at hr
  rw [D.skew] at hs
  linarith

theorem boxFieldP_dp (t : ℝ) {x : E4} (h1 : M.Ptor < pE x) : dpE x (boxFieldP D t x) = 0 := by
  unfold boxFieldP
  by_cases h2 : pE x < M.h + 2 * M.δ
  · rw [map_smul, boxBase_dp D h1 h2, smul_zero]
  · rw [cutoffChi_zero (by linarith [M.δ_pos]), zero_smul, map_zero]

theorem boxFieldP_fibres (t : ℝ) {x : E4} (hx : x ∈ M.F) : boxFieldP D t x = 0 := by
  simp [boxFieldP, boxBase, D.fibre t x hx]

theorem boxFieldP_time {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) (x : E4) : boxFieldP D t x = 0 := by
  simp [boxFieldP, boxBase, D.time_supp t ht]

theorem boxFieldP_far (t : ℝ) {x : E4} (hx : M.h + 7 / 4 * M.δ ≤ pE x) :
    boxFieldP D t x = 0 := by
  simp [boxFieldP, cutoffChi_zero hx]

theorem boxFieldP_eq_base (t : ℝ) {x : E4} (hx : pE x ≤ M.h + 3 / 2 * M.δ) :
    boxFieldP D t x = boxBase D t x := by
  simp [boxFieldP, cutoffChi_one hx]

theorem contDiffAt_boxBase {q : ℝ × E4} (hq : pE q.2 < M.h + 2 * M.δ) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E4 => boxBase D q.1 q.2) q :=
  contDiffAt_solve4 D.smooth_Om.contDiffAt D.smooth_a.contDiffAt.neg (D.nondeg _ _ hq)

theorem contDiff_boxFieldP : ContDiff ℝ ∞ (fun q : ℝ × E4 => boxFieldP D q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : pE q.2 < M.h + 2 * M.δ
  · exact ((contDiff_cutoffChi.comp (contDiff_pE.comp contDiff_snd)).contDiffAt).smul
      (contDiffAt_boxBase D hq)
  · apply (contDiffAt_const (c := (0 : E4))).congr_of_eventuallyEq
    have hO : {q' : ℝ × E4 | M.h + 7 / 4 * M.δ < pE q'.2} ∈ 𝓝 q :=
      (isOpen_lt continuous_const (continuous_pE.comp continuous_snd)).mem_nhds
        (show M.h + 7 / 4 * M.δ < pE q.2 by push Not at hq; linarith [M.δ_pos])
    filter_upwards [hO] with q' hq'
    exact boxFieldP_far D _ hq'.le

/-- **Equivariance of the uncut field** under deck maps preserving the data. -/
theorem boxFieldP_map (T : DeckCore) (hT : T.Preserves D.Om D.a) (t : ℝ) (x : E4) :
    boxFieldP D t (T.T x) = fderiv ℝ T.T x (boxFieldP D t x) := by
  unfold boxFieldP
  rw [T.pE_eq, map_smul]
  by_cases hx : pE x < M.h + 2 * M.δ
  · congr 1
    symm
    apply boxBase_unique D (by rw [T.pE_eq]; exact hx)
    apply ContinuousLinearMap.ext
    intro w'
    obtain ⟨w, rfl⟩ := T.dT_surj x w'
    rw [hT.1, boxBase_spec D hx, neg_apply, neg_apply, hT.2]
  · rw [cutoffChi_zero (by linarith [M.δ_pos]), zero_smul, zero_smul]

/-! ### The base speed bound -/

/-- The base speed `|Y^u| + |Y^v|`. -/
def baseSpeed (y : E4) : ℝ := |y 2| + |y 3|

/-- The fundamental block `[0, 1] × {(u, v) ∈ [0, 1]², p ≤ h + 2δ}` in `ℝ × E4`. -/
def fundBlock (M : MoserParams) : Set (ℝ × E4) :=
  Icc (0 : ℝ) 1 ×ˢ {x : E4 | x 2 ∈ Icc (0 : ℝ) 1 ∧ x 3 ∈ Icc (0 : ℝ) 1 ∧ pE x ≤ M.h + 2 * M.δ}

lemma isCompact_fundBlock : IsCompact (fundBlock M) := by
  set r : ℝ := 4 + |M.h + 2 * M.δ| / π
  apply isCompact_Icc.prod
  apply (isCompact_closedBall (0 : E4) r).of_isClosed_subset
  · refine ((isClosed_Icc.preimage (dc 2).continuous).inter
      ((isClosed_Icc.preimage (dc 3).continuous).inter
        (isClosed_le continuous_pE continuous_const)))
  · rintro x ⟨h2, h3, hp⟩
    rw [mem_closedBall_zero_iff]
    have hpx : π * (x 0 ^ 2 + x 1 ^ 2) ≤ M.h + 2 * M.δ := by
      have : pE x = π * (x 0 ^ 2 + x 1 ^ 2) := by simp [pE]
      linarith
    have hsq : x 0 ^ 2 + x 1 ^ 2 ≤ |M.h + 2 * M.δ| / π := by
      rw [le_div_iff₀ Real.pi_pos]; linarith [le_abs_self (M.h + 2 * M.δ)]
    have a0 : |x 0| ≤ 1 + x 0 ^ 2 := by cases abs_cases (x 0) <;> nlinarith
    have a1 : |x 1| ≤ 1 + x 1 ^ 2 := by cases abs_cases (x 1) <;> nlinarith
    have a2 : |x 2| ≤ 1 := abs_le.mpr ⟨by linarith [h2.1], h2.2⟩
    have a3 : |x 3| ≤ 1 := abs_le.mpr ⟨by linarith [h3.1], h3.2⟩
    calc ‖x‖ ≤ |x 0| + |x 1| + |x 2| + |x 3| := norm_E4_le x
      _ ≤ r := by simp only [r]; linarith

/-- **The base speed bound** `C_Y = sup` of `|Y^u| + |Y^v|` over the fundamental block
(explicit `sSup`). -/
def Cb : ℝ := max (sSup ((fun q : ℝ × E4 => baseSpeed (boxFieldP D q.1 q.2)) '' fundBlock M)) 0

lemma bddAbove_Cb :
    BddAbove ((fun q : ℝ × E4 => baseSpeed (boxFieldP D q.1 q.2)) '' fundBlock M) :=
  (isCompact_fundBlock.image_of_continuousOn (by
    have hF := (contDiff_boxFieldP D).continuous
    have : Continuous fun q : ℝ × E4 => baseSpeed (boxFieldP D q.1 q.2) :=
      ((dc 2).continuous.comp hF).abs.add ((dc 3).continuous.comp hF).abs
    exact this.continuousOn)).bddAbove

lemma Cb_nonneg : 0 ≤ Cb D := le_max_right _ _

lemma baseSpeed_le_Cb_block {q : ℝ × E4} (hq : q ∈ fundBlock M) :
    baseSpeed (boxFieldP D q.1 q.2) ≤ Cb D :=
  (le_csSup (bddAbove_Cb D) (mem_image_of_mem _ hq)).trans (le_max_left _ _)

lemma baseSpeed_map (T : DeckCore) (x v : E4) :
    baseSpeed (fderiv ℝ T.T x v) = baseSpeed v := by
  unfold baseSpeed; rw [(T.dT_base x v).1, (T.dT_base x v).2]

/-- **The base speed bound holds everywhere** (deck reduction to the fundamental block). -/
theorem baseSpeed_le_Cb (G : DeckGens D.Om D.a) (t : ℝ) (x : E4) :
    baseSpeed (boxFieldP D t x) ≤ Cb D := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  swap
  · rw [boxFieldP_time D ht]; simpa [baseSpeed] using Cb_nonneg D
  by_cases hp : M.h + 2 * M.δ < pE x
  · rw [boxFieldP_far D t (by linarith [M.δ_pos])]; simpa [baseSpeed] using Cb_nonneg D
  push Not at hp
  revert hp
  refine deck_reduce G (Q := fun x => pE x ≤ M.h + 2 * M.δ →
    baseSpeed (boxFieldP D t x) ≤ Cb D) (fun T hT y hy hp => ?_) (fun y h2 h3 hp => ?_) x
  · rw [T.pE_eq] at hp
    rw [boxFieldP_map D T hT, baseSpeed_map]; exact hy hp
  · have hm : ((t, y) : ℝ × E4) ∈ fundBlock M :=
      Set.mk_mem_prod ht (show y 2 ∈ Icc (0 : ℝ) 1 ∧ y 3 ∈ Icc (0 : ℝ) 1 ∧
        pE y ≤ M.h + 2 * M.δ from ⟨⟨h2.1, h2.2.le⟩, ⟨h3.1, h3.2.le⟩, hp⟩)
    have := baseSpeed_le_Cb_block D hm
    dsimp only at this ⊢
    exact this

/-! ### The box cutoff -/

/-- **The box-cut Moser field** `boxCut L · Y_t` (cut off in `p` and in `(u, v)`). -/
def boxField (L : ℝ) (t : ℝ) (x : E4) : E4 := boxCut L x • boxFieldP D t x

/-- The box size used for starting points in the block `|u|, |v| ≤ A`. -/
def boxL (A : ℝ) : ℝ := A + Cb D + 2

/-- **The handle Moser map** for starts in the block `|u|, |v| ≤ A`: the time-`1` flow of the
box-cut field. -/
def PhiB (A : ℝ) : E4 → E4 := flow (boxField D (boxL D A)) 1

/-- Its inverse. -/
def PhiBInv (A : ℝ) : E4 → E4 := flowInv (boxField D (boxL D A)) 1

theorem contDiff_boxField (L : ℝ) : ContDiff ℝ ∞ (fun q : ℝ × E4 => boxField D L q.1 q.2) :=
  ((contDiff_boxCut L).comp contDiff_snd).smul (contDiff_boxFieldP D)

theorem boxField_time (L : ℝ) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) (x : E4) :
    boxField D L t x = 0 := by simp [boxField, boxFieldP_time D ht]

theorem boxField_fibres (L t : ℝ) {x : E4} (hx : x ∈ M.F) : boxField D L t x = 0 := by
  simp [boxField, boxFieldP_fibres D t hx]

theorem boxField_dp (L t : ℝ) {x : E4} (h1 : M.Ptor < pE x) : dpE x (boxField D L t x) = 0 := by
  simp [boxField, boxFieldP_dp D t h1]

theorem baseSpeed_boxField_le (L t : ℝ) (x : E4) :
    baseSpeed (boxField D L t x) ≤ baseSpeed (boxFieldP D t x) := by
  have h0 := boxCut_nonneg L x; have h1 := boxCut_le_one L x
  unfold baseSpeed boxField
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg h0]
  nlinarith [abs_nonneg (boxFieldP D t x 2), abs_nonneg (boxFieldP D t x 3)]

lemma isCompact_slab (r c : ℝ) : IsCompact {x : E4 | |x 2| ≤ r ∧ |x 3| ≤ r ∧ pE x ≤ c} := by
  set ρ : ℝ := 2 + |c| / π + 2 * |r|
  apply (isCompact_closedBall (0 : E4) ρ).of_isClosed_subset
  · exact (isClosed_le ((dc 2).continuous.abs) continuous_const).inter
      ((isClosed_le ((dc 3).continuous.abs) continuous_const).inter
        (isClosed_le continuous_pE continuous_const))
  · rintro x ⟨h2, h3, hp⟩
    rw [mem_closedBall_zero_iff]
    have hpx : π * (x 0 ^ 2 + x 1 ^ 2) ≤ c := by
      have : pE x = π * (x 0 ^ 2 + x 1 ^ 2) := by simp [pE]
      linarith
    have hsq : x 0 ^ 2 + x 1 ^ 2 ≤ |c| / π := by
      rw [le_div_iff₀ Real.pi_pos]; linarith [le_abs_self c]
    have a0 : |x 0| ≤ 1 + x 0 ^ 2 := by cases abs_cases (x 0) <;> nlinarith
    have a1 : |x 1| ≤ 1 + x 1 ^ 2 := by cases abs_cases (x 1) <;> nlinarith
    calc ‖x‖ ≤ |x 0| + |x 1| + |x 2| + |x 3| := norm_E4_le x
      _ ≤ ρ := by simp only [ρ]; linarith [le_abs_self r]

theorem hasCompactSupport_boxField (L : ℝ) :
    HasCompactSupport (fun q : ℝ × E4 => boxField D L q.1 q.2) := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_slab (L + 1) (M.h + 2 * M.δ))) (fun q hq => ?_)
  by_contra hne
  apply hq
  refine Set.mk_mem_prod ?_ ?_
  · by_contra ht; exact hne (boxField_time D L ht _)
  · have hc : boxCut L q.2 ≠ 0 := fun h => hne (by simp [boxField, h])
    obtain ⟨h2, h3⟩ := boxCut_ne_zero hc
    refine ⟨h2.le, h3.le, ?_⟩
    by_contra hp
    exact hne (by rw [boxField, boxFieldP_far D _ (by push Not at hp; linarith [M.δ_pos]),
      smul_zero])

/-- The box-cut field is an `LField` (compact support in `(t, x)`). -/
theorem lfield_boxField (L : ℝ) : LField (boxField D L) where
  smooth := contDiff_boxField D L
  lipschitz := (contDiff_boxField D L).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_boxField D L) (by simp)
  time := ⟨2, by norm_num, fun t y ht => boxField_time D L (fun h => by
    rcases h with ⟨h0, h1⟩
    rw [abs_of_nonneg h0] at ht; linarith) y⟩

/-- Where the box cutoff is `1` (an open set), the box-cut field is the uncut field. -/
theorem boxField_eventuallyEq (L : ℝ) {q : ℝ × E4} (h2 : |q.2 2| < L) (h3 : |q.2 3| < L) :
    (fun q : ℝ × E4 => boxField D L q.1 q.2) =ᶠ[𝓝 q] fun q => boxFieldP D q.1 q.2 := by
  have hO : {q' : ℝ × E4 | |q'.2 2| < L ∧ |q'.2 3| < L} ∈ 𝓝 q :=
    ((isOpen_lt ((dc 2).continuous.comp continuous_snd).abs continuous_const).inter
      (isOpen_lt ((dc 3).continuous.comp continuous_snd).abs continuous_const)).mem_nhds ⟨h2, h3⟩
  filter_upwards [hO] with q' hq'
  simp [boxField, boxCut_one hq'.1.le hq'.2.le]

/-! ### Trajectories stay in the box -/

section traj

variable (G : DeckGens D.Om D.a) (L : ℝ)
include G

/-- **Base displacement**: over `t ∈ [0, 1]` a trajectory moves at most `C_Y t` in `u` and
in `v`. -/
theorem flow_disp (x : E4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |flow (boxField D L) t x 2 - x 2| ≤ Cb D ∧ |flow (boxField D L) t x 3 - x 3| ≤ Cb D := by
  have hV := lfield_boxField D L
  have key : ∀ i : Fin 4, (∀ y : E4, |y i| ≤ baseSpeed y) →
      |flow (boxField D L) t x i - x i| ≤ Cb D := by
    intro i hi
    have hd : ∀ s, HasDerivAt (fun r => flow (boxField D L) r x i)
        (boxField D L s (flow (boxField D L) s x) i) s := fun s =>
      (dc i).hasFDerivAt.comp_hasDerivAt s (hV.flow_hasDerivAt x s)
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r => flow (boxField D L) r x i)
      (a := 0) (b := t) (C := Cb D) (fun s _ => (hd s).hasDerivWithinAt)
      (fun s _ => by
        rw [Real.norm_eq_abs]
        exact (hi _).trans ((baseSpeed_boxField_le D L s _).trans (baseSpeed_le_Cb D G s _)))
      t ⟨ht.1, le_rfl⟩
    simp only [Real.norm_eq_abs, hV.flow_zero, sub_zero] at h
    calc _ ≤ Cb D * t := h
      _ ≤ Cb D * 1 := by gcongr; exacts [Cb_nonneg D, ht.2]
      _ = Cb D := mul_one _
  exact ⟨key 2 fun y => by unfold baseSpeed; linarith [abs_nonneg (y 3)],
    key 3 fun y => by unfold baseSpeed; linarith [abs_nonneg (y 2)]⟩

end traj

/-! ### The Moser identity, via a transported bump -/

/-- The forms, primitives and fields as functions on `ℝ × E4`. -/
def OmB (q : ℝ × E4) : E4 →L[ℝ] E4 →L[ℝ] ℝ := D.Om q.1 q.2
def aB (q : ℝ × E4) : E4 →L[ℝ] ℝ := D.a q.1 q.2
def YB (q : ℝ × E4) : E4 := boxBase D q.1 q.2
def XB (q : ℝ × E4) : E4 := boxFieldP D q.1 q.2

lemma diff_OmB (q : ℝ × E4) : DifferentiableAt ℝ (OmB D) q :=
  D.smooth_Om.differentiable (by simp) q

lemma diff_aB (q : ℝ × E4) : DifferentiableAt ℝ (aB D) q :=
  D.smooth_a.differentiable (by simp) q

lemma OmB_time (q : ℝ × E4) (v w : E4) :
    fderiv ℝ (OmB D) q (1, 0) v w = fderiv ℝ (aB D) q (0, v) w - fderiv ℝ (aB D) q (0, w) v := by
  obtain ⟨t, x⟩ := q
  have h0 := hasDerivAt_time (G := fun q => OmB D q v w) (diff_eval2 (diff_OmB D (t, x)) v w)
  have h1 := h0.unique (D.dt t x v w)
  rw [fderiv_eval2' (diff_OmB D (t, x))] at h1
  have hv := fderiv_space (G := aB D) (diff_aB D (t, x)) v
  have hw := fderiv_space (G := aB D) (diff_aB D (t, x)) w
  change fderiv ℝ (D.a t) x v = _ at hv
  change fderiv ℝ (D.a t) x w = _ at hw
  rw [h1, d1_apply, hv, hw]

lemma OmB_closed (q : ℝ × E4) (u v w : E4) :
    fderiv ℝ (OmB D) q (0, u) v w - fderiv ℝ (OmB D) q (0, v) u w +
      fderiv ℝ (OmB D) q (0, w) u v = 0 := by
  obtain ⟨t, x⟩ := q
  have hs : ∀ z, fderiv ℝ (D.Om t) x z = fderiv ℝ (OmB D) (t, x) (0, z) := fun z =>
    fderiv_space (G := OmB D) (diff_OmB D (t, x)) z
  have := D.closed t x u v w
  rw [hs, hs, hs] at this
  exact this

lemma YB_contraction {q : ℝ × E4} (hq : pE q.2 < M.h + 2 * M.δ) (z : ℝ × E4) (w : E4) :
    fderiv ℝ (OmB D) q z (YB D q) w + OmB D q (fderiv ℝ (YB D) q z) w =
      -(fderiv ℝ (aB D) q z w) := by
  have hY : DifferentiableAt ℝ (YB D) q :=
    (contDiffAt_boxBase D hq).differentiableAt (by simp)
  have hleft := (diff_OmB D q).hasFDerivAt.clm_apply hY.hasFDerivAt
  have hO : {q' : ℝ × E4 | pE q'.2 < M.h + 2 * M.δ} ∈ 𝓝 q :=
    (isOpen_lt (continuous_pE.comp continuous_snd) continuous_const).mem_nhds hq
  have heq : (fun q' => OmB D q' (YB D q')) =ᶠ[𝓝 q] fun q' => -aB D q' := by
    filter_upwards [hO] with q' hq' using boxBase_spec D hq'
  have hright : HasFDerivAt (fun q' => OmB D q' (YB D q')) (-fderiv ℝ (aB D) q) q :=
    ((diff_aB D q).hasFDerivAt.neg).congr_of_eventuallyEq heq
  have hh := congrArg (fun A : (ℝ × E4) →L[ℝ] E4 →L[ℝ] ℝ => A z w) (hleft.unique hright)
  simpa only [add_apply, comp_apply, flip_apply, neg_apply, add_comm] using hh

lemma YB_transport {q : ℝ × E4} (hq : pE q.2 < M.h + 2 * M.δ) (v w : E4) :
    fderiv ℝ (OmB D) q (1, YB D q) v w + OmB D q (fderiv ℝ (YB D) q (0, v)) w +
      OmB D q v (fderiv ℝ (YB D) q (0, w)) = 0 := by
  have h1 := YB_contraction D hq (0, v) w
  have h2 := YB_contraction D hq (0, w) v
  have hc := OmB_closed D q (YB D q) v w
  have ht := OmB_time D q v w
  have hsk : OmB D q v (fderiv ℝ (YB D) q (0, w)) = -OmB D q (fderiv ℝ (YB D) q (0, w)) v :=
    D.skew _ _ _ _
  rw [show ((1 : ℝ), YB D q) = ((1 : ℝ), (0 : E4)) + (0, YB D q) by ext <;> simp, map_add,
    add_apply, add_apply, hsk]
  linarith

/-- The weighted transport bracket of the `p`-cut field vanishes everywhere. -/
lemma XB_bracket (q : ℝ × E4) (v w : E4) :
    deriv (weightG M) (pE q.2) * dpE q.2 (XB D q) * OmB D q v w +
      weightG M (pE q.2) * fderiv ℝ (OmB D) q (1, XB D q) v w +
      weightG M (pE q.2) * OmB D q (fderiv ℝ (XB D) q (0, v)) w +
      weightG M (pE q.2) * OmB D q v (fderiv ℝ (XB D) q (0, w)) = 0 := by
  obtain ⟨t, x⟩ := q
  set p := pE x
  change deriv (weightG M) p * dpE x (XB D (t, x)) * OmB D (t, x) v w +
      weightG M p * fderiv ℝ (OmB D) (t, x) (1, XB D (t, x)) v w +
      weightG M p * OmB D (t, x) (fderiv ℝ (XB D) (t, x) (0, v)) w +
      weightG M p * OmB D (t, x) v (fderiv ℝ (XB D) (t, x) (0, w)) = 0
  by_cases hp : p < M.h + 3 / 2 * M.δ
  · have hO : {q' : ℝ × E4 | pE q'.2 < M.h + 3 / 2 * M.δ} ∈ 𝓝 (t, x) :=
      (isOpen_lt (continuous_pE.comp continuous_snd) continuous_const).mem_nhds hp
    have hXY : XB D =ᶠ[𝓝 (t, x)] YB D := by
      filter_upwards [hO] with q' hq' using boxFieldP_eq_base D _ hq'.le
    have hdX : fderiv ℝ (XB D) (t, x) = fderiv ℝ (YB D) (t, x) := hXY.fderiv_eq
    have hX0 : XB D (t, x) = YB D (t, x) := hXY.eq_of_nhds
    have hT := YB_transport D (q := (t, x)) (by simp only; linarith [M.δ_pos]) v w
    have hdp : deriv (weightG M) p * dpE x (XB D (t, x)) = 0 := by
      by_cases h1 : M.Ptor < p
      · rw [show XB D (t, x) = boxFieldP D t x from rfl, boxFieldP_dp D t h1, mul_zero]
      · rw [deriv_eq_zero_of_eventually_const (c := 1), zero_mul]
        filter_upwards [Iio_mem_nhds (show p < M.h + M.δ by
          linarith [M.Ptor_lt, M.δ_pos, not_lt.mp h1])] with r hr
        exact weightG_one (mem_Iio.mp hr).le
    rw [hdp, hdX, hX0]
    linear_combination weightG M p * hT
  · push Not at hp
    have h0 : weightG M p = 0 := weightG_zero (by linarith [M.δ_pos])
    have h0' : deriv (weightG M) p = 0 := by
      apply deriv_eq_zero_of_eventually_const (c := 0)
      filter_upwards [Ioi_mem_nhds (show M.h + 5 / 4 * M.δ < p by linarith [M.δ_pos])]
        with r hr
      exact weightG_zero (mem_Ioi.mp hr).le
    rw [h0, h0']; ring

/-- The backward flow is transported: `D(Ψ⁻¹)(1, V) = 0`. -/
lemma dflowInv_transport {V : ℝ → E4 → E4} (hV : LField V) (q : ℝ × E4) :
    fderiv ℝ (fun p : ℝ × E4 => flowInv V p.1 p.2) q (1, V q.1 q.2) = 0 := by
  obtain ⟨t, y⟩ := q
  set Gi : ℝ × E4 → E4 := fun p => flowInv V p.1 p.2
  set z := flowInv V t y
  have hy : flow V t z = y := hV.flow_flowInv t y
  have hc : HasDerivAt (fun s : ℝ => (s, flow V s z)) ((1 : ℝ), V t (flow V t z)) t :=
    (hasDerivAt_id t).prodMk (hV.flow_hasDerivAt z t)
  have hG : DifferentiableAt ℝ Gi (t, flow V t z) :=
    hV.flowInv_smooth.differentiable (by simp) _
  have h1 := hG.hasFDerivAt.comp_hasDerivAt t hc
  have hconst : (Gi ∘ fun s : ℝ => (s, flow V s z)) = fun _ => z := by
    funext s; exact hV.flowInv_flow s z
  rw [hconst] at h1
  have := h1.unique (hasDerivAt_const t z)
  rw [hy] at this
  exact this

section pullback

variable (G : DeckGens D.Om D.a) (A : ℝ)

/-- The transported bump `F_t = boxCut A ∘ Ψ_t⁻¹`. -/
def bumpT (q : ℝ × E4) : ℝ := boxCut A (flowInv (boxField D (boxL D A)) q.1 q.2)

/-- The weighted form `W_t = F_t g(p) Ω_t`. -/
def WB (q : ℝ × E4) : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  (OmB D q).comp ((bumpT D A q * weightG M (pE q.2)) • ContinuousLinearMap.id ℝ E4)

lemma WB_apply (q : ℝ × E4) (v w : E4) :
    WB D A q v w = (bumpT D A q * weightG M (pE q.2)) * OmB D q v w := by
  simp [WB]

lemma contDiff_bumpT : ContDiff ℝ ∞ (bumpT D A) :=
  (contDiff_boxCut A).comp (lfield_boxField D (boxL D A)).flowInv_smooth

lemma contDiff_WB : ContDiff ℝ ∞ (WB D A) :=
  D.smooth_Om.clm_comp (((contDiff_bumpT D A).mul
    (contDiff_weightG.comp (contDiff_pE.comp contDiff_snd))).smul contDiff_const)

include G in
/-- Where the transported bump is nonzero, the box cutoff is `1` near the point. -/
lemma bumpT_support {q : ℝ × E4} (hq : bumpT D A q ≠ 0) :
    (fun q : ℝ × E4 => boxField D (boxL D A) q.1 q.2) =ᶠ[𝓝 q] fun q => boxFieldP D q.1 q.2 := by
  obtain ⟨t, y⟩ := q
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · set V := boxField D (boxL D A)
    have hV := lfield_boxField D (boxL D A)
    set z := flowInv V t y
    obtain ⟨hz2, hz3⟩ := boxCut_ne_zero hq
    have hy : flow V t z = y := hV.flow_flowInv t y
    obtain ⟨d2, d3⟩ := flow_disp D G (boxL D A) z ht
    rw [hy] at d2 d3
    have a2 := abs_sub_abs_le_abs_sub (y 2) (z 2)
    have a3 := abs_sub_abs_le_abs_sub (y 3) (z 3)
    apply boxField_eventuallyEq
    · simp only; unfold boxL; linarith
    · simp only; unfold boxL; linarith
  · have hO : {q' : ℝ × E4 | q'.1 ∉ Icc (0 : ℝ) 1} ∈ 𝓝 (t, y) :=
      ((isClosed_Icc.preimage continuous_fst).isOpen_compl).mem_nhds ht
    filter_upwards [hO] with q' hq'
    rw [boxField_time D _ hq', boxFieldP_time D hq']

include G in
/-- **The transport equation for the weighted, bumped form**, everywhere. -/
lemma WB_transport (q : ℝ × E4) (v w : E4) :
    fderiv ℝ (WB D A) q (1, boxField D (boxL D A) q.1 q.2) v w +
      WB D A q (fderiv ℝ (fun q : ℝ × E4 => boxField D (boxL D A) q.1 q.2) q (0, v)) w +
      WB D A q v (fderiv ℝ (fun q : ℝ × E4 => boxField D (boxL D A) q.1 q.2) q (0, w)) = 0 := by
  set X : ℝ × E4 → E4 := fun q => boxField D (boxL D A) q.1 q.2
  have hV := lfield_boxField D (boxL D A)
  set s : ℝ × E4 → ℝ := fun q => bumpT D A q * weightG M (pE q.2)
  have hWd : DifferentiableAt ℝ (WB D A) q := (contDiff_WB D A).differentiable (by simp) q
  have hF : DifferentiableAt ℝ (bumpT D A) q := (contDiff_bumpT D A).differentiable (by simp) q
  obtain ⟨t, x⟩ := q
  have hp' : HasFDerivAt (fun q : ℝ × E4 => pE q.2)
      ((dpE x).comp (ContinuousLinearMap.snd ℝ ℝ E4)) (t, x) := by
    have h := (hasFDerivAt_pE x).comp (t, x) (ContinuousLinearMap.snd ℝ ℝ E4).hasFDerivAt
    exact h
  have hgd : HasDerivAt (weightG M) (deriv (weightG M) (pE x)) (pE x) :=
    (contDiff_weightG.differentiable (by simp) (pE x)).hasDerivAt
  have hg := hgd.comp_hasFDerivAt (t, x) hp'
  have hs := hF.hasFDerivAt.mul hg
  have hO := (diff_eval2 (diff_OmB D (t, x)) v w).hasFDerivAt
  have hprod := hs.mul hO
  have e1 : fderiv ℝ (WB D A) (t, x) (1, X (t, x)) v w =
      fderiv ℝ (fun q => s q * OmB D q v w) (t, x) (1, X (t, x)) := by
    rw [← fderiv_eval2' hWd, show (fun q' => WB D A q' v w) = (fun q => s q * OmB D q v w) from
      funext fun q => WB_apply D A q v w]
  have hdF : fderiv ℝ (bumpT D A) (t, x) (1, X (t, x)) = 0 := by
    have hc : DifferentiableAt ℝ (fun p : ℝ × E4 => flowInv (boxField D (boxL D A)) p.1 p.2)
        (t, x) := hV.flowInv_smooth.differentiable (by simp) _
    have hb : DifferentiableAt ℝ (boxCut A) (flowInv (boxField D (boxL D A)) t x) :=
      (contDiff_boxCut A).differentiable (by simp) _
    have : bumpT D A = fun p : ℝ × E4 => boxCut A
        ((fun p : ℝ × E4 => flowInv (boxField D (boxL D A)) p.1 p.2) p) := rfl
    rw [this, fderiv_fun_comp (t, x) hb hc]
    simp only [comp_apply]
    rw [dflowInv_transport hV (t, x)]; simp
  have hpf : fderiv ℝ (fun q => s q * OmB D q v w) (t, x) = _ := hprod.fderiv
  rw [e1, hpf, WB_apply, WB_apply]
  simp only [add_apply, smul_apply, smul_eq_mul, comp_apply, coe_snd', hdF, Function.comp_apply,
    Pi.mul_apply]
  rw [fderiv_eval2' (diff_OmB D (t, x))]
  by_cases hb : bumpT D A (t, x) = 0
  · rw [hb]; ring
  · have hXX := bumpT_support D G A hb
    have hdX : fderiv ℝ X (t, x) = fderiv ℝ (XB D) (t, x) := hXX.fderiv_eq
    have hX0 : X (t, x) = XB D (t, x) := hXX.eq_of_nhds
    have hbr := XB_bracket D (t, x) v w
    simp only at hbr
    rw [hdX, hX0]
    linear_combination bumpT D A (t, x) * hbr

include G in
/-- **The Moser identity** (`lem:pre-moser`) for the box-cut flow:
`Ψ_t^*Ω_t = Ω_0` at every `x` with `|u|, |v| ≤ A` and `p ≤ h + δ`. -/
theorem boxFlow_pullback (t : ℝ) {x : E4} (h2 : |x 2| ≤ A) (h3 : |x 3| ≤ A)
    (hx : pE x ≤ M.h + M.δ) (v w : E4) :
    D.Om t (flow (boxField D (boxL D A)) t x) (fderiv ℝ (flow (boxField D (boxL D A)) t) x v)
      (fderiv ℝ (flow (boxField D (boxL D A)) t) x w) = D.Om 0 x v w := by
  have hV := lfield_boxField D (boxL D A)
  have hP := hV.flow_preserves_form (WB D A) (contDiff_WB D A)
    (fun q v w => WB_transport D G A q v w) t x v w
  have hc : M.Ptor < M.h + M.δ := by linarith [M.Ptor_lt, M.δ_pos]
  have hsub : ∀ s, pE (flow (boxField D (boxL D A)) s x) ≤ M.h + M.δ := fun s => by
    have hfi := hV.flowFrom_firstIntegral (Q := fun y => Real.smoothTransition (pE y - (M.h + M.δ)))
      (Q' := fun y => deriv (fun p => Real.smoothTransition (p - (M.h + M.δ))) (pE y) • dpE y)
      (fun y => ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _ |>.comp
        (pE y) ((differentiable_id.sub_const _) (pE y))).hasDerivAt.comp_hasFDerivAt y
          (hasFDerivAt_pE y))
      (fun r y => by
        rw [smul_apply, smul_eq_mul]
        by_cases hy : M.Ptor < pE y
        · rw [boxField_dp D _ r hy, mul_zero]
        · rw [deriv_eq_zero_of_eventually_const (c := 0), zero_mul]
          filter_upwards [Iio_mem_nhds (show pE y < M.h + M.δ by linarith [not_lt.mp hy])]
            with q hq
          exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.mp hq])) 0 x s
    have h0 : Real.smoothTransition (pE x - (M.h + M.δ)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    have h1 : Real.smoothTransition (pE (flow (boxField D (boxL D A)) s x) - (M.h + M.δ)) = 0 := by
      rw [← h0]; exact hfi
    have := Real.smoothTransition.zero_iff_nonpos.mp h1
    linarith
  rw [WB_apply, WB_apply] at hP
  have hb1 : bumpT D A (t, flow (boxField D (boxL D A)) t x) = 1 := by
    simp only [bumpT]; rw [hV.flowInv_flow]; exact boxCut_one h2 h3
  have hb0 : bumpT D A (0, x) = 1 := by
    simp only [bumpT]
    rw [show flowInv (boxField D (boxL D A)) 0 x = x from hV.flowFrom_self 0 x]
    exact boxCut_one h2 h3
  rw [hb1, hb0, weightG_one (hsub t), weightG_one hx, one_mul, one_mul, one_mul] at hP
  exact hP

end pullback

/-! ### Sublevels, fibres, deck maps -/

section props

variable (L : ℝ)

/-- Any `G(p)` with `G' = 0` on `(-∞, P_tor]` is a first integral of the box-cut flow. -/
theorem box_firstIntegral {Gf : ℝ → ℝ} (hG : Differentiable ℝ Gf)
    (hG0 : ∀ p ≤ M.Ptor, deriv Gf p = 0) (t₀ : ℝ) (x : E4) (t : ℝ) :
    Gf (pE (flowFrom (boxField D L) t₀ x t)) = Gf (pE x) := by
  refine (lfield_boxField D L).flowFrom_firstIntegral (Q := fun y => Gf (pE y))
    (Q' := fun y => deriv Gf (pE y) • dpE y)
    (fun y => (hG (pE y)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_pE y)) ?_ t₀ x t
  intro s y
  rw [smul_apply, smul_eq_mul]
  by_cases hy : M.Ptor < pE y
  · rw [boxField_dp D L s hy, mul_zero]
  · rw [hG0 _ (not_lt.mp hy), zero_mul]

theorem box_sublevel {c : ℝ} (hc : M.Ptor < c) (t₀ : ℝ) (x : E4) (t : ℝ) :
    pE (flowFrom (boxField D L) t₀ x t) ≤ c ↔ pE x ≤ c := by
  have hG : Differentiable ℝ (fun p => Real.smoothTransition (p - c)) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) |>.comp
      (differentiable_id.sub_const c)
  have hG0 : ∀ p ≤ M.Ptor, deriv (fun p => Real.smoothTransition (p - c)) p = 0 := by
    intro p hp
    apply deriv_eq_zero_of_eventually_const (c := 0)
    filter_upwards [Iio_mem_nhds (show p < c by linarith)] with q hq
    exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.mp hq])
  have := box_firstIntegral D L hG hG0 t₀ x t
  rw [← sub_nonpos, ← sub_nonpos (a := pE x), ← Real.smoothTransition.zero_iff_nonpos,
    ← Real.smoothTransition.zero_iff_nonpos, this]

theorem box_lt {c : ℝ} (hc : M.Ptor < c) (t₀ : ℝ) (x : E4) (t : ℝ) :
    pE (flowFrom (boxField D L) t₀ x t) < c ↔ pE x < c := by
  constructor
  · intro h
    set c' := max (pE (flowFrom (boxField D L) t₀ x t)) ((M.Ptor + c) / 2)
    have h1 : M.Ptor < c' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h2 : c' < c := max_lt h (by linarith)
    exact lt_of_le_of_lt ((box_sublevel D L h1 t₀ x t).mp (le_max_left _ _)) h2
  · intro h
    set c' := max (pE x) ((M.Ptor + c) / 2)
    have h1 : M.Ptor < c' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h2 : c' < c := max_lt h (by linarith)
    exact lt_of_le_of_lt ((box_sublevel D L h1 t₀ x t).mpr (le_max_left _ _)) h2

theorem box_level {c : ℝ} (hc : M.Ptor < c) (t₀ : ℝ) (x : E4) (t : ℝ) :
    pE (flowFrom (boxField D L) t₀ x t) = c ↔ pE x = c := by
  have h1 := box_sublevel D L hc t₀ x t
  have h2 := box_lt D L hc t₀ x t
  constructor
  · intro h
    refine le_antisymm (h1.mp h.le) (not_lt.mp fun h' => ?_)
    have := h2.mpr h'
    rw [h] at this; exact lt_irrefl c this
  · intro h
    refine le_antisymm (h1.mpr h.le) (not_lt.mp fun h' => ?_)
    have := h2.mp h'
    rw [h] at this; exact lt_irrefl c this

/-- The box-cut flow fixes every point of `F`. -/
theorem box_fixes {x : E4} (hx : x ∈ M.F) (t₀ t : ℝ) : flowFrom (boxField D L) t₀ x t = x :=
  (lfield_boxField D L).flowFrom_of_stationary (fun s => boxField_fibres D L s hx) t₀ t

end props

section deck

variable (G : DeckGens D.Om D.a) (A : ℝ)
include G

/-- **Deck compatibility** of the box-cut flow: if `x` and `T x` lie in the block
`|u|, |v| ≤ A`, then `Ψ_t(T x) = T Ψ_t(x)` for all `t`. -/
theorem boxFlow_deck (T : DeckCore) (hT : T.Preserves D.Om D.a) {x : E4}
    (hx2 : |x 2| ≤ A) (hx3 : |x 3| ≤ A) (hTx2 : |T.T x 2| ≤ A) (hTx3 : |T.T x 3| ≤ A) (t : ℝ) :
    flow (boxField D (boxL D A)) t (T.T x) = T.T (flow (boxField D (boxL D A)) t x) := by
  set V := boxField D (boxL D A)
  have hV := lfield_boxField D (boxL D A)
  have hC := Cb_nonneg D
  refine hV.flowFrom_eq (u := fun s => T.T (flow V s x))
    ⟨by simp only; rw [show flow V 0 x = x from hV.flow_zero x], fun s => ?_⟩ t
  have hd : HasDerivAt (fun s => T.T (flow V s x)) _ s :=
    ((T.diff _).hasFDerivAt).comp_hasDerivAt s (hV.flow_hasDerivAt x s)
  refine hd.congr_deriv ?_
  symm
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · obtain ⟨d2, d3⟩ := flow_disp D G (boxL D A) x hs
    set y := flow V s x
    have a2 := abs_sub_abs_le_abs_sub (y 2) (x 2)
    have a3 := abs_sub_abs_le_abs_sub (y 3) (x 3)
    have e2 : T.T y 2 - T.T x 2 = y 2 - x 2 := by rw [T.shift2, T.shift2]; ring
    have e3 : T.T y 3 - T.T x 3 = y 3 - x 3 := by rw [T.shift3, T.shift3]; ring
    have b2 := abs_sub_abs_le_abs_sub (T.T y 2) (T.T x 2)
    have b3 := abs_sub_abs_le_abs_sub (T.T y 3) (T.T x 3)
    rw [e2] at b2; rw [e3] at b3
    have hy := (boxField_eventuallyEq D (boxL D A) (q := (s, y))
      (by simp only; unfold boxL; linarith) (by simp only; unfold boxL; linarith)).eq_of_nhds
    have hTy := (boxField_eventuallyEq D (boxL D A) (q := (s, T.T y))
      (by simp only; unfold boxL; linarith) (by simp only; unfold boxL; linarith)).eq_of_nhds
    simp only at hy hTy
    change boxField D (boxL D A) s (T.T y) = fderiv ℝ T.T y (boxField D (boxL D A) s y)
    rw [hy, hTy, boxFieldP_map D T hT]
  · change boxField D (boxL D A) s (T.T (flow V s x)) =
      fderiv ℝ T.T (flow V s x) (boxField D (boxL D A) s (flow V s x))
    rw [boxField_time D _ hs, boxField_time D _ hs, map_zero]

theorem boxPhi_deck (T : DeckCore) (hT : T.Preserves D.Om D.a) {x : E4}
    (hx2 : |x 2| ≤ A) (hx3 : |x 3| ≤ A) (hTx2 : |T.T x 2| ≤ A) (hTx3 : |T.T x 3| ≤ A) :
    PhiB D A (T.T x) = T.T (PhiB D A x) :=
  boxFlow_deck D G A T hT hx2 hx3 hTx2 hTx3 1

/-- **Injectivity modulo deck** (docs §5): for starts `x, y` over `[0, 1]²` and `A ≥ 2C_Y + 2`,
`Φ x = T (Φ y)` forces `x = T y`. -/
theorem boxPhi_inj_mod_deck (hA : 2 * Cb D + 2 ≤ A) (T : DeckCore) (hT : T.Preserves D.Om D.a)
    {x y : E4} (hx2 : x 2 ∈ Icc (0 : ℝ) 1) (hx3 : x 3 ∈ Icc (0 : ℝ) 1)
    (hy2 : y 2 ∈ Icc (0 : ℝ) 1) (hy3 : y 3 ∈ Icc (0 : ℝ) 1)
    (h : PhiB D A x = T.T (PhiB D A y)) : x = T.T y := by
  have hV := lfield_boxField D (boxL D A)
  have hC := Cb_nonneg D
  obtain ⟨dx2, dx3⟩ := flow_disp D G (boxL D A) x ⟨zero_le_one, le_rfl⟩
  obtain ⟨dy2, dy3⟩ := flow_disp D G (boxL D A) y ⟨zero_le_one, le_rfl⟩
  have h2 := congrArg (fun z : E4 => z 2) h
  have h3 := congrArg (fun z : E4 => z 3) h
  simp only [T.shift2, T.shift3] at h2 h3
  change flow (boxField D (boxL D A)) 1 x 2 = flow (boxField D (boxL D A)) 1 y 2 + T.m at h2
  change flow (boxField D (boxL D A)) 1 x 3 = flow (boxField D (boxL D A)) 1 y 3 + T.n at h3
  have hm : |(T.m : ℝ)| ≤ 1 + 2 * Cb D := by
    rw [abs_le] at dx2 dy2 ⊢
    constructor <;> linarith [hx2.1, hx2.2, hy2.1, hy2.2]
  have hn : |(T.n : ℝ)| ≤ 1 + 2 * Cb D := by
    rw [abs_le] at dx3 dy3 ⊢
    constructor <;> linarith [hx3.1, hx3.2, hy3.1, hy3.2]
  have hTy2 : |T.T y 2| ≤ A := by
    rw [T.shift2, abs_le]; rw [abs_le] at hm
    constructor <;> linarith [hy2.1, hy2.2]
  have hTy3 : |T.T y 3| ≤ A := by
    rw [T.shift3, abs_le]; rw [abs_le] at hn
    constructor <;> linarith [hy3.1, hy3.2]
  have hy2' : |y 2| ≤ A := by rw [abs_le]; constructor <;> linarith [hy2.1, hy2.2]
  have hy3' : |y 3| ≤ A := by rw [abs_le]; constructor <;> linarith [hy3.1, hy3.2]
  have hd := boxPhi_deck D G A T hT hy2' hy3' hTy2 hTy3
  rw [← hd] at h
  exact hV.flow_injective 1 h

end deck

/-! ### The handle Moser map -/

/-- **The handle Moser map** (`prop:shd4-moser`, box version). For Moser data with deck
generators `G` and a block size `A`, `Φ = PhiB D A` is a `C^∞` diffeomorphism of `E4` (inverse
`PhiBInv D A`, also `C^∞`) such that
* (a) `Φ^*Ω_1 = Ω_0` at every `x` with `|u|, |v| ≤ A` and `p ≤ h + δ`;
* (b) `Φ`, `Φ⁻¹` preserve each of `{p ≤ c}`, `{p < c}`, `{p = c}` for every `c > P_tor`;
* (c) `Φ` and `Φ⁻¹` fix every point of `F`;
* (d) `Φ(T x) = T Φ(x)` for every deck map `T` preserving the data, whenever `x` and `T x` lie
  in the block `|u|, |v| ≤ A`;
* (e) for `A ≥ 2C_Y + 2`: if `x, y` lie over `[0, 1]²` and `Φ x = T Φ y`, then `x = T y`. -/
theorem handle_moser_box (G : DeckGens D.Om D.a) (A : ℝ) :
    ContDiff ℝ ∞ (PhiB D A) ∧ ContDiff ℝ ∞ (PhiBInv D A) ∧
    Function.LeftInverse (PhiBInv D A) (PhiB D A) ∧
    Function.RightInverse (PhiBInv D A) (PhiB D A) ∧
    (∀ x, |x 2| ≤ A → |x 3| ≤ A → pE x ≤ M.h + M.δ → ∀ v w,
      D.Om 1 (PhiB D A x) (fderiv ℝ (PhiB D A) x v) (fderiv ℝ (PhiB D A) x w) =
        D.Om 0 x v w) ∧
    (∀ c, M.Ptor < c → ∀ x,
      (pE (PhiB D A x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiB D A x) < c ↔ pE x < c) ∧
      (pE (PhiB D A x) = c ↔ pE x = c) ∧
      (pE (PhiBInv D A x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiBInv D A x) < c ↔ pE x < c) ∧
      (pE (PhiBInv D A x) = c ↔ pE x = c)) ∧
    (∀ x ∈ M.F, PhiB D A x = x ∧ PhiBInv D A x = x) ∧
    (∀ T : DeckCore, T.Preserves D.Om D.a → ∀ x, |x 2| ≤ A → |x 3| ≤ A →
      |T.T x 2| ≤ A → |T.T x 3| ≤ A → PhiB D A (T.T x) = T.T (PhiB D A x)) ∧
    (2 * Cb D + 2 ≤ A → ∀ T : DeckCore, T.Preserves D.Om D.a → ∀ x y : E4,
      x 2 ∈ Icc (0 : ℝ) 1 → x 3 ∈ Icc (0 : ℝ) 1 → y 2 ∈ Icc (0 : ℝ) 1 → y 3 ∈ Icc (0 : ℝ) 1 →
      PhiB D A x = T.T (PhiB D A y) → x = T.T y) := by
  have hV := lfield_boxField D (boxL D A)
  refine ⟨hV.flow_slice_smooth 1, hV.flowInv_slice_smooth 1, hV.flowInv_flow 1,
    hV.flow_flowInv 1, fun x h2 h3 hx v w => boxFlow_pullback D G A 1 h2 h3 hx v w,
    fun c hc x => ⟨box_sublevel D _ hc 0 x 1, box_lt D _ hc 0 x 1, box_level D _ hc 0 x 1,
      box_sublevel D _ hc 1 x 0, box_lt D _ hc 1 x 0, box_level D _ hc 1 x 0⟩,
    fun x hx => ⟨box_fixes D _ hx 0 1, box_fixes D _ hx 1 0⟩,
    fun T hT x h2 h3 h2' h3' => boxPhi_deck D G A T hT h2 h3 h2' h3',
    fun hA T hT x y hx2 hx3 hy2 hy3 h => boxPhi_inj_mod_deck D G A hA T hT hx2 hx3 hy2 hy3 h⟩

/-! ### The global Moser map (independent of the box) -/

section global

variable (G : DeckGens D.Om D.a)
include G

/-- Base displacement between two times in `[0, 1]`, for any initial time. -/
theorem flowFrom_disp_seg (L t₀ : ℝ) (y : E4) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |flowFrom (boxField D L) t₀ y b 2 - flowFrom (boxField D L) t₀ y a 2| ≤ Cb D ∧
      |flowFrom (boxField D L) t₀ y b 3 - flowFrom (boxField D L) t₀ y a 3| ≤ Cb D := by
  have hV := lfield_boxField D L
  have key : ∀ i : Fin 4, (∀ z : E4, |z i| ≤ baseSpeed z) →
      |flowFrom (boxField D L) t₀ y b i - flowFrom (boxField D L) t₀ y a i| ≤ Cb D := by
    intro i hi
    have hd : ∀ s, HasDerivAt (fun r => flowFrom (boxField D L) t₀ y r i)
        (boxField D L s (flowFrom (boxField D L) t₀ y s) i) s := fun s =>
      (dc i).hasFDerivAt.comp_hasDerivAt s (hV.flowFrom_hasDerivAt t₀ y s)
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun r => flowFrom (boxField D L) t₀ y r i) (a := a) (b := b) (C := Cb D)
      (fun s _ => (hd s).hasDerivWithinAt)
      (fun s _ => by
        rw [Real.norm_eq_abs]
        exact (hi _).trans ((baseSpeed_boxField_le D L s _).trans (baseSpeed_le_Cb D G s _)))
      b ⟨hab, le_rfl⟩
    simp only [Real.norm_eq_abs] at h
    calc _ ≤ Cb D * (b - a) := h
      _ ≤ Cb D * 1 := by gcongr; exacts [Cb_nonneg D, by linarith]
      _ = Cb D := mul_one _
  exact ⟨key 2 fun z => by unfold baseSpeed; linarith [abs_nonneg (z 3)],
    key 3 fun z => by unfold baseSpeed; linarith [abs_nonneg (z 2)]⟩

theorem flowFrom_disp (L : ℝ) {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (y : E4) :
    |flowFrom (boxField D L) t₀ y t 2 - y 2| ≤ Cb D ∧
      |flowFrom (boxField D L) t₀ y t 3 - y 3| ≤ Cb D := by
  have hV := lfield_boxField D L
  have h0 : flowFrom (boxField D L) t₀ y t₀ = y := hV.flowFrom_self t₀ y
  rcases le_total t₀ t with h | h
  · have := flowFrom_disp_seg D G L t₀ y ht₀.1 h ht.2
    rwa [h0] at this
  · have := flowFrom_disp_seg D G L t₀ y ht.1 h ht₀.2
    rw [h0] at this
    exact ⟨by rw [abs_sub_comm]; exact this.1, by rw [abs_sub_comm]; exact this.2⟩

/-- **Independence of the box**: for starts (at a time in `[0, 1]`) in the block `|u|, |v| ≤ A`,
the flows of the box-cut fields with boxes `boxL A ≤ boxL A'` coincide. -/
theorem flowFrom_box_eq {A A' : ℝ} (hA : A ≤ A') {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) {y : E4}
    (h2 : |y 2| ≤ A) (h3 : |y 3| ≤ A) (t : ℝ) :
    flowFrom (boxField D (boxL D A)) t₀ y t = flowFrom (boxField D (boxL D A')) t₀ y t := by
  have hV := lfield_boxField D (boxL D A)
  have hV' := lfield_boxField D (boxL D A')
  have hC := Cb_nonneg D
  refine (hV'.flowFrom_eq ⟨hV.flowFrom_self t₀ y, fun s => ?_⟩ t).symm
  have hd := hV.flowFrom_hasDerivAt t₀ y s
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · obtain ⟨d2, d3⟩ := flowFrom_disp D G (boxL D A) ht₀ hs y
    set z := flowFrom (boxField D (boxL D A)) t₀ y s
    have a2 := abs_sub_abs_le_abs_sub (z 2) (y 2)
    have a3 := abs_sub_abs_le_abs_sub (z 3) (y 3)
    have e1 := (boxField_eventuallyEq D (boxL D A) (q := (s, z))
      (by simp only; unfold boxL; linarith) (by simp only; unfold boxL; linarith)).eq_of_nhds
    have e2 := (boxField_eventuallyEq D (boxL D A') (q := (s, z))
      (by simp only; unfold boxL; linarith) (by simp only; unfold boxL; linarith)).eq_of_nhds
    simp only at e1 e2
    rwa [e2, ← e1]
  · rwa [boxField_time D _ hs, ← boxField_time D (boxL D A') hs
      (flowFrom (boxField D (boxL D A)) t₀ y s)] at hd

end global

/-- **The global handle Moser map** `Φ`: the time-`1` box-cut flow, with the box adapted to the
starting point (independent of the box: `PhiG_eq`). -/
def PhiG (x : E4) : E4 := PhiB D (Aof x) x

/-- **Its inverse** `Φ⁻¹`: the backward box-cut flow from time `1`, box adapted to the point. -/
def PhiGInv (y : E4) : E4 := PhiBInv D (Aof y) y

section global2

variable (G : DeckGens D.Om D.a)
include G

theorem PhiG_eq {A : ℝ} {x : E4} (h2 : |x 2| ≤ A) (h3 : |x 3| ≤ A) : PhiG D x = PhiB D A x := by
  unfold PhiG PhiB flow
  rw [flowFrom_box_eq D G (le_max_left (Aof x) A) ⟨le_rfl, zero_le_one⟩ (le_Aof2 x) (le_Aof3 x),
    flowFrom_box_eq D G (le_max_right (Aof x) A) ⟨le_rfl, zero_le_one⟩ h2 h3]

theorem PhiGInv_eq {A : ℝ} {y : E4} (h2 : |y 2| ≤ A) (h3 : |y 3| ≤ A) :
    PhiGInv D y = PhiBInv D A y := by
  unfold PhiGInv PhiBInv flowInv
  rw [flowFrom_box_eq D G (le_max_left (Aof y) A) ⟨zero_le_one, le_rfl⟩ (le_Aof2 y) (le_Aof3 y),
    flowFrom_box_eq D G (le_max_right (Aof y) A) ⟨zero_le_one, le_rfl⟩ h2 h3]

theorem PhiG_eventuallyEq (x : E4) : PhiG D =ᶠ[𝓝 x] PhiB D (Aof x + 2) := by
  filter_upwards [nhds_block x] with Y hY
  exact PhiG_eq D G (by unfold Aof; linarith [hY.1, abs_nonneg (x 3)])
    (by unfold Aof; linarith [hY.2, abs_nonneg (x 2)])

theorem PhiGInv_eventuallyEq (x : E4) : PhiGInv D =ᶠ[𝓝 x] PhiBInv D (Aof x + 2) := by
  filter_upwards [nhds_block x] with Y hY
  exact PhiGInv_eq D G (by unfold Aof; linarith [hY.1, abs_nonneg (x 3)])
    (by unfold Aof; linarith [hY.2, abs_nonneg (x 2)])

theorem contDiff_PhiG : ContDiff ℝ ∞ (PhiG D) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((handle_moser_box D G (Aof x + 2)).1.contDiffAt).congr_of_eventuallyEq
    (PhiG_eventuallyEq D G x)

theorem contDiff_PhiGInv : ContDiff ℝ ∞ (PhiGInv D) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((handle_moser_box D G (Aof x + 2)).2.1.contDiffAt).congr_of_eventuallyEq
    (PhiGInv_eventuallyEq D G x)

lemma PhiB_disp (A : ℝ) (x : E4) :
    |PhiB D A x 2 - x 2| ≤ Cb D ∧ |PhiB D A x 3 - x 3| ≤ Cb D :=
  flowFrom_disp D G _ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ x

lemma PhiBInv_disp (A : ℝ) (y : E4) :
    |PhiBInv D A y 2 - y 2| ≤ Cb D ∧ |PhiBInv D A y 3 - y 3| ≤ Cb D :=
  flowFrom_disp D G _ ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ y

theorem PhiGInv_PhiG (x : E4) : PhiGInv D (PhiG D x) = x := by
  set A := Aof x + Cb D
  have hC := Cb_nonneg D
  rw [PhiG_eq D G (A := A) (by unfold A; linarith [le_Aof2 x]) (by unfold A; linarith [le_Aof3 x])]
  obtain ⟨d2, d3⟩ := PhiB_disp D G A x
  have a2 := abs_sub_abs_le_abs_sub (PhiB D A x 2) (x 2)
  have a3 := abs_sub_abs_le_abs_sub (PhiB D A x 3) (x 3)
  rw [PhiGInv_eq D G (A := A) (by unfold A; linarith [le_Aof2 x])
    (by unfold A; linarith [le_Aof3 x])]
  exact (lfield_boxField D (boxL D A)).flowInv_flow 1 x

theorem PhiG_PhiGInv (y : E4) : PhiG D (PhiGInv D y) = y := by
  set A := Aof y + Cb D
  have hC := Cb_nonneg D
  rw [PhiGInv_eq D G (A := A) (by unfold A; linarith [le_Aof2 y]) (by unfold A; linarith [le_Aof3 y])]
  obtain ⟨d2, d3⟩ := PhiBInv_disp D G A y
  have a2 := abs_sub_abs_le_abs_sub (PhiBInv D A y 2) (y 2)
  have a3 := abs_sub_abs_le_abs_sub (PhiBInv D A y 3) (y 3)
  rw [PhiG_eq D G (A := A) (by unfold A; linarith [le_Aof2 y])
    (by unfold A; linarith [le_Aof3 y])]
  exact (lfield_boxField D (boxL D A)).flow_flowInv 1 y

/-- **Global Moser identity**: `Φ^*Ω_1 = Ω_0` on `{p ≤ h + δ}`. -/
theorem PhiG_pullback {x : E4} (hx : pE x ≤ M.h + M.δ) (v w : E4) :
    D.Om 1 (PhiG D x) (fderiv ℝ (PhiG D) x v) (fderiv ℝ (PhiG D) x w) = D.Om 0 x v w := by
  have he := PhiG_eventuallyEq D G x
  rw [he.fderiv_eq, he.eq_of_nhds]
  exact (handle_moser_box D G (Aof x + 2)).2.2.2.2.1 x
    (by unfold Aof; linarith [abs_nonneg (x 3)]) (by unfold Aof; linarith [abs_nonneg (x 2)])
    hx v w

/-- **Global deck equivariance** of `Φ`. -/
theorem PhiG_deck (T : DeckCore) (hT : T.Preserves D.Om D.a) (x : E4) :
    PhiG D (T.T x) = T.T (PhiG D x) := by
  set A := Aof x + Aof (T.T x)
  have b1 := le_Aof2 x; have b2 := le_Aof3 x; have b3 := le_Aof2 (T.T x)
  have b4 := le_Aof3 (T.T x); have b5 := abs_nonneg (x 2); have b6 := abs_nonneg (T.T x 2)
  have h2 : |x 2| ≤ A := by unfold A; linarith
  have h3 : |x 3| ≤ A := by unfold A; linarith
  have h2' : |T.T x 2| ≤ A := by unfold A; linarith
  have h3' : |T.T x 3| ≤ A := by unfold A; linarith
  rw [PhiG_eq D G h2' h3', PhiG_eq D G h2 h3]
  exact boxPhi_deck D G A T hT h2 h3 h2' h3'

/-- **Global deck equivariance** of `Φ⁻¹`. -/
theorem PhiGInv_deck (T : DeckCore) (hT : T.Preserves D.Om D.a) (y : E4) :
    PhiGInv D (T.T y) = T.T (PhiGInv D y) := by
  have h := PhiG_deck D G T hT (PhiGInv D y)
  rw [PhiG_PhiGInv D G] at h
  rw [← h, PhiGInv_PhiG D G]

theorem PhiG_level {c : ℝ} (hc : M.Ptor < c) (x : E4) :
    (pE (PhiG D x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiG D x) < c ↔ pE x < c) ∧
      (pE (PhiG D x) = c ↔ pE x = c) := by
  have := (handle_moser_box D G (Aof x)).2.2.2.2.2.1 c hc x
  exact ⟨this.1, this.2.1, this.2.2.1⟩

theorem PhiGInv_level {c : ℝ} (hc : M.Ptor < c) (x : E4) :
    (pE (PhiGInv D x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiGInv D x) < c ↔ pE x < c) ∧
      (pE (PhiGInv D x) = c ↔ pE x = c) := by
  have := (handle_moser_box D G (Aof x)).2.2.2.2.2.1 c hc x
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem PhiG_fixes {x : E4} (hx : x ∈ M.F) : PhiG D x = x ∧ PhiGInv D x = x :=
  (handle_moser_box D G (Aof x)).2.2.2.2.2.2.1 x hx

/-- **The global handle Moser map** (`prop:shd4-moser`): `Φ = PhiG D`, `Φ⁻¹ = PhiGInv D` are
`C^∞`, mutually inverse, `Φ^*Ω_1 = Ω_0` on `{p ≤ h + δ}`, both preserve `{p ≤ c}`, `{p < c}`,
`{p = c}` for `c > P_tor`, fix `F` pointwise and commute with every deck map preserving the
data. -/
theorem handle_moser_global :
    ContDiff ℝ ∞ (PhiG D) ∧ ContDiff ℝ ∞ (PhiGInv D) ∧
    (∀ x, PhiGInv D (PhiG D x) = x) ∧ (∀ y, PhiG D (PhiGInv D y) = y) ∧
    (∀ x, pE x ≤ M.h + M.δ → ∀ v w,
      D.Om 1 (PhiG D x) (fderiv ℝ (PhiG D) x v) (fderiv ℝ (PhiG D) x w) = D.Om 0 x v w) ∧
    (∀ c, M.Ptor < c → ∀ x,
      (pE (PhiG D x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiG D x) < c ↔ pE x < c) ∧
      (pE (PhiG D x) = c ↔ pE x = c) ∧
      (pE (PhiGInv D x) ≤ c ↔ pE x ≤ c) ∧ (pE (PhiGInv D x) < c ↔ pE x < c) ∧
      (pE (PhiGInv D x) = c ↔ pE x = c)) ∧
    (∀ x ∈ M.F, PhiG D x = x ∧ PhiGInv D x = x) ∧
    (∀ T : DeckCore, T.Preserves D.Om D.a → ∀ x,
      PhiG D (T.T x) = T.T (PhiG D x) ∧ PhiGInv D (T.T x) = T.T (PhiGInv D x)) :=
  ⟨contDiff_PhiG D G, contDiff_PhiGInv D G, PhiGInv_PhiG D G, PhiG_PhiGInv D G,
    fun x hx v w => PhiG_pullback D G hx v w,
    fun c hc x => ⟨(PhiG_level D G hc x).1, (PhiG_level D G hc x).2.1, (PhiG_level D G hc x).2.2,
      (PhiGInv_level D G hc x).1, (PhiGInv_level D G hc x).2.1, (PhiGInv_level D G hc x).2.2⟩,
    fun x hx => PhiG_fixes D G hx,
    fun T hT x => ⟨PhiG_deck D G T hT x, PhiGInv_deck D G T hT x⟩⟩

end global2

end field

end SymplecticPacking.Handle
