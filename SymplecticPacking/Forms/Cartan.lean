import Mathlib
import SymplecticPacking.Forms.Basic

/-!
# The exact Moser / Cartan lemma for a family of maps

Setting: `φ : ℝ → E → F` jointly smooth in `(t, x)`, with values in an open set `U ⊆ F`, and
`∂ₜ φ t x = V t (φ t x)` (no regularity of `V` itself is needed). For a (possibly time-dependent)
smooth 1-form `λ` on `U` we prove:

* `pull2_d1_const_of_dt`: if `φₜ^*(ι_{Vₜ} dλₜ + ∂ₜλₜ) = 0` for all `t`, then `φₜ^*(dλₜ)` is
  independent of `t`.
* `pull2_d1_const`: the special case of a time-independent `λ`.

Method: everything is moved to `ℝ × E`. For a `C²` 1-form `A` on `ℝ × E` with
`dA((1,0),(0,w)) ≡ 0`, closedness of `dA` gives `∂ₜ dA((0,v),(0,w)) = 0` (`d1_space_const`).
We apply this to `A = Ψ^* B` with `Ψ(t,x) = (t, φ t x)` and `B(t,y)(s,u) = λₜ(y) u`.
As in `Forms/Basic.lean`, derivatives of 2-form fields are only handled after evaluation.
-/

noncomputable section

namespace SymplecticPacking.Forms

open ContinuousLinearMap Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Contraction `ι_V Ω` of a 2-form with a vector field. -/
def contract (V : F → F) (Ω : Form2 F) : Form1 F := fun y => Ω y (V y)

@[simp] lemma contract_apply (V : F → F) (Ω : Form2 F) (y w : F) :
    contract V Ω y w = Ω y (V y) w := rfl

/-- Time derivative `∂ₜλₜ` of a time-dependent 1-form. -/
def dtForm (Λ : ℝ → Form1 F) (t : ℝ) : Form1 F := fun y => deriv (fun s => Λ s y) t

/-! ### Partial derivatives on `ℝ × E` -/

section partials

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma hasDerivAt_time {G : ℝ × E → H} {t : ℝ} {x : E} (h : DifferentiableAt ℝ G (t, x)) :
    HasDerivAt (fun s => G (s, x)) (fderiv ℝ G (t, x) (1, 0)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact h.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, x)) t h1

lemma hasFDerivAt_space {G : ℝ × E → H} {t : ℝ} {x : E} (h : DifferentiableAt ℝ G (t, x)) :
    HasFDerivAt (fun y => G (t, y)) ((fderiv ℝ G (t, x)).comp (inr ℝ ℝ E)) x :=
  h.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

lemma fderiv_space {G : ℝ × E → H} {t : ℝ} {x : E} (h : DifferentiableAt ℝ G (t, x)) (v : E) :
    fderiv ℝ (fun y => G (t, y)) x v = fderiv ℝ G (t, x) (0, v) := by
  rw [(hasFDerivAt_space h).fderiv]; rfl

end partials

lemma fderiv_eval1 {E' Y : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {A : E' → Y →L[ℝ] ℝ}
    {q : E'} (h : DifferentiableAt ℝ A q) (u : E') (z : Y) :
    fderiv ℝ (fun p => A p z) q u = fderiv ℝ A q u z := by
  rw [fderiv_clm_apply h (differentiableAt_const z)]
  simp

/-! ### The core lemma on `ℝ × E` -/

/-- If `A` is a `C²` 1-form on `ℝ × E` with `dA((1,0), (0,w)) = 0` everywhere, then the
spatial part `dA((0,v),(0,w))` at `(t,x)` does not depend on `t`. -/
theorem d1_space_const {A : Form1 (ℝ × E)} (hA : ∀ q, ContDiffAt ℝ 2 A q)
    (h : ∀ q w, d1 A q (1, 0) (0, w) = 0) (t : ℝ) (x v w : E) :
    d1 A (t, x) (0, v) (0, w) = d1 A (0, x) (0, v) (0, w) := by
  have hD : ∀ q, DifferentiableAt ℝ (fderiv ℝ A) q := fun q =>
    differentiableAt_fderiv_of_contDiffAt (hA q)
  have he : ∀ b c, (fun p => d1 A p b c) = fun p => fderiv ℝ A p b c - fderiv ℝ A p c b :=
    fun b c => funext fun p => rfl
  have hdd : ∀ q b c, DifferentiableAt ℝ (fun p => d1 A p b c) q := by
    intro q b c
    rw [he]
    exact (differentiableAt_eval2 (hD q) b c).sub (differentiableAt_eval2 (hD q) c b)
  -- derivative of `dA(b,c)` in direction `a`, in terms of the second derivative of `A`
  have hT : ∀ q a b c, fderiv ℝ (fderiv ℝ A) q a b c - fderiv ℝ (fderiv ℝ A) q a c b =
      fderiv ℝ (fun p => d1 A p b c) q a := by
    intro q a b c
    rw [he, fderiv_fun_sub (differentiableAt_eval2 (hD q) b c)
      (differentiableAt_eval2 (hD q) c b)]
    simp [fderiv_eval2 (hD q)]
  have hz : ∀ q a c, fderiv ℝ (fun p => d1 A p (1, 0) (0, c)) q a = 0 := by
    intro q a c
    have : (fun p => d1 A p (1, 0) (0, c)) = fun _ => 0 := funext fun p => h p c
    rw [this]; simp
  have hderiv : ∀ s, HasDerivAt (fun s => d1 A (s, x) (0, v) (0, w)) 0 s := by
    intro s
    have h1 := hasDerivAt_time (G := fun q => d1 A q (0, v) (0, w)) (hdd (s, x) _ _)
    convert h1 using 1
    rw [← hT]
    have s1 : ∀ a b c, fderiv ℝ (fderiv ℝ A) (s, x) a b c = fderiv ℝ (fderiv ℝ A) (s, x) b a c :=
      fun a b c => DFunLike.congr_fun (symm2 (hA _) a b) c
    have k1 := hT (s, x) (0, v) (1, 0) (0, w)
    have k2 := hT (s, x) (0, w) (1, 0) (0, v)
    rw [hz] at k1 k2
    rw [s1 (1, 0) (0, v), s1 (0, v) (0, w), s1 (1, 0) (0, w)] at *
    linarith
  have hdiff : Differentiable ℝ (fun s => d1 A (s, x) (0, v) (0, w)) :=
    fun s => (hderiv s).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun s => (hderiv s).deriv) t 0

/-! ### Derivatives of the family -/

section family

variable {φ : ℝ → E → F} {V : ℝ → F → F}

lemma fderiv_family_time (hΦ : Differentiable ℝ (fun p : ℝ × E => φ p.1 p.2))
    (hV : ∀ t x, HasDerivAt (fun s => φ s x) (V t (φ t x)) t) (t : ℝ) (x : E) :
    fderiv ℝ (fun p : ℝ × E => φ p.1 p.2) (t, x) (1, 0) = V t (φ t x) :=
  (hasDerivAt_time (hΦ (t, x))).unique (hV t x)

lemma fderiv_family_space (hΦ : Differentiable ℝ (fun p : ℝ × E => φ p.1 p.2)) (t : ℝ)
    (x v : E) : fderiv ℝ (fun p : ℝ × E => φ p.1 p.2) (t, x) (0, v) = fderiv ℝ (φ t) x v :=
  (fderiv_space (G := fun p : ℝ × E => φ p.1 p.2) (hΦ (t, x)) v).symm

end family

/-! ### Cartan's formula along a family (time-independent form) -/

section cartan

variable {φ : ℝ → E → F} {V : ℝ → F → F} {U : Set F} {lam : Form1 F}

end cartan

/-! ### Exact Moser lemma: time-dependent form -/

section moser

variable {φ : ℝ → E → F} {V : ℝ → F → F} {U : Set F}

/-- Exact Moser lemma for a family of maps and a time-dependent 1-form `Λ t` on an open set `U`:
if `φₜ^*(ι_{Vₜ} dΛₜ + ∂ₜΛₜ) = 0` for all `t`, then `φₜ^*(dΛₜ) = φ₀^*(dΛ₀)`. -/
theorem pull2_d1_const_of_dt {Λ : ℝ → Form1 F} (hU : IsOpen U)
    (hΛ : ContDiffOn ℝ ∞ (fun p : ℝ × F => Λ p.1 p.2) (univ ×ˢ U))
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2)) (hφU : ∀ t x, φ t x ∈ U)
    (hV : ∀ t x, HasDerivAt (fun s => φ s x) (V t (φ t x)) t)
    (hyp : ∀ t, pull1 (φ t) (contract (V t) (d1 (Λ t)) + dtForm Λ t) = 0) (t : ℝ) :
    pull2 (φ t) (d1 (Λ t)) = pull2 (φ 0) (d1 (Λ 0)) := by
  set Φ : ℝ × E → F := fun p => φ p.1 p.2 with hΦdef
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  set L : ℝ × F → F →L[ℝ] ℝ := fun p => Λ p.1 p.2 with hLdef
  have hLat : ∀ s y, y ∈ U → ContDiffAt ℝ ∞ L (s, y) := fun s y hy =>
    hΛ.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨trivial, hy⟩)
  set B : Form1 (ℝ × F) := fun p => (L p).comp (snd ℝ ℝ F) with hBdef
  have hBat : ∀ s y, y ∈ U → ContDiffAt ℝ ∞ B (s, y) := fun s y hy =>
    (hLat s y hy).clm_comp contDiffAt_const
  set Ψ : ℝ × E → ℝ × F := fun q => (q.1, Φ q) with hΨdef
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_fst.prodMk hΦ
  have hΨd : ∀ q, HasFDerivAt Ψ ((fst ℝ ℝ E).prod (fderiv ℝ Φ q)) q := fun q =>
    (hasFDerivAt_fst).prodMk (hΦd q).hasFDerivAt
  have hΨt : ∀ s x, fderiv ℝ Ψ (s, x) (1, 0) = (1, V s (φ s x)) := by
    intro s x
    rw [(hΨd _).fderiv, prod_apply, fderiv_family_time hΦd hV]; rfl
  have hΨx : ∀ s x u, fderiv ℝ Ψ (s, x) (0, u) = (0, fderiv ℝ (φ s) x u) := by
    intro s x u
    rw [(hΨd _).fderiv, prod_apply, fderiv_family_space hΦd]; rfl
  set A : Form1 (ℝ × E) := pull1 Ψ B with hAdef
  have hAc : ∀ q, ContDiffAt ℝ 2 A q := by
    intro q
    have h0 : ContDiffAt ℝ ∞ B (Ψ q) := hBat q.1 (Φ q) (hφU q.1 q.2)
    have h1 : ContDiffAt ℝ ∞ (B ∘ Ψ) q := h0.comp q hΨ.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fderiv ℝ Ψ) q :=
      (hΨ.fderiv_right (m := ∞) (by simp)).contDiffAt
    exact (h1.clm_comp h2).of_le (by simp)
  have hd1 : ∀ q, d1 A q = pull2 Ψ (d1 B) q := fun q =>
    pull2_d1_apply (hΨ.contDiffAt.of_le (by simp))
      ((hBat q.1 (Φ q) (hφU q.1 q.2)).differentiableAt (by simp))
  -- partial derivatives of `L`
  have hLd : ∀ s y, y ∈ U → DifferentiableAt ℝ L (s, y) := fun s y hy =>
    (hLat s y hy).differentiableAt (by simp)
  have hLt : ∀ s y, y ∈ U → fderiv ℝ L (s, y) (1, 0) = dtForm Λ s y := fun s y hy =>
    ((hasDerivAt_time (hLd s y hy)).deriv).symm
  have hLx : ∀ s y u, y ∈ U → fderiv ℝ L (s, y) (0, u) = fderiv ℝ (Λ s) y u := fun s y u hy =>
    (fderiv_space (G := L) (hLd s y hy) u).symm
  have hBf : ∀ s y z w, y ∈ U → fderiv ℝ B (s, y) z w = fderiv ℝ L (s, y) z w.2 := by
    intro s y z w hy
    have hBd : DifferentiableAt ℝ B (s, y) := (hBat s y hy).differentiableAt (by simp)
    rw [← fderiv_eval1 hBd]
    have : (fun p => B p w) = fun p => L p w.2 := rfl
    rw [this, fderiv_eval1 (hLd s y hy)]
  -- the two components of `dB`
  have hB1 : ∀ s y a w, y ∈ U →
      d1 B (s, y) (1, a) (0, w) = dtForm Λ s y w + d1 (Λ s) y a w := by
    intro s y a w hy
    have hsplit : ((1 : ℝ), a) = ((1 : ℝ), (0 : F)) + (0, a) := by simp
    rw [d1_apply, hBf s y _ _ hy, hBf s y _ _ hy, hsplit, map_add, add_apply, hLt s y hy,
      hLx s y a hy, hLx s y w hy, d1_apply]
    simp only [Prod.snd_add, zero_add]
    ring
  have hB2 : ∀ s y u w, y ∈ U → d1 B (s, y) (0, u) (0, w) = d1 (Λ s) y u w := by
    intro s y u w hy
    rw [d1_apply, hBf s y _ _ hy, hBf s y _ _ hy, hLx s y u hy, hLx s y w hy, d1_apply]
  -- apply the core lemma
  have hcore : ∀ q w, d1 A q (1, 0) (0, w) = 0 := by
    rintro ⟨s, x⟩ w
    rw [hd1, pull2_apply, hΨt, hΨx]
    change d1 B (s, φ s x) _ _ = 0
    rw [hB1 s _ _ _ (hφU s x)]
    have h := congrArg (fun α : Form1 E => α x w) (hyp s)
    simp only [pull1_apply, Pi.add_apply, add_apply, contract_apply] at h
    simpa [add_comm] using h
  have hrep : ∀ s x v w, pull2 (φ s) (d1 (Λ s)) x v w = d1 A (s, x) (0, v) (0, w) := by
    intro s x v w
    rw [hd1, pull2_apply Ψ, hΨx, hΨx]
    change _ = d1 B (s, φ s x) _ _
    rw [hB2 s _ _ _ (hφU s x), pull2_apply]
  funext x
  ext v w
  rw [hrep, hrep]
  exact d1_space_const hAc hcore t x v w

/-- Exact Moser lemma for a family of maps and a fixed 1-form `λ` on an open set `U`:
if `Vₜ` is `dλ`-orthogonal to the image of every `Dφₜ`, i.e. `φₜ^*(ι_{Vₜ} dλ) = 0`, then
`φₜ^*(dλ) = φ₀^*(dλ)`. -/
theorem pull2_d1_const {lam : Form1 F} (hU : IsOpen U) (hlam : ContDiffOn ℝ ∞ lam U)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2)) (hφU : ∀ t x, φ t x ∈ U)
    (hV : ∀ t x, HasDerivAt (fun s => φ s x) (V t (φ t x)) t)
    (hyp : ∀ t, pull1 (φ t) (contract (V t) (d1 lam)) = 0) (t : ℝ) :
    pull2 (φ t) (d1 lam) = pull2 (φ 0) (d1 lam) := by
  have hdt : ∀ s, dtForm (fun _ => lam) s = 0 := fun s => by
    funext y; simp [dtForm]
  refine pull2_d1_const_of_dt (Λ := fun _ => lam) hU ?_ hΦ hφU hV ?_ t
  · exact hlam.comp contDiffOn_snd (fun p hp => hp.2)
  · intro s; rw [hdt, add_zero]; exact hyp s

end moser

/-! ### Global versions (`U = univ`) -/

section global

variable {φ : ℝ → E → F} {V : ℝ → F → F}

theorem pull2_d1_const_of_dt_univ {Λ : ℝ → Form1 F}
    (hΛ : ContDiff ℝ ∞ (fun p : ℝ × F => Λ p.1 p.2))
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2))
    (hV : ∀ t x, HasDerivAt (fun s => φ s x) (V t (φ t x)) t)
    (hyp : ∀ t, pull1 (φ t) (contract (V t) (d1 (Λ t)) + dtForm Λ t) = 0) (t : ℝ) :
    pull2 (φ t) (d1 (Λ t)) = pull2 (φ 0) (d1 (Λ 0)) :=
  pull2_d1_const_of_dt (U := univ) isOpen_univ hΛ.contDiffOn hΦ (fun _ _ => trivial) hV hyp t

theorem pull2_d1_const_univ {lam : Form1 F} (hlam : ContDiff ℝ ∞ lam)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2))
    (hV : ∀ t x, HasDerivAt (fun s => φ s x) (V t (φ t x)) t)
    (hyp : ∀ t, pull1 (φ t) (contract (V t) (d1 lam)) = 0) (t : ℝ) :
    pull2 (φ t) (d1 lam) = pull2 (φ 0) (d1 lam) :=
  pull2_d1_const (U := univ) isOpen_univ hlam.contDiffOn hΦ (fun _ _ => trivial) hV hyp t

end global

end SymplecticPacking.Forms
