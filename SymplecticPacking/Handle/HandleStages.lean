import SymplecticPacking.Handle.HandlePer

/-!
# Families of forms, the fibre rotation and the three fibres

`sec:shd-four` (`cons:shd4-moser`): parameter-free ingredients of the three stages of the handle
Moser path, which are constructed for cubic data in
`Branch2/Model/Cubic/Handle/HandleStages.lean`.

* calculus for families `E : ℝ × E4 → E4 →L[ℝ] ℝ`: `contDiff_d1_family`, the `λ`-derivative
  `famDot E`, and `hasDerivAt_d1_family` (`∂_λ dE_λ = d ∂_λE_λ`, by symmetry of second
  derivatives);
* `IsDeck T`: `T` is one of the two deck maps `deckU`, `deckV`;
* the fibre rotation field `Rrot = 2π(−y ∂_x + x ∂_y)` and the rotations `rotE s`;
* `fibreSetH`: the three fibres `N_{b_j}`, all lifts to the cover.
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e symm2)
open SymplecticPacking.Bundle (pE dpE u0 u1 annulus stepA bB OmegaT alpha1E Omega0loc)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

/-! ### Calculus for families of one-forms -/

section family

variable {E : ℝ × E4 → (E4 →L[ℝ] ℝ)}

lemma fderiv_apply_const {Q H Y : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {B : Q → Y →L[ℝ] H} {x : Q} (h : DifferentiableAt ℝ B x) (z : Y) (u : Q) :
    fderiv ℝ (fun q => B q z) x u = fderiv ℝ B x u z := by
  rw [fderiv_clm_apply h (differentiableAt_const z)]
  simp

lemma fderiv_family_space (hs : ContDiff ℝ ∞ E) (s : ℝ) (X v : E4) :
    fderiv ℝ (fun Y => E (s, Y)) X v = fderiv ℝ E (s, X) (0, v) :=
  Forms.fderiv_space ((hs.differentiable (by simp)) (s, X)) v

lemma d1_family_apply (hs : ContDiff ℝ ∞ E) (s : ℝ) (X v w : E4) :
    d1 (fun Y => E (s, Y)) X v w = fderiv ℝ E (s, X) (0, v) w - fderiv ℝ E (s, X) (0, w) v := by
  rw [Forms.d1_apply, fderiv_family_space hs, fderiv_family_space hs]

lemma contDiff_fderiv_fam (hs : ContDiff ℝ ∞ E) : ContDiff ℝ ∞ (fderiv ℝ E) :=
  (contDiff_infty_iff_fderiv.mp hs).2

theorem contDiff_d1_family (hs : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (fun q : ℝ × E4 => d1 (fun Y => E (q.1, Y)) q.2) := by
  have hD := contDiff_fderiv_fam hs
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  have e : (fun q : ℝ × E4 => d1 (fun Y => E (q.1, Y)) q.2 v w) =
      fun q => fderiv ℝ E q (0, v) w - fderiv ℝ E q (0, w) v :=
    funext fun q => d1_family_apply hs q.1 q.2 v w
  rw [e]
  exact ((hD.clm_apply contDiff_const).clm_apply contDiff_const).sub
    ((hD.clm_apply contDiff_const).clm_apply contDiff_const)

/-- The `λ`-derivative of the family, `∂_λ E`. -/
def famDot (E : ℝ × E4 → (E4 →L[ℝ] ℝ)) (q : ℝ × E4) : E4 →L[ℝ] ℝ := fderiv ℝ E q (1, 0)

lemma contDiff_famDot (hs : ContDiff ℝ ∞ E) : ContDiff ℝ ∞ (famDot E) :=
  (contDiff_fderiv_fam hs).clm_apply contDiff_const

/-- **`∂_λ dE_λ = d ∂_λ E_λ`**. -/
theorem hasDerivAt_d1_family (hs : ContDiff ℝ ∞ E) (lam : ℝ) (X v w : E4) :
    HasDerivAt (fun s => d1 (fun Y => E (s, Y)) X v w)
      (d1 (fun Y => famDot E (lam, Y)) X v w) lam := by
  have hD : Differentiable ℝ (fderiv ℝ E) :=
    (contDiff_fderiv_fam hs).differentiable (by simp)
  have hg : ∀ z : E4, ∀ a : E4, HasDerivAt (fun s => fderiv ℝ E (s, X) (0, z) a)
      (fderiv ℝ (fderiv ℝ E) (lam, X) (1, 0) (0, z) a) lam := by
    intro z a
    have hdiff : DifferentiableAt ℝ (fun q => fderiv ℝ E q (0, z) a) (lam, X) := by
      have := (hD (lam, X))
      fun_prop
    have h := Forms.hasDerivAt_time hdiff
    rwa [fderiv_apply_const (B := fun q => fderiv ℝ E q (0, z)) (by fun_prop),
      fderiv_apply_const (hD _)] at h
  have e : (fun s => d1 (fun Y => E (s, Y)) X v w) =
      fun s => fderiv ℝ E (s, X) (0, v) w - fderiv ℝ E (s, X) (0, w) v :=
    funext fun s => d1_family_apply hs s X v w
  rw [e]
  have hdot : ContDiff ℝ ∞ (famDot E) := contDiff_famDot hs
  have rhs : d1 (fun Y => famDot E (lam, Y)) X v w =
      fderiv ℝ (fderiv ℝ E) (lam, X) (0, v) (1, 0) w -
        fderiv ℝ (fderiv ℝ E) (lam, X) (0, w) (1, 0) v := by
    rw [d1_family_apply hdot]
    unfold famDot
    rw [fderiv_apply_const (B := fderiv ℝ E) (hD _), fderiv_apply_const (B := fderiv ℝ E) (hD _)]
  have h2 : ContDiffAt ℝ 2 E (lam, X) := hs.contDiffAt.of_le (by simp)
  rw [rhs, symm2 h2 (0, v) (1, 0), symm2 h2 (0, w) (1, 0)]
  exact (hg v w).sub (hg w v)

end family

/-! ### The periodised primitives -/

variable (P : Params)

/-! ### Horizontality and deck invariance of the primitives -/

/-- The two deck maps. -/
def IsDeck (T : DeckCore) : Prop := T = deckU ∨ T = deckV

/-! ### The parameters of the handle Moser problem -/

open SymplecticPacking.Qhat (Psupp)
open SymplecticPacking.Bundle (bpoints)

/-- The fibre rotation field `R = 2π(−y ∂_x + x ∂_y)` (`ι_R ω_V = −dp`). -/
def Rrot (X : E4) : E4 := mk ((2 * π : ℝ) • (_root_.Complex.I * wL X)) 0 0

/-- **The three fibres** `N_{b_j}`, all lifts to the cover. -/
def fibreSetH : Set E4 :=
  {X | ∃ j : Fin 3, ∃ m n : ℤ, X 2 = (bpoints j).1 + m ∧ X 3 = (bpoints j).2 + n}

/-! ### Representations as `d` of global primitives (closedness, skewness) -/

open SymplecticPacking.Return (betaLoc)

/-! ### Toricity near the boundary -/

lemma Rrot_apply (X : E4) : Rrot X 0 = -(2 * π * X 1) ∧ Rrot X 1 = 2 * π * X 0 ∧
    Rrot X 2 = 0 ∧ Rrot X 3 = 0 := by
  simp [Rrot]

lemma famDot_eq_zero {E : ℝ × E4 → (E4 →L[ℝ] ℝ)} {q : ℝ × E4} (h : E =ᶠ[𝓝 q] fun _ => 0) :
    famDot E q = 0 := by
  unfold famDot; rw [h.fderiv_eq]; simp

/-- The fibre rotation by the angle `2πs`. -/
def rotE (s : ℝ) (X : E4) : E4 := mk (_root_.Complex.exp (((2 * π * s : ℝ) : ℂ) * _root_.Complex.I) * wL X) (X 2) (X 3)

lemma hasDerivAt_rotE (X : E4) : HasDerivAt (fun s => rotE s X) (Rrot X) 0 := by
  have hc : HasDerivAt (fun s : ℝ => _root_.Complex.exp (((2 * π * s : ℝ) : ℂ) * _root_.Complex.I) * wL X)
      ((2 * π : ℝ) • (_root_.Complex.I * wL X)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (((2 * π * s : ℝ) : ℂ) * _root_.Complex.I))
        (((2 * π : ℝ) : ℂ) * _root_.Complex.I) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * π)).ofReal_comp.mul_const _root_.Complex.I
      simpa using this
    have := (h1.cexp).mul_const (wL X)
    convert this using 1
    simp [Complex.real_smul]; ring
  have h := mkL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc.prodMk
    ((hasDerivAt_const (0 : ℝ) (X 2)).prodMk (hasDerivAt_const (0 : ℝ) (X 3))))
  exact h

lemma rotE_coords (s : ℝ) (X : E4) : rotE s X 2 = X 2 ∧ rotE s X 3 = X 3 ∧ pE (rotE s X) = pE X := by
  refine ⟨by simp [rotE], by simp [rotE], ?_⟩
  simp only [rotE, pE_mk, norm_mul, Complex.norm_exp]
  simp [pE_eq]

/-! ### The three fibres -/

lemma bpoints_fst (j : Fin 3) : (bpoints j).1 ∉ Icc u0 u1 := by
  fin_cases j <;> simp [bpoints, u0, u1] <;> norm_num

lemma fract_fibre {X : E4} (hX : X ∈ fibreSetH) : ∃ j : Fin 3, Int.fract (X 2) = (bpoints j).1 ∧
    ∃ n : ℤ, X 3 = (bpoints j).2 + n := by
  obtain ⟨j, m, n, h2, h3⟩ := hX
  refine ⟨j, ?_, n, h3⟩
  rw [h2, Int.fract_add_intCast, Int.fract_eq_self.mpr (Bundle.bpoints_fst_mem j)]

lemma bB_fibre {X : E4} (hX : X ∈ fibreSetH) : bB (X 3) = 0 := by
  obtain ⟨j, -, n, hn⟩ := fract_fibre hX
  have hp : Function.Periodic bB 1 := fun v => Bundle.bB_add_one v
  rw [hn, show (n : ℝ) = n * 1 by ring, hp.int_mul n]
  exact (bB_eventually_zero j).self_of_nhds

end SymplecticPacking.Handle
