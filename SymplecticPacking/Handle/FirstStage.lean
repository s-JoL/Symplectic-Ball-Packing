import SymplecticPacking.Handle.Frame
import SymplecticPacking.Handle.Layers
import SymplecticPacking.Bundle.OmegaT

/-!
# Lemmas for the first stage of the handle

`sec:shd-four` (`cons:shd4-eta`, `lem:shd4-eta`): parameter-free lemmas for the first stage
`Ω^{(1)}_λ = Ω₁ + dη_λ`, which is constructed for cubic data in
`Branch2/Model/Cubic/Handle/FirstStage.lean`.

* derivatives of the fibre rotation `chartA` (`fderiv_chartA_2`, `fderiv_chartA_3`,
  `fderiv_chartA_surj`) and transfer of nondegeneracy along pullbacks (`nondeg_pull2_of_inj`,
  `nondeg_of_pull2_surj`);
* the local one-form `GbE G = G(s, w) β`, `β = b(t) dt` (coordinates `(x, y, s, t)` of the
  `𝒜⁺`-frame, `Handle/Twist.lean`), its derivative and smoothness (`hasFDerivAt_GbE_coef`,
  `contDiff_GbE`);
* openness of the annulus and collar sets (`isOpen_annulusE`, `isOpen_collarE`) and smoothness
  helpers (`contDiff_smul_dc`, `contDiff_smul_dc_joint`, `d1_add3`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc wedge wedge_apply d0 d1 pull1 pull2 Form1 Form2 splitForm pf e
  d1_mul_apply)
open SymplecticPacking.Bundle (pE dpE stepA bB u0 u1 annulus annulusPlus lambdaCu lambdaCv
  kappaT kappa1 alpha1 OmegaT OmegaT_split pp contDiff_stepA contDiff_bB contDiff_deriv_stepA)
open SymplecticPacking.Qhat (qhatP qhatInvP QhamP Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

attribute [local irreducible] Bundle.frameA Bundle.Zunit lambdaCu lambdaCv Bundle.etaHu
  Bundle.etaHv Bundle.sigmaC

variable (P : Params)

/-! ### Generic helpers -/

lemma contDiff_pE : ContDiff ℝ ∞ pE := by
  have : pE = fun X => π * ‖wL X‖ ^ 2 := funext pE_eq
  rw [this]; exact contDiff_fibreArea.comp wL.contDiff

lemma d1_eq_zero_of {α : Form1 E4} {X : E4} (h : α =ᶠ[𝓝 X] fun _ => 0) : d1 α X = 0 := by
  rw [d1_congr h]; ext v w; simp [Forms.d1]

lemma fderiv_chartA_2 {X : E4} (hX : X ∈ bandE) (v : E4) : fderiv ℝ chartA X v 2 = v 2 := by
  rw [fderiv_chartA_apply hX]; simp
lemma fderiv_chartA_3 {X : E4} (hX : X ∈ bandE) (v : E4) : fderiv ℝ chartA X v 3 = v 3 := by
  rw [fderiv_chartA_apply hX]; simp

/-- Nondegeneracy pulls back along a map with injective derivative. -/
lemma nondeg_pull2_of_inj {φ : E4 → E4} {Ω : Form2 E4} {Y : E4}
    (hinj : Function.Injective (fderiv ℝ φ Y))
    (hΩ : ∀ v, (∀ w, Ω (φ Y) v w = 0) → v = 0) :
    ∀ v, (∀ w, pull2 φ Ω Y v w = 0) → v = 0 := by
  intro v hv
  have hsurj : Function.Surjective (fderiv ℝ φ Y) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℝ φ Y : E4 →ₗ[ℝ] E4))).mp hinj
  have : fderiv ℝ φ Y v = 0 := hΩ _ fun w => by
    obtain ⟨w', rfl⟩ := hsurj w
    exact hv w'
  exact hinj (this.trans (map_zero _).symm)

/-- Nondegeneracy descends along a map with surjective derivative. -/
lemma nondeg_of_pull2_surj {φ : E4 → E4} {Ω : Form2 E4} {Y : E4}
    (hsurj : Function.Surjective (fderiv ℝ φ Y))
    (h : ∀ v, (∀ w, pull2 φ Ω Y v w = 0) → v = 0) :
    ∀ v, (∀ w, Ω (φ Y) v w = 0) → v = 0 := by
  intro v hv
  obtain ⟨v', rfl⟩ := hsurj v
  rw [h v' fun w => hv _, map_zero]

lemma fderiv_chartA_surj {Y : E4} (hY : Y ∈ bandE) : Function.Surjective (fderiv ℝ chartA Y) := by
  intro v
  refine ⟨fderiv ℝ chartInv (chartA Y) v, ?_⟩
  have hYA : chartA Y ∈ bandE := chartA_mem_band hY
  have hid : chartA ∘ chartInv =ᶠ[𝓝 (chartA Y)] id := by
    filter_upwards [isOpen_bandE.mem_nhds hYA] with Z hZ using chartA_chartInv hZ
  have hc := fderiv_comp (chartA Y)
    (by rw [chartInv_chartA hY]; exact (contDiffAt_chartA hY).differentiableAt (by simp))
    ((contDiffAt_chartInv hYA).differentiableAt (by simp))
  rw [hid.fderiv_eq, fderiv_id, chartInv_chartA hY] at hc
  exact (congrArg (fun L : E4 →L[ℝ] E4 => L v) hc).symm

/-! ### Local forms -/

/-- `γ_sm = e_h (s − 1/6) dt` (`Bundle.gammaSm`). -/
def gsmE : Form1 E4 := fun X => (P.eh * (X 2 - 1 / 6)) • dc 3

/-- `G(s, w) β` for a coefficient `G(s, w)` independent of `t`. -/
def GbE (G : ℝ → ℂ → ℝ) : Form1 E4 := fun X => (G (X 2) (wL X) * bB (X 3)) • dc 3

/-- `dγ_sm + ω_V + d(G β)`; `Ω_pre = OmegaPreG P G_f` (`prop:shd4-third`). -/
def OmegaPreG (G : ℝ → ℂ → ℝ) : Form2 E4 := fun X => d1 (gsmE P) X + omegaV X + d1 (GbE G) X

lemma pp_affine {f : ℝ → ℝ → ℝ → ℝ} {u v : ℝ} {a b : ℝ} (h : ∀ q, f u v q = a + b * q) (p : ℝ) :
    pp f u v p = b := by
  simp only [pp]
  rw [show (fun q => f u v q) = fun q => a + b * q from funext h]
  simpa using ((hasDerivAt_id p).const_mul b).const_add a |>.deriv

/-! ### The square of a twisted form (`prop:shd4-second`) -/

lemma hasFDerivAt_GbE_coef {G : ℝ → ℂ → ℝ} {X : E4}
    (hG : DifferentiableAt ℝ (fun z : ℝ × ℂ => G z.1 z.2) (X 2, wL X)) :
    HasFDerivAt (fun Y : E4 => G (Y 2) (wL Y) * bB (Y 3))
      (bB (X 3) • (fderiv ℝ (fun z : ℝ × ℂ => G z.1 z.2) (X 2, wL X)).comp ((dc 2).prod wL) +
        G (X 2) (wL X) • (deriv bB (X 3) • dc 3)) X := by
  have h1 := hG.hasFDerivAt.comp X ((dc 2).prod wL).hasFDerivAt
  have hb : HasFDerivAt (fun Y : E4 => bB (Y 3)) (deriv bB (X 3) • dc 3) X :=
    ((contDiff_bB.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt X (dc 3).hasFDerivAt
  have h := h1.mul hb
  exact h.congr_fderiv (add_comm _ _)

lemma wL_decomp (v : E4) : wL v = (v 0 : ℝ) • (1 : ℂ) + (v 1 : ℝ) • Complex.I := by
  apply Complex.ext <;> simp

/-! ### The first-stage primitive (`cons:shd4-eta`) -/

lemma contDiff_smul_dc {g : E4 → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 4) :
    ContDiff ℝ ∞ (fun Y => g Y • dc i) := hg.smul contDiff_const

lemma contDiff_smul_dc_joint {g : ℝ × E4 → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 4) :
    ContDiff ℝ ∞ (fun z => g z • dc i) := hg.smul contDiff_const

/-- The `β`-coefficient of `η_λ`: `f(s)[H*(p(q_λ⁻¹ q_{λ f(s)} w)) − H*(p(w))] b(t)`. -/
def etaCoef (lam : ℝ) (X : E4) : ℝ :=
  stepA (X 2) * (P.Hstar (π * ‖qhatInvP P lam (qhatP P (lam * stepA (X 2)) (wL X))‖ ^ 2) -
    P.Hstar (pE X)) * bB (X 3)

/-- **The first-stage primitive on `𝒜 × ℂ`** (`cons:shd4-eta`):
`η_λ = (Q^λ_s ∘ q_{λ f(s)}) ds + f(s)[H*(p(q_λ⁻¹ q_{λ f(s)} w)) − H*(p(w))] β`. -/
def etaLoc (lam : ℝ) : Form1 E4 := fun X => PhiS P lam X • dc 2 + etaCoef P lam X • dc 3

open Classical in
/-- **The first-stage primitive on `N`**: the zero extension of `η_λ` from `𝒜`, in the global
`Zunit`-frame (the local form is transported by `chartInv`; it has only base components). -/
def eta (lam : ℝ) : Form1 E4 := fun X =>
  if X 2 ∈ annulus then etaLoc P lam (chartInv X) else 0

/-- **The first stage** `Ω^{(1)}_λ = Ω₁ + dη_λ` (`cons:shd4-eta`). -/
def firstStage (lam : ℝ) : Form2 E4 := fun X => OmegaT P 1 X + d1 (eta P lam) X

lemma isOpen_annulusE : IsOpen {X : E4 | X 2 ∈ annulus} :=
  isOpen_Ioo.preimage (dc 2).continuous

lemma isOpen_collarE : IsOpen {X : E4 | X 2 < u0 ∨ u1 < X 2} :=
  (isOpen_lt (dc 2).continuous continuous_const).union
    (isOpen_lt continuous_const (dc 2).continuous)

/-! ### The first-stage identity (`lem:shd4-eta` (c)) -/

lemma contDiff_GbE {G : ℝ → ℂ → ℝ} (hG : ContDiff ℝ ∞ (fun z : ℝ × ℂ => G z.1 z.2)) :
    ContDiff ℝ ∞ (GbE G) :=
  contDiff_smul_dc ((hG.comp ((dc 2).contDiff.prodMk wL.contDiff)).mul
    (contDiff_bB.comp (dc 3).contDiff)) 3

lemma d1_add3 {α β γ : Form1 E4} {X : E4} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hγ : ContDiff ℝ ∞ γ) : d1 (fun Y => α Y + β Y + γ Y) X = d1 α X + d1 β X + d1 γ X := by
  have d := fun (f : Form1 E4) (h : ContDiff ℝ ∞ f) => h.differentiable (by simp) X
  have e1 : (fun Y => α Y + β Y + γ Y) = (α + β) + γ := rfl
  rw [e1, Forms.d1_add_apply ((d α hα).add (d β hβ)) (d γ hγ),
    Forms.d1_add_apply (d α hα) (d β hβ)]

/-! ### The first stage is symplectic (`prop:shd4-second`) -/

end SymplecticPacking.Handle
