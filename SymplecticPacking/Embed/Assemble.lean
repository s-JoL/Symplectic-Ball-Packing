import SymplecticPacking.Embed.Deck
import SymplecticPacking.Embed.Spec
import SymplecticPacking.Return.AvoidL
import SymplecticPacking.Return.BallChartRep

/-!
# Smoothness lemmas for the capacity-scale embeddings

`sec:rtc-packing`: ingredients of the embeddings `fcap P Φ⁻¹ i = b_ball ∘ 𝒯 ∘ Ncoord ∘ f_i^N`
(`rem:shd-four`), which are assembled for cubic data in
`Branch2/Model/Cubic/Embed/Assemble.lean`. Here `Ncoord (x, y, u, v) = (Zunit u v, x + iy)`,
`𝒯 = ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ ι` is `Return.compositeT` and the ball chart `b_ball` is read in `E4` by
`c2ToE4`.

* smoothness of `Ncoord`, `Return.compositeT` and the ball chart (`contDiff_Ncoord`,
  `contDiffAt_compositeT`, `contDiffAt_ballChart`); `c2ToE4_injective`, `ballChart_inj`;
* `bump X₀ r : E4 → B(X₀, r)`, a global smooth map with `bump 0 = X₀` and derivative `id` at
  `0` (`bump_zero`, `contDiff_bump`, `bump_mem`, `fderiv_bump`). The pullback identities of
  `sec:rtc` (`compositeT_pullback`, `ballChart_symplectic_rep`) are stated for global smooth
  families; they are applied to `Ncoord ∘ f_i^N ∘ bump X₀ r`.
-/

noncomputable section

namespace SymplecticPacking.Embed

open _root_.Complex ComplexConjugate Set Metric Filter Topology
open SymplecticPacking.Forms (Form2 pull2 pull2_apply)
open SymplecticPacking.Return (Ncoord C3 NDom compositeT compositeBall ballChart c2ToE4 nsq nsq2
  injection OmegaE)
open SymplecticPacking.Strip (fN srcBall rhoHat PhiInvSpec)
open scoped Real ContDiff

/-! ### Definitions -/

section defs

variable (P : Params)

end defs

/-! ### Parameters -/

section params

variable (P : Params)

end params

/-! ### Smoothness of the pieces -/

lemma contDiff_Ncoord : ContDiff ℝ ∞ Ncoord := by
  have e : Ncoord = fun Y : E4 => (Bundle.Zunit (Y 2) (Y 3), Return.fibreCLM Y) := by
    funext Y; simp [Ncoord, Return.fibreCLM_apply]
  rw [e]
  exact Return.contDiff_Zpart.prodMk Return.fibreCLM.contDiff

lemma contDiffAt_compositeT {dn h : ℝ} (hdn : 0 < dn) (hdn3 : dn < 1 / 3) {x : C3 × ℂ}
    (hx : Return.pN x.2 < dn) : ContDiffAt ℝ ∞ (compositeT dn h) x := by
  have h1 : ContDiff ℝ ∞ (fun y : C3 × ℂ =>
      Return.returnFlowInv dn 1 (Return.transport dn (Return.wOf dn h) 1 y).1) :=
    (Return.returnFlowInv_smooth hdn3.le).comp (contDiff_const.prodMk
      (contDiff_fst.comp ((Return.transport_smooth hdn hdn3.le _).comp
        (contDiff_const.prodMk contDiff_id))))
  exact h1.contDiffAt.comp x (Return.contDiffAt_injection hx)

lemma contDiffAt_ballChart {Z : C3} (h0 : Z 0 ≠ 0) : ContDiffAt ℝ ∞ ballChart Z := by
  set c : ℂ := ((Real.sqrt π : ℝ) : ℂ)⁻¹
  have e : ballChart = fun Y : C3 =>
      (conj (Y 0) * (((‖Y 0‖)⁻¹ : ℝ) : ℂ) * Y 1 * c,
        conj (Y 0) * (((‖Y 0‖)⁻¹ : ℝ) : ℂ) * Y 2 * c) := by
    funext Y
    simp only [ballChart, c, div_eq_mul_inv, ofReal_inv]
  have hp : ∀ j : Fin 3, ContDiff ℝ ∞ (fun Y : C3 => Y j) := fun j => contDiff_apply ℝ ℂ j
  have hconj : ContDiff ℝ ∞ (fun Y : C3 => conj (Y 0)) :=
    conjCLE.toContinuousLinearMap.contDiff.comp (hp 0)
  have hn : ContDiffAt ℝ ∞ (fun Y : C3 => (((‖Y 0‖)⁻¹ : ℝ) : ℂ)) Z :=
    ofRealCLM.contDiff.contDiffAt.comp Z
      (((hp 0).contDiffAt.norm ℝ h0).inv (norm_ne_zero_iff.mpr h0))
  have hg := hconj.contDiffAt.mul hn
  rw [e]
  exact (((hg.mul (hp 1).contDiffAt).mul contDiffAt_const)).prodMk
    ((hg.mul (hp 2).contDiffAt).mul contDiffAt_const)

lemma contDiff_c2ToE4 : ContDiff ℝ ∞ c2ToE4 := by
  have e : c2ToE4 = Return.c2CLM := by funext z; exact (Return.c2CLM_apply z).symm
  rw [e]; exact Return.c2CLM.contDiff

lemma c2ToE4_injective {z z' : ℂ × ℂ} (h : c2ToE4 z = c2ToE4 z') : z = z' := by
  have h0 := congrArg (fun X : E4 => X 0) h
  have h1 := congrArg (fun X : E4 => X 1) h
  have h2 := congrArg (fun X : E4 => X 2) h
  have h3 := congrArg (fun X : E4 => X 3) h
  simp [c2ToE4] at h0 h1 h2 h3
  exact Prod.ext (Complex.ext h0 h2) (Complex.ext h1 h3)

/-- **The ball chart is injective modulo gauge** on unit representatives off `L`. -/
lemma ballChart_inj {Z Z' : C3} (hZ : nsq Z = 1) (hZ' : nsq Z' = 1) (h0 : Z 0 ≠ 0)
    (h0' : Z' 0 ≠ 0) (h : ballChart Z = ballChart Z') :
    ∃ μ : ℂ, conj μ * μ = 1 ∧ Z = μ • Z' := by
  have hN : normSq (Z 0) = normSq (Z' 0) := by
    have e1 := Return.ballChart_norm Z hZ h0
    have e2 := Return.ballChart_norm Z' hZ' h0'
    rw [h] at e1; linarith
  have ha : ‖Z 0‖ = ‖Z' 0‖ := by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hN
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hN
  have hapos : 0 < ‖Z 0‖ := norm_pos_iff.mpr h0
  have ha' : ((‖Z 0‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hapos.ne'
  have hpi : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hc0 : conj (Z 0) * Z 0 = ((‖Z 0‖ : ℝ) : ℂ) ^ 2 := conj_mul' _
  have hc0' : conj (Z' 0) * Z' 0 = ((‖Z 0‖ : ℝ) : ℂ) ^ 2 := by rw [ha]; exact conj_mul' _
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [ballChart, ← ha] at h1 h2
  field_simp at h1 h2
  refine ⟨conj (Z' 0) * Z 0 / ((‖Z 0‖ : ℝ) : ℂ) ^ 2, ?_, ?_⟩
  · rw [map_div₀, map_mul, conj_conj, map_pow, conj_ofReal]
    field_simp
    linear_combination (conj (Z 0) * Z 0) * hc0' + ((‖Z 0‖ : ℝ) : ℂ) ^ 2 * hc0
  · ext j
    fin_cases j
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination (-1 : ℂ) * hc0'
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination (Z 0) * h1 - Z 1 * hc0
    · simp only [Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination (Z 0) * h2 - Z 2 * hc0

/-! ### The global reparametrisation `bump` -/

/-- `bump X₀ r y = X₀ + (r/√(r² + ‖y‖²)) y`: a smooth map `E4 → B(X₀, r)`, `bump 0 = X₀`,
`D bump(0) = id`. -/
def bump (X0 : E4) (r : ℝ) (y : E4) : E4 := X0 + (r / Real.sqrt (r ^ 2 + ‖y‖ ^ 2)) • y

lemma bump_zero (X0 : E4) (r : ℝ) : bump X0 r 0 = X0 := by simp [bump]

lemma contDiff_bumpCoef {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (fun y : E4 => r / Real.sqrt (r ^ 2 + ‖y‖ ^ 2)) := by
  have hq : ContDiff ℝ ∞ (fun y : E4 => r ^ 2 + ‖y‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℝ)
  have hs := hq.sqrt fun y => by positivity
  exact contDiff_const.div hs fun y => (Real.sqrt_pos.mpr (by positivity)).ne'

lemma contDiff_bump (X0 : E4) {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (bump X0 r) :=
  contDiff_const.add ((contDiff_bumpCoef hr).smul contDiff_id)

lemma bump_mem (X0 : E4) {r : ℝ} (hr : 0 < r) (y : E4) : bump X0 r y ∈ ball X0 r := by
  rw [mem_ball, dist_eq_norm, bump, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hs : 0 < Real.sqrt (r ^ 2 + ‖y‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_of_pos (div_pos hr hs), div_mul_eq_mul_div, div_lt_iff₀ hs]
  have : ‖y‖ < Real.sqrt (r ^ 2 + ‖y‖ ^ 2) :=
    (Real.lt_sqrt (norm_nonneg y)).mpr (by nlinarith)
  nlinarith

lemma hasFDerivAt_bump (X0 : E4) {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (bump X0 r) (ContinuousLinearMap.id ℝ E4) 0 := by
  have hc := ((contDiff_bumpCoef hr).differentiable (by simp) (0 : E4)).hasFDerivAt
  have h := (hc.smul (hasFDerivAt_id (0 : E4))).const_add X0
  have h1 : r / Real.sqrt (r ^ 2 + ‖(0 : E4)‖ ^ 2) = 1 := by
    simp [Real.sqrt_sq hr.le, hr.ne']
  have e : ContinuousLinearMap.id ℝ E4 = (r / Real.sqrt (r ^ 2 + ‖(0 : E4)‖ ^ 2)) •
      ContinuousLinearMap.id ℝ E4 + (fderiv ℝ (fun y : E4 => r / Real.sqrt (r ^ 2 + ‖y‖ ^ 2))
        0).smulRight (id (0 : E4)) := by
    rw [h1]; ext v; simp
  rw [e]; exact h

lemma fderiv_bump (X0 : E4) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (bump X0 r) 0 = ContinuousLinearMap.id ℝ E4 := (hasFDerivAt_bump X0 hr).fderiv

/-! ### Capacity scale -/

section cap

variable {P : Params} {Phi PhiInv : E4 → E4} (hΦ : PhiInvSpec P Phi PhiInv)
include hΦ

/-! ### Injectivity and disjointness -/

/-! ### The dilation -/

end cap

/-! ### The interface `Embed.Spec` -/

end SymplecticPacking.Embed
