import SymplecticPacking.Return.Flow
import SymplecticPacking.Return.OmegaE
import SymplecticPacking.Forms.Cartan

/-!
# The transport to `T = 1`

`sec:rtc`, the transport to `T = 1` (Proposition prop:rtc-transport, Lemma lem:rtc-denominator).

Representatives `(Z, W) ∈ ℂ³ × ℂ`, time `T`. The transport field `transportField` (Algebra.lean) has
the denominator `N_den`, which vanishes only at `T = 0` on the singular points of the cones
`F = const`; it is integrated through a *cut-off* field

  `transportVF dn w T x = χ(T, x) · (W n_⊥/(A N_den), −T W/(B N_den))`,

where `n_⊥ = n − (Z†n/‖Z‖²) Z` (equal to `n` on the unit sphere) and `χ` is an explicit smooth
cutoff (`Real.smoothTransition`) which is `1` near the compact set
`K_w = {‖Z‖ = 1, F(Z) = T W, |W|² ≤ w, T ∈ [0,1]}` (where `N_den ≥ min(3/2, T₀²/d_n)` by
`Nden_lower`) and `0` where `N_den ≤ c/2`, `‖Z‖² ∉ (1/2, 3/2)`, `|W|² ≥ w + 2` or `T ∉ (-1, 2)`.
The flow `transport dn w T = τ_T` is the definite-description flow of `Flow.lean`.

Main results (for `0 < d_n ≤ 1/3`, start points `x ∈ X₀` with `‖Z‖ = 1`, `|W|² ≤ w`; in the paper
`w = 16t₀/ε`, `injection_normW_le`):
* `transport_mem`: for `T ∈ [0,1]`, `τ_T(x) ∈ X_T`, `‖Z‖ = 1`, `|W|² ≤ w`
  (continuity/bootstrap argument with the conservation laws of
  Lemma lem:rtc-transport-field (iii) and the denominator bound);
* `transport_hasDerivAt`: on `[0,1]` the curve `T ↦ τ_T(x)` is an integral curve of the
  *uncut* `transportField` (so the cutoff is invisible);
* `transport_smooth`: joint smoothness of `τ`;
* `transport_injective`: injectivity of each `τ_T`;
* `transport_pullback`: `τ_T^* Ω_E = Ω_E` on every smooth family of points of `X₀`
  (via `Forms.pull2_d1_const` and `transport_isotropic`);
* `transport_gaugeEquiv`, `transport_equivariant` (Lemma lem:rtc-equivariant), by uniqueness.
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate Filter Topology Set Metric
open SymplecticPacking.Forms (Form1 Form2 d1 pull1 pull2 contract pull1_apply pull2_apply
  contract_apply pull2_d1_const)
open scoped Real ContDiff

/-! ### Smoothness of the ingredients -/

@[fun_prop] lemma contDiff_conj' {n : WithTop ℕ∞} : ContDiff ℝ n (fun z : ℂ => conj z) :=
  conjCLE.contDiff

attribute [local fun_prop] contDiff_normSq' contDiff_nsq

lemma contDiff_Fpoly {n : WithTop ℕ∞} : ContDiff ℝ n Fpoly := by unfold Fpoly; fun_prop

lemma contDiff_nvec {n : WithTop ℕ∞} : ContDiff ℝ n nvec := by
  rw [contDiff_pi]; intro j; unfold nvec Fpoly; fun_prop

lemma contDiff_Gfun {n : WithTop ℕ∞} : ContDiff ℝ n Gfun := contDiff_nsq.comp contDiff_nvec

lemma contDiff_herm {n : WithTop ℕ∞} : ContDiff ℝ n (fun p : C3 × C3 => herm p.1 p.2) := by
  unfold herm; simp only [Fin.sum_univ_three]; fun_prop

lemma contDiff_Acoef (dn : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (fun W : ℂ => Acoef dn W) := by
  unfold Acoef pW
  fun_prop (disch := exact fun W => (one_add_normSq_pos W).ne')

lemma contDiff_Bcoef (dn : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (fun W : ℂ => Bcoef dn W) := by
  unfold Bcoef
  fun_prop (disch := exact fun W => (pow_pos (one_add_normSq_pos W) 2).ne')

/-- `N_den` is smooth in `(T, Z, W)` (for `0 < d_n ≤ 1/3`, `A, B > 0`). -/
lemma contDiff_Nden {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ × (C3 × ℂ) => Nden dn p.2.1 p.2.2 p.1) := by
  unfold Nden
  have hA := contDiff_Acoef dn (n := n)
  have hB := contDiff_Bcoef dn (n := n)
  have hG := contDiff_Gfun (n := n)
  exact (hG.comp (contDiff_fst.comp contDiff_snd)).div (hA.comp (contDiff_snd.comp contDiff_snd))
    (fun p => (Acoef_pos hdn hdn3 _).ne') |>.add
    ((contDiff_fst.pow 2).div (hB.comp (contDiff_snd.comp contDiff_snd))
    (fun p => (Bcoef_pos hdn _).ne'))

lemma contDiffAt_nperp {Z : C3} (hZ : nsq Z ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n nperp Z := by
  unfold nperp
  have h1 : ContDiff ℝ n (fun Z : C3 => herm Z (nvec Z)) :=
    contDiff_herm.comp (contDiff_id.prodMk contDiff_nvec)
  have h2 : ContDiffAt ℝ n (fun Z : C3 => (((1 / nsq Z : ℝ)) : ℂ)) Z :=
    ofRealCLM.contDiff.contDiffAt.comp Z (contDiffAt_const.div contDiff_nsq.contDiffAt hZ)
  have h3 : ContDiffAt ℝ n (fun Z : C3 => herm Z (nvec Z) / (nsq Z : ℂ)) Z := by
    have : (fun Z : C3 => herm Z (nvec Z) / (nsq Z : ℂ)) =
        fun Z : C3 => herm Z (nvec Z) * (((1 / nsq Z : ℝ)) : ℂ) := by
      funext Z; push_cast; ring
    rw [this]; exact h1.contDiffAt.mul h2
  exact contDiff_nvec.contDiffAt.sub (h3.smul contDiffAt_id)

/-! ### The cut-off transport field -/

/-- The lower bound `c_w = min(3/2, T₀(√w)²/d_n)` for `N_den` on `K_w` (`Nden_lower`). -/
def cTr (dn w : ℝ) : ℝ := min (3 / 2) (T0fun (Real.sqrt w) ^ 2 / dn)

lemma T0fun_pos (Wmax : ℝ) : 0 < T0fun Wmax := by
  unfold T0fun
  have : 0 < Real.sqrt 6 * max 1 Wmax :=
    mul_pos (Real.sqrt_pos.mpr (by norm_num)) (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact lt_min one_pos (by positivity)

lemma cTr_pos {dn : ℝ} (hdn : 0 < dn) (w : ℝ) : 0 < cTr dn w :=
  lt_min (by norm_num) (div_pos (pow_pos (T0fun_pos _) 2) hdn)

/-- The cutoff `χ(T, Z, W)`. -/
def chiTr (dn w T : ℝ) (x : C3 × ℂ) : ℝ :=
  step (cTr dn w / 2) (3 * cTr dn w / 4) (Nden dn x.1 x.2 T) *
    plateau (1 / 2) (3 / 4) (5 / 4) (3 / 2) (nsq x.1) *
    step 0 1 (w + 2 - normSq x.2) *
    plateau (-1) (-1 / 2) (3 / 2) 2 T

/-- The uncut field with `n` replaced by `n_⊥`. -/
def transportBase (dn T : ℝ) (x : C3 × ℂ) : C3 × ℂ :=
  ((x.2 / ((Acoef dn x.2 * Nden dn x.1 x.2 T : ℝ) : ℂ)) • nperp x.1,
   ((-T / (Bcoef dn x.2 * Nden dn x.1 x.2 T) : ℝ) : ℂ) * x.2)

/-- The cut-off transport field. -/
def transportVF (dn w T : ℝ) (x : C3 × ℂ) : C3 × ℂ := chiTr dn w T x • transportBase dn T x

/-- **The transport** `τ_T` (flow of `transportVF` from `T = 0`). -/
def transport (dn w T : ℝ) (x : C3 × ℂ) : C3 × ℂ := flow (transportVF dn w) T x

/-- Its inverse, the backward flow from `T` to `0`. -/
def transportInv (dn w T : ℝ) (y : C3 × ℂ) : C3 × ℂ := flowInv (transportVF dn w) T y

lemma transportBase_unit (dn T : ℝ) {x : C3 × ℂ} (hZ : nsq x.1 = 1) :
    transportBase dn T x = transportField dn x.1 x.2 T := by
  simp only [transportBase, transportField, nperp_unit hZ]

lemma chiTr_eq_one {dn w T : ℝ} (hdn : 0 < dn) {x : C3 × ℂ} (hN : 3 * cTr dn w / 4 ≤ Nden dn x.1 x.2 T)
    (hZ : nsq x.1 = 1) (hW : normSq x.2 ≤ w + 1) (hT1 : -1 / 2 ≤ T) (hT2 : T ≤ 3 / 2) :
    chiTr dn w T x = 1 := by
  have hc := cTr_pos hdn w
  unfold chiTr
  rw [step_eq_one (by linarith) hN, plateau_eq_one (by norm_num) (by norm_num) (by rw [hZ]; norm_num)
    (by rw [hZ]; norm_num), step_eq_one (by norm_num) (by linarith),
    plateau_eq_one (by norm_num) (by norm_num) hT1 hT2]
  norm_num

/-- `transportVF = transportField` near `K_w`. -/
lemma transportVF_eq {dn w T : ℝ} (hdn : 0 < dn) {x : C3 × ℂ}
    (hN : 3 * cTr dn w / 4 ≤ Nden dn x.1 x.2 T) (hZ : nsq x.1 = 1) (hW : normSq x.2 ≤ w + 1)
    (hT1 : -1 / 2 ≤ T) (hT2 : T ≤ 3 / 2) : transportVF dn w T x = transportField dn x.1 x.2 T := by
  rw [transportVF, chiTr_eq_one hdn hN hZ hW hT1 hT2, one_smul, transportBase_unit dn T hZ]

/-- The denominator bound on `K_w`. -/
lemma Nden_ge_cTr {dn w T : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {x : C3 × ℂ}
    (hZ : nsq x.1 = 1) (hc : Fpoly x.1 = T * x.2) (hT : 0 ≤ T) (hW : normSq x.2 ≤ w) :
    cTr dn w ≤ Nden dn x.1 x.2 T := by
  apply Nden_lower hdn hdn3 hZ hc hT
  rw [← Real.sqrt_sq (norm_nonneg x.2), ← normSq_eq_norm_sq]
  exact Real.sqrt_le_sqrt hW

/-- On `K_w`: `transportVF = transportField`. -/
lemma transportVF_eq_of_mem {dn w T : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {x : C3 × ℂ}
    (hZ : nsq x.1 = 1) (hc : Fpoly x.1 = T * x.2) (hW : normSq x.2 ≤ w) (hT : T ∈ Icc 0 1) :
    transportVF dn w T x = transportField dn x.1 x.2 T := by
  have h1 := Nden_ge_cTr hdn hdn3 hZ hc hT.1 hW
  have h2 := cTr_pos hdn w
  exact transportVF_eq hdn (by linarith) hZ (by linarith) (by linarith [hT.1]) (by linarith [hT.2])

/-! #### The cut-off field is smooth and compactly supported -/

lemma transportVF_smooth {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => transportVF dn w p.1 p.2) := by
  have hc := cTr_pos hdn w
  have hN := contDiff_Nden hdn hdn3 (n := ∞)
  have hnsq : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => nsq p.2.1) :=
    contDiff_nsq.comp (contDiff_fst.comp contDiff_snd)
  have hχ : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => chiTr dn w p.1 p.2) := by
    unfold chiTr
    have hW : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => normSq p.2.2) :=
      contDiff_normSq'.comp (contDiff_snd.comp contDiff_snd)
    exact ((((step_contDiff _ _).comp hN).mul ((plateau_contDiff _ _ _ _).comp hnsq)).mul
      ((step_contDiff _ _).comp (contDiff_const.sub hW))).mul
      ((plateau_contDiff _ _ _ _).comp contDiff_fst)
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h1 : nsq p.2.1 < 1 / 2
  · apply contDiffAt_of_eventually_zero
    filter_upwards [hnsq.continuous.continuousAt.eventually_lt continuousAt_const h1] with q hq
    simp only [transportVF, chiTr, Pi.zero_apply]
    rw [plateau_eq_zero_left (by norm_num : (1 / 2 : ℝ) < 3 / 4) hq.le]
    simp
  by_cases h2 : Nden dn p.2.1 p.2.2 p.1 < cTr dn w / 2
  · apply contDiffAt_of_eventually_zero
    filter_upwards [hN.continuous.continuousAt.eventually_lt continuousAt_const h2] with q hq
    simp only [transportVF, chiTr, Pi.zero_apply]
    rw [step_eq_zero (by linarith : cTr dn w / 2 < 3 * cTr dn w / 4) hq.le]
    simp
  push Not at h1 h2
  have hZ : nsq p.2.1 ≠ 0 := by linarith
  have hNp : Nden dn p.2.1 p.2.2 p.1 ≠ 0 := by linarith
  have hA : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => Acoef dn p.2.2) :=
    (contDiff_Acoef dn).comp (contDiff_snd.comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => Bcoef dn p.2.2) :=
    (contDiff_Bcoef dn).comp (contDiff_snd.comp contDiff_snd)
  have hW2 : ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => p.2.2) := contDiff_snd.comp contDiff_snd
  have hAN0 : Acoef dn p.2.2 * Nden dn p.2.1 p.2.2 p.1 ≠ 0 :=
    mul_ne_zero (Acoef_pos hdn hdn3 _).ne' hNp
  have hAN : ContDiffAt ℝ ∞ (fun q : ℝ × (C3 × ℂ) =>
      ((1 / (Acoef dn q.2.2 * Nden dn q.2.1 q.2.2 q.1) : ℝ) : ℂ)) p :=
    ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_const.div (hA.mul hN).contDiffAt hAN0)
  have hb1 : ContDiffAt ℝ ∞ (fun q : ℝ × (C3 × ℂ) => (q.2.2 / ((Acoef dn q.2.2 *
      Nden dn q.2.1 q.2.2 q.1 : ℝ) : ℂ)) • nperp q.2.1) p := by
    have : (fun q : ℝ × (C3 × ℂ) => (q.2.2 / ((Acoef dn q.2.2 *
        Nden dn q.2.1 q.2.2 q.1 : ℝ) : ℂ))) = fun q : ℝ × (C3 × ℂ) =>
        q.2.2 * ((1 / (Acoef dn q.2.2 * Nden dn q.2.1 q.2.2 q.1) : ℝ) : ℂ) := by
      funext q; push_cast; ring
    have hs : ContDiffAt ℝ ∞ (fun q : ℝ × (C3 × ℂ) => (q.2.2 / ((Acoef dn q.2.2 *
        Nden dn q.2.1 q.2.2 q.1 : ℝ) : ℂ))) p := by
      rw [this]; exact hW2.contDiffAt.mul hAN
    exact hs.smul ((contDiffAt_nperp hZ).comp p (contDiff_fst.comp contDiff_snd).contDiffAt)
  have hBN0 : Bcoef dn p.2.2 * Nden dn p.2.1 p.2.2 p.1 ≠ 0 :=
    mul_ne_zero (Bcoef_pos hdn _).ne' hNp
  have hb2 : ContDiffAt ℝ ∞ (fun q : ℝ × (C3 × ℂ) => (((-q.1 / (Bcoef dn q.2.2 *
      Nden dn q.2.1 q.2.2 q.1) : ℝ) : ℂ) * q.2.2)) p := by
    have : ContDiffAt ℝ ∞ (fun q : ℝ × (C3 × ℂ) => (-q.1 / (Bcoef dn q.2.2 *
        Nden dn q.2.1 q.2.2 q.1) : ℝ)) p :=
      (contDiff_fst.neg.contDiffAt).div (hB.mul hN).contDiffAt hBN0
    exact (ofRealCLM.contDiff.contDiffAt.comp p this).mul hW2.contDiffAt
  exact hχ.contDiffAt.smul (hb1.prodMk hb2)

lemma chiTr_hasCompactSupport (dn w : ℝ) :
    HasCompactSupport (fun p : ℝ × (C3 × ℂ) => chiTr dn w p.1 p.2) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × (C3 × ℂ)) (|w| + 4))
  intro p hp
  by_contra hne
  apply hp
  rw [mem_closedBall_zero_iff]
  unfold chiTr at hne
  have hT := plateau_ne_zero (by norm_num) (by norm_num) (right_ne_zero_of_mul hne)
  have h3 : step 0 1 (w + 2 - normSq p.2.2) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hZ := plateau_ne_zero (by norm_num) (by norm_num)
    (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne)))
  have hW : normSq p.2.2 < w + 2 := by
    by_contra h; exact h3 (step_eq_zero one_pos (by linarith))
  have hw := le_abs_self w
  have hw0 := abs_nonneg w
  have hR : 0 ≤ |w| + 4 := by positivity
  rw [norm_prod_le_iff, norm_prod_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hT.1, hT.2]
  · rw [pi_norm_le_iff_of_nonneg hR]
    intro j
    have h1 := normSq_le_nsq p.2.1 j
    rw [normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (p.2.1 j)]
  · have h1 := normSq_eq_norm_sq p.2.2
    nlinarith [norm_nonneg p.2.2]

theorem transportVF_csField {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w : ℝ) :
    CSField (transportVF dn w) where
  smooth := transportVF_smooth hdn hdn3 w
  compact := (chiTr_hasCompactSupport dn w).smul_right
    (f' := fun p : ℝ × (C3 × ℂ) => transportBase dn p.1 p.2)

/-! #### `‖Z‖²` is a first integral -/

lemma hasFDerivAt_nsq_fst (x : C3 × ℂ) :
    HasFDerivAt (fun y : C3 × ℂ => nsq y.1) (fderiv ℝ (fun y : C3 × ℂ => nsq y.1) x) x :=
  (((contDiff_nsq (n := 1)).comp contDiff_fst).differentiable one_ne_zero x).hasFDerivAt

lemma fderiv_nsq_fst (x v : C3 × ℂ) :
    fderiv ℝ (fun y : C3 × ℂ => nsq y.1) x v = 2 * (herm x.1 v.1).re := by
  apply fderiv_apply_of_line (((contDiff_nsq (n := 1)).comp contDiff_fst).differentiable
    one_ne_zero x)
  have h := hasDerivAt_quad (nsq x.1) (herm x.1 v.1).re (nsq v.1)
  convert h using 1
  funext t
  show nsq (x.1 + t • v.1) = _
  rw [nsq_add_smul]

lemma herm_rsmul (a v : C3) (r : ℝ) : herm a (r • v) = r * herm a v := by
  simp only [herm, Fin.sum_univ_three, Pi.smul_apply, real_smul]; ring

lemma herm_transportVF (dn w T : ℝ) (x : C3 × ℂ) : herm x.1 (transportVF dn w T x).1 = 0 := by
  by_cases hZ : nsq x.1 = 0
  · have : chiTr dn w T x = 0 := by
      unfold chiTr
      rw [plateau_eq_zero_left (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by rw [hZ]; norm_num)]
      simp
    rw [transportVF, this, zero_smul]
    simp [herm]
  · rw [transportVF, Prod.smul_fst, herm_rsmul, transportBase, herm_smul_right, herm_nperp hZ,
      mul_zero, mul_zero]

theorem nsq_transport {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w T : ℝ) (x : C3 × ℂ) :
    nsq (transport dn w T x).1 = nsq x.1 :=
  (transportVF_csField hdn hdn3 w).flow_firstIntegral (Q := fun y : C3 × ℂ => nsq y.1)
    hasFDerivAt_nsq_fst (fun t y => by rw [fderiv_nsq_fst, herm_transportVF]; simp) T x

/-! ### Global existence on `[0,1]` and invariance of `X_T` -/

/-- Derivative of `|W|²` along a curve. -/
lemma hasDerivAt_normSq_comp {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => normSq (f s)) (2 * (conj (f t) * f').re) t := by
  have hre := (reCLM.hasFDerivAt (x := f t)).comp_hasDerivAt t hf
  have him := (imCLM.hasFDerivAt (x := f t)).comp_hasDerivAt t hf
  have h := (hre.mul hre).add (him.mul him)
  convert h using 1
  · funext s; simp [normSq_apply, Function.comp]
  · simp only [Function.comp, reCLM_apply, imCLM_apply, mul_re, conj_re, conj_im]; ring

/-- **Invariance of `X_T`** (Proposition prop:rtc-transport, first part): for a start point
`x ∈ X₀` with `‖Z‖ = 1`, `|W|² ≤ w`, and `T ∈ [0,1]`, `τ_T(x)` satisfies `‖Z‖ = 1`,
`F(Z) = T W` and `|W|² ≤ w`. -/
theorem transport_mem {dn w : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {x : C3 × ℂ}
    (hZ : nsq x.1 = 1) (hF : Fpoly x.1 = 0) (hW : normSq x.2 ≤ w) {T : ℝ} (hT : T ∈ Icc 0 1) :
    nsq (transport dn w T x).1 = 1 ∧ Fpoly (transport dn w T x).1 = T * (transport dn w T x).2 ∧
      normSq (transport dn w T x).2 ≤ w := by
  have hV := transportVF_csField hdn hdn3 w
  set u : ℝ → C3 × ℂ := fun t => transport dn w t x with hu
  have hnsq : ∀ t, nsq (u t).1 = 1 := fun t => (nsq_transport hdn hdn3 w t x).trans hZ
  have hcont : Continuous u := hV.flowFrom_continuous 0 x
  have hder : ∀ t, HasDerivAt u (transportVF dn w t (u t)) t := fun t => hV.flow_hasDerivAt x t
  have hc := cTr_pos hdn w
  set S : Set ℝ := {t | Fpoly (u t).1 = t * (u t).2 ∧ normSq (u t).2 ≤ w} with hS
  have hSc : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq ((contDiff_Fpoly (n := 0)).continuous.comp (continuous_fst.comp hcont))
        ((continuous_ofReal.mul (continuous_snd.comp hcont)))
    · exact isClosed_le ((contDiff_normSq' (n := 0)).continuous.comp
        (continuous_snd.comp hcont)) continuous_const
  have hsub : Icc (0 : ℝ) 1 ⊆ S := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hSc.inter isClosed_Icc)
    · refine ⟨?_, ?_⟩
      · simp [hu, transport, hV.flow_zero x, hF]
      · simp only [hu, transport, hV.flow_zero x]; exact hW
    · rintro t₀ ⟨⟨hC0, hW0⟩, ht₀⟩
      -- the good open set where the field is the uncut one
      set G : Set (ℝ × (C3 × ℂ)) := {p | 3 * cTr dn w / 4 < Nden dn p.2.1 p.2.2 p.1 ∧
        normSq p.2.2 < w + 1 ∧ -1 / 2 < p.1 ∧ p.1 < 3 / 2} with hG
      have hGo : IsOpen G := by
        have hN := (contDiff_Nden hdn hdn3 (n := 0)).continuous
        refine (isOpen_lt continuous_const hN).inter ((isOpen_lt
          ((contDiff_normSq' (n := 0)).continuous.comp (continuous_snd.comp continuous_snd))
          continuous_const).inter ((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)))
      have hN0 := Nden_ge_cTr hdn hdn3 (hnsq t₀) hC0 ht₀.1 hW0
      have hp0 : (t₀, u t₀) ∈ G := ⟨by linarith, by linarith, by linarith [ht₀.1],
        by linarith [ht₀.2]⟩
      have hev : ∀ᶠ s in 𝓝 t₀, (s, u s) ∈ G :=
        (continuous_id.prodMk hcont).continuousAt.preimage_mem_nhds (hGo.mem_nhds hp0)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
      have hGs : ∀ s ∈ Icc t₀ (t₀ + ε / 2), (s, u s) ∈ G := fun s hs =>
        hball (by rw [Real.ball_eq_Ioo]; constructor <;> linarith [hs.1, hs.2])
      have hVs : ∀ s ∈ Icc t₀ (t₀ + ε / 2),
          transportVF dn w s (u s) = transportField dn (u s).1 (u s).2 s := fun s hs =>
        transportVF_eq hdn (hGs s hs).1.le (hnsq s) (hGs s hs).2.1.le (hGs s hs).2.2.1.le
          (hGs s hs).2.2.2.le
      -- the constraint is constant
      have hCst : ∀ s ∈ Icc t₀ (t₀ + ε / 2), Fpoly (u s).1 - s * (u s).2 =
          Fpoly (u t₀).1 - t₀ * (u t₀).2 := by
        apply constant_of_has_deriv_right_zero
        · exact (((contDiff_Fpoly (n := 0)).continuous.comp (continuous_fst.comp hcont)).sub
            (continuous_ofReal.mul (continuous_snd.comp hcont))).continuousOn
        · intro s hs
          have hs' : s ∈ Icc t₀ (t₀ + ε / 2) := ⟨hs.1, hs.2.le⟩
          have hd := hder s
          rw [hVs s hs'] at hd
          have h1 : HasDerivAt (fun r => Fpoly (u r).1)
              (fderiv ℝ Fpoly (u s).1 (transportField dn (u s).1 (u s).2 s).1) s :=
            (((contDiff_Fpoly (n := 1)).differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt s
              ((ContinuousLinearMap.fst ℝ C3 ℂ).hasFDerivAt.comp_hasDerivAt s hd)
          have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * (u r).2)
              (1 * (u s).2 + (s : ℂ) * (transportField dn (u s).1 (u s).2 s).2) s :=
            (hasDerivAt_id (s : ℝ)).ofReal_comp.mul
              ((ContinuousLinearMap.snd ℝ C3 ℂ).hasFDerivAt.comp_hasDerivAt s hd)
          have h3 := h1.sub h2
          rw [fderiv_Fpoly] at h3
          have hNs : Nden dn (u s).1 (u s).2 s ≠ 0 := by
            have := (hGs s hs').1; linarith
          have h0 := transport_constraint dn (u s).1 (u s).2 s (hnsq s)
            (Acoef_pos hdn hdn3 _).ne' (Bcoef_pos hdn _).ne' hNs
          refine (h3.congr_deriv ?_).hasDerivWithinAt
          linear_combination h0
      -- `|W|²` does not increase
      have hWm : AntitoneOn (fun s => normSq (u s).2) (Icc t₀ (t₀ + ε / 2)) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          ((contDiff_normSq' (n := 0)).continuous.comp (continuous_snd.comp hcont)).continuousOn
          (f' := fun s => 2 * (conj (u s).2 * (transportVF dn w s (u s)).2).re)
        · intro s _
          exact (hasDerivAt_normSq_comp
            ((ContinuousLinearMap.snd ℝ C3 ℂ).hasFDerivAt.comp_hasDerivAt s (hder s))).hasDerivWithinAt
        · intro s hs
          rw [interior_Icc] at hs
          have hs' : s ∈ Icc t₀ (t₀ + ε / 2) := ⟨hs.1.le, hs.2.le⟩
          rw [hVs s hs', transport_normW]
          have hNs : 0 < Nden dn (u s).1 (u s).2 s := by
            have := (hGs s hs').1; linarith
          have hB := Bcoef_pos hdn (u s).2
          have hs0 : 0 ≤ s := by linarith [ht₀.1, hs.1]
          have := normSq_nonneg (u s).2
          apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos hB hNs).le
          nlinarith
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      refine ⟨t₀ + ε / 2, by simp; linarith, fun s hs => ?_⟩
      have hs' : s ∈ Icc t₀ (t₀ + ε / 2) := ⟨hs.1.le, hs.2.le⟩
      refine ⟨?_, ?_⟩
      · have := hCst s hs'
        rw [hC0, sub_self] at this
        exact sub_eq_zero.mp this
      · exact (hWm (left_mem_Icc.mpr (by linarith)) hs' hs.1.le).trans hW0
  exact ⟨hnsq T, (hsub hT).1, (hsub hT).2⟩

/-- On `[0,1]`, `T ↦ τ_T(x)` is an integral curve of the uncut `transportField`. -/
theorem transport_hasDerivAt {dn w : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {x : C3 × ℂ}
    (hZ : nsq x.1 = 1) (hF : Fpoly x.1 = 0) (hW : normSq x.2 ≤ w) {T : ℝ} (hT : T ∈ Icc 0 1) :
    HasDerivAt (fun s => transport dn w s x)
      (transportField dn (transport dn w T x).1 (transport dn w T x).2 T) T := by
  obtain ⟨h1, h2, h3⟩ := transport_mem hdn hdn3 hZ hF hW hT
  rw [← transportVF_eq_of_mem hdn hdn3 h1 h2 h3 hT]
  exact (transportVF_csField hdn hdn3 w).flow_hasDerivAt x T

@[simp] theorem transport_zero {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w : ℝ)
    (x : C3 × ℂ) : transport dn w 0 x = x := (transportVF_csField hdn hdn3 w).flow_zero x

/-! ### Smoothness and injectivity -/

theorem transport_smooth {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (C3 × ℂ) => transport dn w p.1 p.2) :=
  (transportVF_csField hdn hdn3 w).flow_smooth

/-- **Injectivity of `τ_T`** (in fact on all of `ℂ³ × ℂ`; the backward flow is a left inverse). -/
theorem transport_injective {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w T : ℝ) :
    Function.Injective (transport dn w T) :=
  (transportVF_csField hdn hdn3 w).flow_injective T

/-! ### `τ_T^* Ω_E = Ω_E` -/

lemma contDiffOn_lamE (dn : ℝ) :
    ContDiffOn ℝ ∞ (lamE dn) {y : C3 × ℂ | y.1 ≠ 0} := fun y hy =>
  (contDiffAt_dc (n := ∞) (contDiffAt_PhiE dn (nsq_pos hy))).contDiffWithinAt

lemma isOpen_fst_ne_zero : IsOpen {y : C3 × ℂ | y.1 ≠ 0} :=
  isOpen_ne_fun continuous_fst continuous_const

lemma ne_zero_of_nsq_eq_one {Z : C3} (h : nsq Z = 1) : Z ≠ 0 := by
  rintro rfl; simp [nsq] at h

/-- Tangency: if `F(Z) = T W` along a differentiable family, its derivative satisfies
`dF_Z(Ż) = T Ẇ`. -/
lemma tangent_of_constraint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → C3 × ℂ} {x : E} (hg : DifferentiableAt ℝ g x) {T : ℝ}
    (hc : ∀ y, Fpoly (g y).1 = T * (g y).2) (ξ : E) :
    dF (g x).1 (fderiv ℝ g x ξ).1 = T * (fderiv ℝ g x ξ).2 := by
  have h1 := (((contDiff_Fpoly (n := 1)).differentiable one_ne_zero (g x).1).hasFDerivAt).comp x
    hg.hasFDerivAt.fst
  have h2 := hg.hasFDerivAt.snd.const_mul (T : ℂ)
  have h3 := h1.sub h2
  have hz : ((Fpoly ∘ fun x => (g x).1) - fun y => (T : ℂ) * (g y).2) = fun _ => 0 :=
    funext fun y => sub_eq_zero.mpr (hc y)
  rw [hz] at h3
  have h4 := congrArg (fun L => L ξ) (h3.unique (hasFDerivAt_const 0 x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.zero_apply, smul_eq_mul, fderiv_Fpoly] at h4
  exact sub_eq_zero.mp h4

/-- **`τ_T^*(Ω_E|_{X_T}) = Ω_E|_{X₀}`** (Proposition prop:rtc-transport, symplectic part),
for every smooth family `φ₀ : E → ℂ³ × ℂ` of points of `X₀` with `‖Z‖ = 1`, `|W|² ≤ w`. -/
theorem transport_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {dn w : ℝ}
    (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {φ₀ : E → C3 × ℂ} (hφ : ContDiff ℝ ∞ φ₀)
    (hZ : ∀ x, nsq (φ₀ x).1 = 1) (hF : ∀ x, Fpoly (φ₀ x).1 = 0) (hW : ∀ x, normSq (φ₀ x).2 ≤ w)
    {T : ℝ} (hT : T ∈ Icc 0 1) :
    pull2 (fun x => transport dn w T (φ₀ x)) (OmegaE dn) = pull2 φ₀ (OmegaE dn) := by
  have hV := transportVF_csField hdn hdn3 w
  have hmem : ∀ t, sigT T t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨(sigT_mem hT.1 t).1, (sigT_mem hT.1 t).2.trans hT.2⟩
  have key := pull2_d1_const (lam := lamE dn) (U := {y : C3 × ℂ | y.1 ≠ 0})
    (φ := fun t x => transport dn w (sigT T t) (φ₀ x))
    (V := fun t y => deriv (sigT T) t • transportVF dn w (sigT T t) y)
    isOpen_fst_ne_zero (contDiffOn_lamE dn) (hV.family_smooth T hφ)
    (fun t x => ne_zero_of_nsq_eq_one (transport_mem hdn hdn3 (hZ x) (hF x) (hW x)
      (hmem t)).1)
    (fun t x => hV.family_hasDerivAt T φ₀ t x) ?_ 1
  · simp only [sigT_one, sigT_zero, transport_zero hdn hdn3] at key
    exact key
  · intro t
    funext x
    ext ξ
    obtain ⟨h1, h2, h3⟩ := transport_mem hdn hdn3 (hZ x) (hF x) (hW x) (hmem t)
    simp only [pull1_apply, contract_apply, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply, Pi.zero_apply]
    rw [transportVF_eq_of_mem hdn hdn3 h1 h2 h3 (hmem t)]
    have hd : DifferentiableAt ℝ (fun x => transport dn w (sigT T t) (φ₀ x)) x :=
      (((transport_smooth hdn hdn3 w).comp (contDiff_const.prodMk hφ)).differentiable
        (by simp)) x
    have htan := tangent_of_constraint hd (T := sigT T t)
      (fun y => (transport_mem hdn hdn3 (hZ y) (hF y) (hW y) (hmem t)).2.1) ξ
    have := transport_isotropic' hdn hdn3 h1 h2 (hmem t).1 _ htan
    rw [← OmegaE, this, mul_zero]

/-! ### Equivariance (Lemma lem:rtc-equivariant) -/

/-- The gauge action `(Z, W) ↦ (cZ, c³W)` as a real-linear map. -/
def gaugeLM (c : ℂ) : (C3 × ℂ) →ₗ[ℝ] (C3 × ℂ) where
  toFun x := (c • x.1, c ^ 3 * x.2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

/-- The cube-root action `(Z, W) ↦ (gZ, W)` as a real-linear map. -/
def cubeRootLM : (C3 × ℂ) →ₗ[ℝ] (C3 × ℂ) where
  toFun x := (cubeRoot x.1, x.2)
  map_add' x y := by ext j <;> [fin_cases j <;> simp <;> ring; simp]
  map_smul' r x := by ext j <;> [fin_cases j <;> simp <;> ring; simp]

lemma chiTr_gauge (dn w T : ℝ) (x : C3 × ℂ) {c : ℂ} (hc : conj c * c = 1) :
    chiTr dn w T (c • x.1, c ^ 3 * x.2) = chiTr dn w T x := by
  simp only [chiTr, Nden_gauge dn x.1 x.2 T hc, nsq_smul_of_unit x.1 hc,
    normSq_mul_of_unit (unit_pow hc 3)]

lemma transportVF_gauge (dn w T : ℝ) (x : C3 × ℂ) {c : ℂ} (hc : conj c * c = 1) :
    transportVF dn w T (gaugeLM c x) = gaugeLM c (transportVF dn w T x) := by
  change transportVF dn w T (c • x.1, c ^ 3 * x.2) =
    (c • (transportVF dn w T x).1, c ^ 3 * (transportVF dn w T x).2)
  simp only [transportVF, chiTr_gauge dn w T x hc, transportBase, Nden_gauge dn x.1 x.2 T hc,
    Acoef_smul dn x.2 (unit_pow hc 3), Bcoef_smul dn x.2 (unit_pow hc 3), nperp_smul x.1 hc,
    Prod.smul_mk, smul_smul]
  ext j
  · simp only [Pi.smul_apply, smul_eq_mul, real_smul]
    linear_combination ((chiTr dn w T x : ℂ) * c * x.2 / ((Acoef dn x.2 *
      Nden dn x.1 x.2 T : ℝ) : ℂ) * nperp x.1 j * (conj c * c + 1)) * hc
  · simp only [real_smul]; ring

lemma transportVF_cubeRoot (dn w T : ℝ) (x : C3 × ℂ) :
    transportVF dn w T (cubeRootLM x) = cubeRootLM (transportVF dn w T x) := by
  change transportVF dn w T (cubeRoot x.1, x.2) =
    (cubeRoot (transportVF dn w T x).1, (transportVF dn w T x).2)
  simp only [transportVF, chiTr, transportBase, Nden, Gfun_cubeRoot, nsq_cubeRoot,
    nperp_cubeRoot, Prod.smul_mk]
  ext j
  · fin_cases j <;> simp [cubeRoot] <;> ring
  · rfl

lemma gaugeLM_apply (c : ℂ) (x : C3 × ℂ) :
    (LinearMap.toContinuousLinearMap (gaugeLM c)) x = (c • x.1, c ^ 3 * x.2) := rfl

lemma cubeRootLM_apply (x : C3 × ℂ) :
    (LinearMap.toContinuousLinearMap cubeRootLM) x = (cubeRoot x.1, x.2) := rfl

/-- **Gauge equivariance of the transport.** -/
theorem transport_gaugeEquiv {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w T : ℝ) (x : C3 × ℂ)
    {c : ℂ} (hc : conj c * c = 1) :
    transport dn w T (c • x.1, c ^ 3 * x.2) =
      (c • (transport dn w T x).1, c ^ 3 * (transport dn w T x).2) := by
  have := (transportVF_csField hdn hdn3 w).flow_map
    (L := LinearMap.toContinuousLinearMap (gaugeLM c))
    (fun t y => transportVF_gauge dn w t y hc) T x
  simpa only [gaugeLM_apply, transport, transportInv] using this

/-- **`g`-equivariance of the transport.** -/
theorem transport_equivariant {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (w T : ℝ)
    (x : C3 × ℂ) :
    transport dn w T (cubeRoot x.1, x.2) =
      (cubeRoot (transport dn w T x).1, (transport dn w T x).2) := by
  have := (transportVF_csField hdn hdn3 w).flow_map
    (L := LinearMap.toContinuousLinearMap cubeRootLM)
    (fun t y => transportVF_cubeRoot dn w t y) T x
  simpa only [cubeRootLM_apply, transport] using this

end SymplecticPacking.Return
