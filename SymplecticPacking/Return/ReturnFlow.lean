import SymplecticPacking.Return.Transport

/-!
# The return to the Fubini–Study form

`sec:rtc`, the return to the Fubini–Study form (Construction cons:rtc-return, Lemma lem:rtc-graph,
Lemma lem:rtc-dc-horizontal, Lemma lem:rtc-return-field, Proposition prop:rtc-return,
Lemma lem:rtc-equivariant for `ψ`).

On representatives `Z ∈ ℂ³ ∖ 0`:
* `PhiS dn s = log ‖Z‖² + s d_n log(1 + u)`, `u = |F(Z)|²/‖Z‖⁶`; `lamS dn s = d^c PhiS`,
  `omegaS dn s = d lamS = ω_FS + s d_n dd^c log(1+u)` (pulled back to `ℂ³ ∖ 0`).
* `lamS_graph`, `omegaS_graph`: `λ_s = γ^* λ_E^{(s d_n)}`, `ω_s = γ^* Ω_E^{(s d_n)}` for the graph
  map `γ(Z) = (Z, F(Z))` (so `γ^*Ω_E = ω_1`, Lemma lem:rtc-graph).
* `lamS_unit`: explicit formula at unit `Z`; `dc_log_one_add_u` (lem:rtc-dc-horizontal).
* `returnField_spec` (lem:rtc-return-field): `ι_{Y_s} ω_s = −d_n d^c log(1+u)` at unit `Z`, on *all*
  tangent vectors (the orbit directions are killed by degeneracy).
* The flow `returnFlow dn s = ψ_s` of a cut-off extension `returnVF` of `Y_s` (equal to `Y_s` on
  the unit sphere for `s ∈ [0,1]`, and proportional to `n_⊥`, so `‖Z‖` is a first integral);
  `returnFlowInv dn s = ψ_s⁻¹` the backward flow.
* `returnFlow_pullback`: `ψ_s^* ω_s = ω_FS` on smooth families of unit vectors (via
  `Forms.pull2_d1_const_of_dt`), and `returnFlowInv_pullback`: `(ψ_s⁻¹)^* ω_FS = ω_s`.
* `returnFlowInv_gaugeEquiv`, `returnFlowInv_equivariant` (cube root): equivariance of `ψ_s⁻¹`.
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate Filter Topology Set Metric
open SymplecticPacking.Forms (Form1 Form2 d1 pull1 pull2 contract dtForm pull1_apply pull2_apply
  contract_apply pull2_d1_const_of_dt pull2_d1_apply)
open scoped Real ContDiff

attribute [local fun_prop] contDiff_normSq' contDiff_nsq

/-! ### The return path of forms -/

/-- `Φ_s = log ‖Z‖² + s d_n log(1 + u)`. -/
def PhiS (dn s : ℝ) (Z : C3) : ℝ := Real.log (nsq Z) + s * dn * Real.log (1 + uFun Z)

/-- `λ_s = d^c Φ_s = d^c log ‖Z‖² + s d_n d^c log(1+u)`. -/
def lamS (dn s : ℝ) : Form1 C3 := dc (PhiS dn s)

/-- `ω_s = d λ_s = ω_FS + s d_n dd^c log(1+u)`. -/
def omegaS (dn s : ℝ) : Form2 C3 := d1 (lamS dn s)

/-- The graph map `γ(Z) = (Z, F(Z))`. -/
def graph (Z : C3) : C3 × ℂ := (Z, Fpoly Z)

lemma contDiff_graph {n : WithTop ℕ∞} : ContDiff ℝ n graph := contDiff_id.prodMk contDiff_Fpoly

lemma hasFDerivAt_graph (Z : C3) :
    HasFDerivAt graph ((ContinuousLinearMap.id ℝ C3).prod (fderiv ℝ Fpoly Z)) Z :=
  (hasFDerivAt_id Z).prodMk ((contDiff_Fpoly (n := 1)).differentiable one_ne_zero Z).hasFDerivAt

lemma fderiv_graph (Z ξ : C3) : fderiv ℝ graph Z ξ = (ξ, dF Z ξ) := by
  simp only [(hasFDerivAt_graph Z).fderiv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderiv_Fpoly]

lemma PhiS_eq_graph (dn s : ℝ) : PhiS dn s = fun Z => PhiE (s * dn) (graph Z) := by
  funext Z; simp only [PhiS, PhiE, graph, uFun]; try ring

lemma contDiffAt_uFun {Z : C3} (hZ : nsq Z ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n uFun Z := by
  unfold uFun
  exact ((contDiff_normSq'.comp contDiff_Fpoly).contDiffAt).div (contDiff_nsq.contDiffAt.pow 3)
    (pow_ne_zero 3 hZ)

lemma contDiffAt_PhiS (dn s : ℝ) {Z : C3} (hZ : nsq Z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (PhiS dn s) Z := by
  unfold PhiS
  have hu := uFun_nonneg Z
  exact (contDiff_nsq.contDiffAt.log hZ).add (contDiffAt_const.mul
    ((contDiffAt_const.add (contDiffAt_uFun hZ)).log (by linarith)))

lemma contDiffOn_lamS (dn s : ℝ) : ContDiffOn ℝ ∞ (lamS dn s) {Z : C3 | Z ≠ 0} := fun Z hZ =>
  (contDiffAt_dc (n := ∞) (contDiffAt_PhiS dn s (nsq_pos hZ).ne')).contDiffWithinAt

/-- `λ_s = γ^* λ_E` with `d_n` replaced by `s d_n`. -/
theorem lamS_graph (dn s : ℝ) {Z : C3} (hZ : Z ≠ 0) :
    lamS dn s Z = pull1 graph (lamE (s * dn)) Z := by
  ext ξ
  have hP : DifferentiableAt ℝ (PhiE (s * dn)) (graph Z) :=
    differentiableAt_PhiE (s * dn) (by simpa [graph] using nsq_pos hZ)
  have hg : DifferentiableAt ℝ graph Z := (hasFDerivAt_graph Z).differentiableAt
  rw [pull1_apply, lamS, lamE, dc_apply, dc_apply, PhiS_eq_graph,
    show (fun Z => PhiE (s * dn) (graph Z)) = PhiE (s * dn) ∘ graph from rfl,
    fderiv_comp Z hP hg, ContinuousLinearMap.comp_apply, fderiv_graph, fderiv_graph]
  congr 2
  all_goals simp only [Prod.smul_mk, smul_eq_mul, dF_smul]

/-- `ω_s = γ^* Ω_E` with `d_n` replaced by `s d_n` (for `s = 1`: `γ^*Ω_E = ω_1`). -/
theorem omegaS_graph (dn s : ℝ) {Z : C3} (hZ : Z ≠ 0) :
    omegaS dn s Z = pull2 graph (OmegaE (s * dn)) Z := by
  have hev : lamS dn s =ᶠ[𝓝 Z] pull1 graph (lamE (s * dn)) := by
    filter_upwards [isOpen_ne.mem_nhds hZ] with Y hY using lamS_graph dn s hY
  have h1 : d1 (lamS dn s) Z = d1 (pull1 graph (lamE (s * dn))) Z := by
    simp only [SymplecticPacking.Forms.d1, hev.fderiv_eq]
  rw [omegaS, h1, OmegaE, pull2_d1_apply contDiff_graph.contDiffAt
    (differentiableAt_lamE (s * dn) (by simpa [graph] using nsq_pos hZ))]

/-- The `d^c log(1+u)` part, at unit `Z`:
`(Im(conj f · dF_Z ξ) − 3|f|² Im(Z†ξ))/(2π(1+|f|²))`. -/
def Dfun (Z ξ : C3) : ℝ :=
  ((conj (Fpoly Z) * dF Z ξ).im - 3 * normSq (Fpoly Z) * (herm Z ξ).im) /
    (2 * π * (1 + normSq (Fpoly Z)))

/-- `λ_s = η_H + s d_n · Dfun` at a unit representative. -/
theorem lamS_unit (dn s : ℝ) {Z : C3} (hZ : nsq Z = 1) (ξ : C3) :
    lamS dn s Z ξ = etaH Z ξ + s * dn * Dfun Z ξ := by
  rw [lamS_graph dn s (ne_zero_of_nsq_eq_one hZ), pull1_apply, fderiv_graph, graph,
    dc_log_one_add (s * dn) hZ, Dfun]
  try ring

/-- `λ_s` is affine in `s` (as covectors, at every `Z ≠ 0`). -/
theorem lamS_affine (dn s : ℝ) {Z : C3} (hZ : Z ≠ 0) :
    lamS dn s Z = lamS dn 0 Z + s • (lamS dn 1 Z - lamS dn 0 Z) := by
  have hz := (nsq_pos hZ).ne'
  have h0 := (contDiffAt_PhiS dn 0 hz (n := 1)).differentiableAt one_ne_zero
  have h1 := (contDiffAt_PhiS dn 1 hz (n := 1)).differentiableAt one_ne_zero
  have he : PhiS dn s = fun Y => PhiS dn 0 Y + s * (PhiS dn 1 Y - PhiS dn 0 Y) := by
    funext Y; simp only [PhiS]; ring
  have hd : HasFDerivAt (fun Y => PhiS dn 0 Y + s * (PhiS dn 1 Y - PhiS dn 0 Y))
      (fderiv ℝ (PhiS dn 0) Z + s • (fderiv ℝ (PhiS dn 1) Z - fderiv ℝ (PhiS dn 0) Z)) Z :=
    h0.hasFDerivAt.add ((h1.hasFDerivAt.sub h0.hasFDerivAt).const_mul s)
  ext ξ
  simp only [lamS, dc_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  ring

/-- `λ_1 − λ_0 = d_n d^c log(1+u)` equals `d_n · Dfun` at unit `Z`. -/
theorem lamS_sub_unit (dn : ℝ) {Z : C3} (hZ : nsq Z = 1) (ξ : C3) :
    lamS dn 1 Z ξ - lamS dn 0 Z ξ = dn * Dfun Z ξ := by
  rw [lamS_unit dn 1 hZ, lamS_unit dn 0 hZ]; ring

/-- **Lemma lem:rtc-dc-horizontal.** At a unit representative,
`d^c log(1+u) = Dfun`, and on `H_Z`: `d^c log(1+u)(ξ) = Im(conj f · n†ξ)/(2π(1+u))`. -/
theorem dc_log_one_add_u {Z : C3} (hZ : nsq Z = 1) (ξ : C3) :
    dc (fun Y => Real.log (1 + uFun Y)) Z ξ = Dfun Z ξ := by
  have hz : nsq Z ≠ 0 := by rw [hZ]; norm_num
  have h0 := (contDiffAt_PhiS 1 0 hz (n := 1)).differentiableAt one_ne_zero
  have h1 := (contDiffAt_PhiS 1 1 hz (n := 1)).differentiableAt one_ne_zero
  have he : (fun Y => Real.log (1 + uFun Y)) = fun Y => PhiS 1 1 Y - PhiS 1 0 Y := by
    funext Y; simp only [PhiS]; ring
  have := lamS_sub_unit 1 hZ ξ
  rw [one_mul] at this
  rw [← this, he, lamS, lamS, dc_apply, dc_apply, dc_apply, fderiv_fun_sub h1 h0,
    ContinuousLinearMap.sub_apply]
  ring

theorem Dfun_horizontal {Z : C3} (hZ : nsq Z = 1) {ξ : C3} (hξ : herm Z ξ = 0) :
    Dfun Z ξ = (conj (Fpoly Z) * herm (nvec Z) ξ).im / (2 * π * (1 + uFun Z)) := by
  rw [Dfun, n_dF Z ξ hξ, hξ, uFun, hZ]; simp

/-! ### Lemma lem:rtc-return-field: `ι_{Y_s} ω_s = −d_n d^c log(1+u)` -/

/-- **Lemma lem:rtc-return-field** (with the orbit directions): at a unit representative and for
`s ∈ [0,1]`, `ω_s(Y_s, ξ) = −d_n Dfun(ξ) = −d_n d^c log(1+u)(ξ)` for *every* `ξ ∈ ℂ³`. -/
theorem returnField_spec {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {Z : C3} (hZ : nsq Z = 1) (ξ : C3) :
    omegaS dn s Z (returnField dn s Z) ξ = -(dn * Dfun Z ξ) := by
  set f := Fpoly Z with hf
  set Y := returnField dn s Z with hY
  set c := herm Z ξ with hc
  set ξh : C3 := ξ - c • Z with hξh
  have hξh0 : herm Z ξh = 0 := by
    rw [hξh, sub_eq_add_neg, ← neg_smul, herm_add_right, herm_smul_right, herm_self_unit hZ]
    simp [c]
  have hY0 : herm Z Y = 0 := returnField_horizontal dn s Z hZ
  have hdec : (ξ, dF Z ξ) = (ξh, dF Z ξh) + c.re • orbitVec Z f + c.im • (I • orbitVec Z f) := by
    have key : (c.re : ℂ) + c.im * I = c := re_add_im c
    have hdξ : dF Z ξh = dF Z ξ - 3 * c * f := by
      rw [hξh, dF_sub, dF_smul, dF_self]; ring
    ext j
    · simp only [orbitVec, Prod.fst_add, Prod.smul_mk, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, real_smul, hξh]
      linear_combination (-(Z j)) * key
    · simp only [orbitVec, Prod.snd_add, Prod.smul_mk, smul_eq_mul, real_smul, hdξ]
      linear_combination (-(3 * f)) * key
  rw [omegaS_graph dn s (ne_zero_of_nsq_eq_one hZ), pull2_apply, fderiv_graph, fderiv_graph,
    graph, hdec, map_add, map_add, map_smul, map_smul, ← hf, OmegaE_orbit_right _ hZ,
    OmegaE_orbitI_right _ hZ, smul_zero, smul_zero, add_zero, add_zero,
    OmegaE_herm _ hZ _ _ _ hY0 hξh0]
  -- identify with the Hermitian form `M_s`
  have hM : ((Acoef (s * dn) f : ℂ) * herm Y ξh + (Bcoef (s * dn) f : ℂ) * (conj (dF Z Y) *
      dF Z ξh)) = herm (Ms dn s Z Y) ξh := by
    have hu : uFun Z = normSq f := by rw [uFun, hZ]; simp [hf]
    have hA : Acoef (s * dn) f = As dn s Z := by
      rw [Acoef, pW, As, hu]; try ring
    have hB : Bcoef (s * dn) f = Bs dn s Z := by
      rw [Bcoef, Bs, hu]; try ring
    rw [← n_dF Z Y hY0, ← n_dF Z ξh hξh0, hA, hB]
    simp only [Ms, herm, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add,
      map_mul, conj_ofReal]
    ring
  rw [hM, returnField_contract hdn hdn3 hs0 hs1 Z hZ ξh]
  have hD : Dfun Z ξ = Dfun Z ξh := by
    simp only [Dfun]
    congr 1
    have hdξ : dF Z ξ = dF Z ξh + 3 * c * f := by
      rw [hξh, dF_sub, dF_smul, dF_self]; ring
    rw [hdξ, hξh0, ← hc]
    have hff : conj f * f = (normSq f : ℂ) := (ofReal_normSq' f).symm
    have : (conj f * (dF Z ξh + 3 * c * f)).im = (conj f * dF Z ξh).im + 3 * normSq f * c.im := by
      rw [mul_add, add_im, show conj f * (3 * c * f) = ((3 * normSq f : ℝ) : ℂ) * c by
        push_cast; linear_combination (3 * c) * hff, im_ofReal_mul]
    simp only [← hf]
    rw [this]; simp
  rw [hD, Dfun_horizontal hZ hξh0]
  ring

/-! ### The cut-off return field and its flow -/

/-- The lower bound `1 − (3/2) d_n` of `A_s + B_s G` on the unit sphere, `s ∈ [0,1]`. -/
def mR (dn : ℝ) : ℝ := 1 - 3 / 2 * dn

lemma mR_pos {dn : ℝ} (hdn3 : dn ≤ 1 / 3) : 0 < mR dn := by unfold mR; linarith

/-- The denominator `A_s + B_s G`. -/
def returnDen (dn s : ℝ) (Z : C3) : ℝ := As dn s Z + Bs dn s Z * Gfun Z

lemma returnDen_ge {dn s : ℝ} (hdn : 0 ≤ dn) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {Z : C3}
    (hZ : nsq Z = 1) : mR dn ≤ returnDen dn s Z := by
  have := As_ge hdn hs0 hs1 Z hZ
  have := mul_nonneg (Bs_nonneg hdn hs0 Z) (Gfun_nonneg Z)
  unfold returnDen mR; linarith

/-- The cutoff. -/
def chiR (dn s : ℝ) (Z : C3) : ℝ :=
  step (mR dn / 2) (3 * mR dn / 4) (returnDen dn s Z) *
    plateau (1 / 2) (3 / 4) (5 / 4) (3 / 2) (nsq Z) * plateau (-1) (-1 / 2) (3 / 2) 2 s

/-- `Y_s` with `n` replaced by `n_⊥`. -/
def returnBase (dn s : ℝ) (Z : C3) : C3 :=
  (-(dn / 2 : ℂ) * Fpoly Z / (((1 + uFun Z) * returnDen dn s Z : ℝ) : ℂ)) • nperp Z

/-- The cut-off return field. -/
def returnVF (dn s : ℝ) (Z : C3) : C3 := chiR dn s Z • returnBase dn s Z

/-- **The return flow** `ψ_s`. -/
def returnFlow (dn s : ℝ) (Z : C3) : C3 := flow (returnVF dn) s Z

/-- **Its inverse** `ψ_s⁻¹`: the same field integrated from `s` back to `0`. -/
def returnFlowInv (dn s : ℝ) (Z : C3) : C3 := flowInv (returnVF dn) s Z

lemma returnVF_eq {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn ≤ 1 / 3) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {Z : C3} (hZ : nsq Z = 1) : returnVF dn s Z = returnField dn s Z := by
  have hm := mR_pos hdn3
  have hD := returnDen_ge hdn hs0 hs1 hZ
  have hχ : chiR dn s Z = 1 := by
    unfold chiR
    rw [step_eq_one (by linarith) (by linarith), plateau_eq_one (by norm_num) (by norm_num)
      (by rw [hZ]; norm_num) (by rw [hZ]; norm_num),
      plateau_eq_one (by norm_num) (by norm_num) (by linarith) (by linarith)]
    norm_num
  rw [returnVF, hχ, one_smul, returnBase, nperp_unit hZ, returnField, returnDen]

lemma contDiffAt_returnDen (dn : ℝ) {p : ℝ × C3} (hZ : nsq p.2 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun q : ℝ × C3 => returnDen dn q.1 q.2) p := by
  have hu : ContDiffAt ℝ n (fun q : ℝ × C3 => uFun q.2) p :=
    (contDiffAt_uFun hZ).comp p contDiff_snd.contDiffAt
  have h1 : (1 : ℝ) + uFun p.2 ≠ 0 := by linarith [uFun_nonneg p.2]
  unfold returnDen As Bs
  exact (contDiffAt_const.sub (((contDiffAt_const.mul contDiffAt_fst).mul contDiffAt_const).mul
    (hu.div (contDiffAt_const.add hu) h1))).add
    (((contDiffAt_fst.mul contDiffAt_const).div ((contDiffAt_const.add hu).pow 2)
    (pow_ne_zero 2 h1)).mul ((contDiff_Gfun.comp contDiff_snd).contDiffAt))

lemma returnVF_smooth {dn : ℝ} (hdn3 : dn ≤ 1 / 3) :
    ContDiff ℝ ∞ (fun p : ℝ × C3 => returnVF dn p.1 p.2) := by
  have hm := mR_pos hdn3
  have hnsq : ContDiff ℝ ∞ (fun p : ℝ × C3 => nsq p.2) := contDiff_nsq.comp contDiff_snd
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h1 : nsq p.2 < 1 / 2
  · apply contDiffAt_of_eventually_zero
    filter_upwards [hnsq.continuous.continuousAt.eventually_lt continuousAt_const h1] with q hq
    simp only [returnVF, chiR, Pi.zero_apply]
    rw [plateau_eq_zero_left (by norm_num : (1 / 2 : ℝ) < 3 / 4) hq.le]
    simp
  push Not at h1
  have hZ : nsq p.2 ≠ 0 := by linarith
  have hD := contDiffAt_returnDen dn hZ (n := ∞)
  by_cases h2 : returnDen dn p.1 p.2 < mR dn / 2
  · apply contDiffAt_of_eventually_zero
    filter_upwards [hD.continuousAt.eventually_lt continuousAt_const h2] with q hq
    simp only [returnVF, chiR, Pi.zero_apply]
    rw [step_eq_zero (by linarith : mR dn / 2 < 3 * mR dn / 4) hq.le]
    simp
  push Not at h2
  have hχ : ContDiffAt ℝ ∞ (fun q : ℝ × C3 => chiR dn q.1 q.2) p := by
    unfold chiR
    exact (((step_contDiff _ _).contDiffAt.comp p hD).mul
      ((plateau_contDiff _ _ _ _).comp hnsq).contDiffAt).mul
      ((plateau_contDiff _ _ _ _).comp contDiff_fst).contDiffAt
  have hu : ContDiffAt ℝ ∞ (fun q : ℝ × C3 => uFun q.2) p :=
    (contDiffAt_uFun hZ).comp p contDiff_snd.contDiffAt
  have hden0 : (1 + uFun p.2) * returnDen dn p.1 p.2 ≠ 0 :=
    mul_ne_zero (by linarith [uFun_nonneg p.2]) (by linarith)
  have hinv : ContDiffAt ℝ ∞ (fun q : ℝ × C3 =>
      ((1 / ((1 + uFun q.2) * returnDen dn q.1 q.2) : ℝ) : ℂ)) p :=
    ofRealCLM.contDiff.contDiffAt.comp p
      (contDiffAt_const.div ((contDiffAt_const.add hu).mul hD) hden0)
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × C3 =>
      -(dn / 2 : ℂ) * Fpoly q.2 / (((1 + uFun q.2) * returnDen dn q.1 q.2 : ℝ) : ℂ)) p := by
    have : (fun q : ℝ × C3 =>
        -(dn / 2 : ℂ) * Fpoly q.2 / (((1 + uFun q.2) * returnDen dn q.1 q.2 : ℝ) : ℂ)) =
        fun q => -(dn / 2 : ℂ) * Fpoly q.2 * ((1 / ((1 + uFun q.2) * returnDen dn q.1 q.2) : ℝ) : ℂ) := by
      funext q; push_cast; ring
    rw [this]
    exact (contDiffAt_const.mul ((contDiff_Fpoly.comp contDiff_snd).contDiffAt)).mul hinv
  exact hχ.smul (hs.smul ((contDiffAt_nperp hZ).comp p contDiff_snd.contDiffAt))

lemma chiR_hasCompactSupport (dn : ℝ) :
    HasCompactSupport (fun p : ℝ × C3 => chiR dn p.1 p.2) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × C3) 4)
  intro p hp
  by_contra hne
  apply hp
  rw [mem_closedBall_zero_iff]
  unfold chiR at hne
  have hT := plateau_ne_zero (by norm_num) (by norm_num) (right_ne_zero_of_mul hne)
  have hZ := plateau_ne_zero (by norm_num) (by norm_num)
    (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
  rw [norm_prod_le_iff]
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hT.1, hT.2]
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro j
    have h1 := normSq_le_nsq p.2 j
    rw [normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (p.2 j)]

theorem returnVF_csField {dn : ℝ} (hdn3 : dn ≤ 1 / 3) : CSField (returnVF dn) where
  smooth := returnVF_smooth hdn3
  compact := (chiR_hasCompactSupport dn).smul_right
    (f' := fun p : ℝ × C3 => returnBase dn p.1 p.2)

/-! #### `‖Z‖²` is a first integral; the flow on the unit sphere -/

lemma hasFDerivAt_nsq (Z : C3) : HasFDerivAt nsq (fderiv ℝ nsq Z) Z :=
  ((contDiff_nsq (n := 1)).differentiable one_ne_zero Z).hasFDerivAt

lemma fderiv_nsq (Z v : C3) : fderiv ℝ nsq Z v = 2 * (herm Z v).re := by
  apply fderiv_apply_of_line ((contDiff_nsq (n := 1)).differentiable one_ne_zero Z)
  have h := hasDerivAt_quad (nsq Z) (herm Z v).re (nsq v)
  convert h using 1
  funext t
  rw [nsq_add_smul]

lemma herm_returnVF (dn s : ℝ) (Z : C3) : herm Z (returnVF dn s Z) = 0 := by
  by_cases hZ : nsq Z = 0
  · have : chiR dn s Z = 0 := by
      unfold chiR
      rw [plateau_eq_zero_left (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by rw [hZ]; norm_num)]
      simp
    rw [returnVF, this, zero_smul]
    simp [herm]
  · rw [returnVF, herm_rsmul, returnBase, herm_smul_right, herm_nperp hZ, mul_zero, mul_zero]

theorem nsq_returnFlow {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    nsq (returnFlow dn s Z) = nsq Z :=
  (returnVF_csField hdn3).flow_firstIntegral (Q := nsq) hasFDerivAt_nsq
    (fun t y => by rw [fderiv_nsq, herm_returnVF]; simp) s Z

theorem nsq_returnFlowInv {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    nsq (returnFlowInv dn s Z) = nsq Z :=
  (returnVF_csField hdn3).flowInv_firstIntegral (Q := nsq) hasFDerivAt_nsq
    (fun t y => by rw [fderiv_nsq, herm_returnVF]; simp) s Z

@[simp] theorem returnFlow_zero {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (Z : C3) : returnFlow dn 0 Z = Z :=
  (returnVF_csField hdn3).flow_zero Z

theorem returnFlowInv_smooth {dn : ℝ} (hdn3 : dn ≤ 1 / 3) :
    ContDiff ℝ ∞ (fun p : ℝ × C3 => returnFlowInv dn p.1 p.2) :=
  (returnVF_csField hdn3).flowInv_smooth

theorem returnFlow_returnFlowInv {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    returnFlow dn s (returnFlowInv dn s Z) = Z := (returnVF_csField hdn3).flow_flowInv s Z

theorem returnFlowInv_injective {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) :
    Function.Injective (returnFlowInv dn s) := (returnVF_csField hdn3).flowInv_injective s

/-! ### Proposition prop:rtc-return: `ψ_s^* ω_s = ω_FS` -/

/-- **Proposition prop:rtc-return.** For every smooth family `φ₀ : E → ℂ³` of unit vectors and
`s ∈ [0,1]`: `ψ_s^* ω_s = ω_0 = ω_FS` (as coordinate 2-forms on `E`). -/
theorem returnFlow_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {dn : ℝ}
    (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) {φ₀ : E → C3} (hφ : ContDiff ℝ ∞ φ₀)
    (hZ : ∀ x, nsq (φ₀ x) = 1) {s : ℝ} (hs : s ∈ Icc 0 1) :
    pull2 (fun x => returnFlow dn s (φ₀ x)) (omegaS dn s) = pull2 φ₀ (omegaS dn 0) := by
  have hdn3' : dn ≤ 1 / 3 := hdn3.le
  have hV := returnVF_csField hdn3'
  have hmem : ∀ t, sigT s t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨(sigT_mem hs.1 t).1, (sigT_mem hs.1 t).2.trans hs.2⟩
  have hunit : ∀ t x, nsq (returnFlow dn (sigT s t) (φ₀ x)) = 1 := fun t x =>
    (nsq_returnFlow hdn3' _ _).trans (hZ x)
  set U : Set C3 := {Z | Z ≠ 0}
  have hU : IsOpen U := isOpen_ne
  -- smoothness of `(t, Z) ↦ λ_{σ(t)}(Z)` on `ℝ × U`, via the affine formula
  have hΛ : ContDiffOn ℝ ∞ (fun p : ℝ × C3 => lamS dn (sigT s p.1) p.2) (univ ×ˢ U) := by
    have h0 : ContDiffOn ℝ ∞ (fun p : ℝ × C3 => lamS dn 0 p.2) (univ ×ˢ U) :=
      (contDiffOn_lamS dn 0).comp contDiffOn_snd (fun p (hp : p ∈ univ ×ˢ U) => hp.2)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × C3 => lamS dn 1 p.2) (univ ×ˢ U) :=
      (contDiffOn_lamS dn 1).comp contDiffOn_snd (fun p (hp : p ∈ univ ×ˢ U) => hp.2)
    have hσ : ContDiffOn ℝ ∞ (fun p : ℝ × C3 => sigT s p.1) (univ ×ˢ U) :=
      ((sigT_contDiff s).comp contDiff_fst).contDiffOn
    refine (h0.add (hσ.smul (h1.sub h0))).congr fun p (hp : p ∈ univ ×ˢ U) => ?_
    exact lamS_affine dn _ hp.2
  have key := pull2_d1_const_of_dt (Λ := fun t => lamS dn (sigT s t)) (U := U)
    (φ := fun t x => returnFlow dn (sigT s t) (φ₀ x))
    (V := fun t y => deriv (sigT s) t • returnVF dn (sigT s t) y)
    hU hΛ (hV.family_smooth s hφ)
    (fun t x => ne_zero_of_nsq_eq_one (hunit t x))
    (fun t x => hV.family_hasDerivAt s φ₀ t x) ?_ 1
  · simp only [sigT_one, sigT_zero, returnFlow_zero hdn3'] at key
    exact key
  · intro t
    funext x
    ext ξ
    have hy := hunit t x
    simp only [pull1_apply, Pi.add_apply, ContinuousLinearMap.add_apply, contract_apply,
      ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply, Pi.zero_apply]
    generalize (fderiv ℝ (fun x => returnFlow dn (sigT s t) (φ₀ x)) x) ξ = η
    generalize returnFlow dn (sigT s t) (φ₀ x) = y at hy ⊢
    rw [returnVF_eq hdn hdn3' (hmem t).1 (hmem t).2 hy]
    change deriv (sigT s) t * omegaS dn (sigT s t) y (returnField dn (sigT s t) y) _ +
      SymplecticPacking.Forms.dtForm (fun t => lamS dn (sigT s t)) t y _ = 0
    rw [returnField_spec hdn hdn3 (hmem t).1 (hmem t).2 hy]
    -- the time derivative of `λ_{σ(t)}` at `y`
    have hd : HasDerivAt (fun r => lamS dn (sigT s r) y)
        (deriv (sigT s) t • (lamS dn 1 y - lamS dn 0 y)) t := by
      have he : (fun r => lamS dn (sigT s r) y) =
          fun r => lamS dn 0 y + sigT s r • (lamS dn 1 y - lamS dn 0 y) := by
        funext r; exact lamS_affine dn _ (ne_zero_of_nsq_eq_one hy)
      rw [he]
      exact ((sigT_hasDerivAt s t).smul_const _).const_add _
    simp only [SymplecticPacking.Forms.dtForm, hd.deriv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    linear_combination (deriv (sigT s) t) * lamS_sub_unit dn hy η

/-- `(ψ_s⁻¹)^* ω_FS = ω_s` on smooth families of unit vectors. -/
theorem returnFlowInv_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {dn : ℝ}
    (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) {φ₀ : E → C3} (hφ : ContDiff ℝ ∞ φ₀)
    (hZ : ∀ x, nsq (φ₀ x) = 1) {s : ℝ} (hs : s ∈ Icc 0 1) :
    pull2 (fun x => returnFlowInv dn s (φ₀ x)) (omegaS dn 0) = pull2 φ₀ (omegaS dn s) := by
  have hdn3' : dn ≤ 1 / 3 := hdn3.le
  have hφ' : ContDiff ℝ ∞ (fun x => returnFlowInv dn s (φ₀ x)) :=
    (returnFlowInv_smooth hdn3').comp (contDiff_const.prodMk hφ)
  have h := returnFlow_pullback hdn hdn3 hφ'
    (fun x => (nsq_returnFlowInv hdn3' s _).trans (hZ x)) hs
  simp only [returnFlow_returnFlowInv hdn3'] at h
  exact h.symm

/-! ### Equivariance (Lemma lem:rtc-equivariant) -/

/-- `Z ↦ cZ` as a real-linear map. -/
def gaugeC3 (c : ℂ) : C3 →ₗ[ℝ] C3 where
  toFun Z := c • Z
  map_add' x y := smul_add c x y
  map_smul' r x := by ext j; simp; ring

/-- `Z ↦ gZ` as a real-linear map. -/
def cubeRootC3 : C3 →ₗ[ℝ] C3 where
  toFun Z := cubeRoot Z
  map_add' x y := by ext j; fin_cases j <;> simp <;> ring
  map_smul' r x := by ext j; fin_cases j <;> simp <;> ring

lemma returnDen_smul (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) :
    returnDen dn s (c • Z) = returnDen dn s Z := by
  rw [returnDen, returnDen, As_smul dn s Z hc, Bs_smul dn s Z hc, Gfun_smul Z hc]

lemma chiR_gauge (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) :
    chiR dn s (c • Z) = chiR dn s Z := by
  simp only [chiR, returnDen_smul dn s Z hc, nsq_smul_of_unit Z hc]

lemma returnVF_gauge (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) :
    returnVF dn s (c • Z) = c • returnVF dn s Z := by
  simp only [returnVF, chiR_gauge dn s Z hc, returnBase, returnDen_smul dn s Z hc, nsq_smul_of_unit Z hc,
    uFun_smul Z hc, nperp_smul Z hc, Fpoly_smul, smul_smul]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, real_smul]
  linear_combination ((chiR dn s Z : ℂ) * (-(dn / 2 : ℂ)) * Fpoly Z /
    (((1 + uFun Z) * returnDen dn s Z : ℝ) : ℂ) * c * nperp Z j * (conj c * c + 1)) * hc

lemma returnDen_cubeRoot (dn s : ℝ) (Z : C3) : returnDen dn s (cubeRoot Z) = returnDen dn s Z := by
  simp only [returnDen, As, Bs, uFun_cubeRoot, Gfun_cubeRoot]

lemma returnVF_cubeRoot (dn s : ℝ) (Z : C3) :
    returnVF dn s (cubeRoot Z) = cubeRoot (returnVF dn s Z) := by
  simp only [returnVF, chiR, returnBase, returnDen_cubeRoot, nsq_cubeRoot, uFun_cubeRoot,
    Fpoly_cubeRoot, nperp_cubeRoot]
  funext j
  fin_cases j <;> simp [cubeRoot] <;> ring

theorem returnFlowInv_gaugeEquiv {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) {c : ℂ}
    (hc : conj c * c = 1) : returnFlowInv dn s (c • Z) = c • returnFlowInv dn s Z :=
  (returnVF_csField hdn3).flowInv_map (L := LinearMap.toContinuousLinearMap (gaugeC3 c))
    (fun t y => returnVF_gauge dn t y hc) s Z

theorem returnFlowInv_equivariant {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    returnFlowInv dn s (cubeRoot Z) = cubeRoot (returnFlowInv dn s Z) :=
  (returnVF_csField hdn3).flowInv_map (L := LinearMap.toContinuousLinearMap cubeRootC3)
    (fun t y => returnVF_cubeRoot dn t y) s Z

end SymplecticPacking.Return
