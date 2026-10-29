import SymplecticPacking.Handle.HandleStages
import SymplecticPacking.Branch2.Model.Cubic.Handle.HandlePer

/-!
# The three stages of the handle Moser path

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`cons:shd4-moser`): the three concrete stages of the handle Moser path, without
periodicity hypotheses, and their deck invariance.

* `etaPer P λ = perJ (η_λ)`, `etaDot P λ = ∂_λ etaPer P λ` (an explicit one-form, `fderiv` of the
  jointly smooth family in the direction `(1, 0)`), `xiPer P = J(p)β + perJ(ξ − J(p)β)`;
* stage forms `OmS0 P t = Ω₀ + t dα₁`, `OmS1 P λ = Ω₁ + d etaPer_λ`, `OmS2 P τ = OmS1 P 1 + τ dξ`;
  `OmegaFinalPer P = OmS2 P 1`, equal to `OmegaFinal P` over `{u₁ − 1 < u < 1 + u₀}`;
* deck invariance of the primitives and of the stage forms (`etaDot_deck`, `xiPer_deck`,
  `OmS0_preserves`, `OmS1_preserves`, `OmS2_preserves`), the parameters `handleParams P`,
  toricity near `p = h + 2δ_m` and vanishing of the primitives on the three fibres
  (`etaDot_fibre`, `xiPer_fibre`, `alpha1E_fibre`).
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e symm2)
open SymplecticPacking.Bundle (pE dpE u0 u1 annulus stepA bB Omega0loc)
open SymplecticPacking.Bundle.Cubic (OmegaT alpha1E)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

/-! ### Calculus for families of one-forms -/

section family

variable {E : ℝ × E4 → (E4 →L[ℝ] ℝ)}

end family

/-! ### The periodised primitives -/

variable (P : Branch2.VCubic)

/-- `η` as a family on `ℝ × E4`. -/
def etaJ (q : ℝ × E4) : E4 →L[ℝ] ℝ := eta P q.1 q.2

/-- `ξ − J(p)β` (constant family). -/
def xiDJ (q : ℝ × E4) : E4 →L[ℝ] ℝ := xi P q.2 - JbE P q.2

/-- **The periodised first-stage primitive** `η_λ` on the whole cover. -/
def etaPer (lam : ℝ) : Form1 E4 := fun X => perJ (etaJ P) (lam, X)

/-- **Its `λ`-derivative** `∂_λ η_λ` (explicit: `fderiv` in the direction `(1, 0)`). -/
def etaDot (lam : ℝ) : Form1 E4 := fun X => famDot (perJ (etaJ P)) (lam, X)

/-- **The periodised second-stage primitive** `ξ = J(p)β + perU(ξ − J(p)β)`. -/
def xiPer : Form1 E4 := fun X => JbE P X + perJ (xiDJ P) (0, X)

/-- Stage `0`: `Ω_t = Ω₀ + t dα₁`. -/
def OmS0 (t : ℝ) : Form2 E4 := OmegaT P t
/-- Stage `1`: `Ω^{(1)}_λ = Ω₁ + dη_λ`. -/
def OmS1 (lam : ℝ) : Form2 E4 := fun X => OmegaT P 1 X + d1 (etaPer P lam) X
/-- Stage `2`: `Ω^{(2)}_τ = Ω^{(1)}_1 + τ dξ`. -/
def OmS2 (τ : ℝ) : Form2 E4 := fun X => OmS1 P 1 X + τ • d1 (xiPer P) X

/-- **The final form on the whole cover** `Ω_final = Ω₀ + dα₁ + dη₁ + dξ` (periodised). -/
def OmegaFinalPer : Form2 E4 := OmS2 P 1

lemma contDiff_etaJ : ContDiff ℝ ∞ (etaJ P) := eta_smooth P

lemma stripSupp_etaJ : StripSupp (etaJ P) := fun s Y h => eta_eq_zero_of_s P s h

lemma contDiff_xiDJ : ContDiff ℝ ∞ (xiDJ P) :=
  ((xi_smooth P).comp contDiff_snd).sub ((contDiff_JbE P).comp contDiff_snd)

lemma stripSupp_xiDJ : StripSupp (xiDJ P) := fun s Y h => by
  simp [xiDJ, xi_eq_JbE_of_s P h]

lemma contDiff_etaPerJ : ContDiff ℝ ∞ (perJ (etaJ P)) :=
  perJ_smooth (contDiff_etaJ P) (stripSupp_etaJ P)

lemma contDiff_xiDPer : ContDiff ℝ ∞ (perJ (xiDJ P)) :=
  perJ_smooth (contDiff_xiDJ P) (stripSupp_xiDJ P)

lemma contDiff_etaPer (lam : ℝ) : ContDiff ℝ ∞ (etaPer P lam) :=
  (contDiff_etaPerJ P).comp (contDiff_const.prodMk contDiff_id)

lemma contDiff_etaDotJ : ContDiff ℝ ∞ (fun q : ℝ × E4 => etaDot P q.1 q.2) :=
  contDiff_famDot (contDiff_etaPerJ P)

lemma contDiff_xiPer : ContDiff ℝ ∞ (xiPer P) :=
  (contDiff_JbE P).add ((contDiff_xiDPer P).comp (contDiff_const.prodMk contDiff_id))

/-! ### Horizontality and deck invariance of the primitives -/

lemma eta_horiz (lam : ℝ) (Y v : E4) : eta P lam Y v = eta P lam Y (e 2) * v 2 +
    eta P lam Y (e 3) * v 3 := by
  exact eta_horizontal P lam Y v

lemma JbE_horiz (Y v : E4) : JbE P Y v = JbE P Y (e 2) * v 2 + JbE P Y (e 3) * v 3 := by
  simp [JbE, Forms.dc]

lemma xi_horiz (Y v : E4) : xi P Y v = xi P Y (e 2) * v 2 + xi P Y (e 3) * v 3 := by
  obtain ⟨c, hc⟩ := xi_horizontal P Y
  rw [hc]; simp [Forms.dc]

lemma etaPer_horiz (lam : ℝ) (Y v : E4) :
    etaPer P lam Y v = etaPer P lam Y (e 2) * v 2 + etaPer P lam Y (e 3) * v 3 :=
  eta_horiz P lam _ v

lemma xiPer_horiz (Y v : E4) : xiPer P Y v = xiPer P Y (e 2) * v 2 + xiPer P Y (e 3) * v 3 := by
  simp only [xiPer, perJ, xiDJ, add_apply, sub_apply]
  rw [JbE_horiz P Y v, xi_horiz P _ v, JbE_horiz P _ v]
  ring

lemma JbE_TuE (Y : E4) : JbE P (TuE Y) = JbE P Y := by
  have hp : pE (TuE Y) = pE Y := deckU.pE_eq Y
  simp only [JbE, hp]; simp [TuE]

lemma etaJ_deck {T : DeckCore} (hT : IsDeck T) (s : ℝ) (X : E4) :
    perJ (etaJ P) (s, T.T X) = perJ (etaJ P) (s, X) := by
  rcases hT with rfl | rfl
  · exact perJ_TuE _ s X
  · exact perJ_TvE (fun s Y => eta_TvE P s Y) s X

lemma xiDJ_deck {T : DeckCore} (hT : IsDeck T) (X : E4) :
    perJ (xiDJ P) (0, T.T X) = perJ (xiDJ P) (0, X) := by
  rcases hT with rfl | rfl
  · exact perJ_TuE _ 0 X
  · exact perJ_TvE (fun s Y => by simp only [xiDJ]; rw [xi_TvE, JbE_TvE]) 0 X

lemma JbE_deck {T : DeckCore} (hT : IsDeck T) (X : E4) : JbE P (T.T X) = JbE P X := by
  rcases hT with rfl | rfl
  · exact JbE_TuE P X
  · exact JbE_TvE P X

lemma xiPer_deck {T : DeckCore} (hT : IsDeck T) (X : E4) : xiPer P (T.T X) = xiPer P X := by
  simp only [xiPer, JbE_deck P hT, xiDJ_deck P hT]

lemma pull1_etaPer {T : DeckCore} (hT : IsDeck T) (lam : ℝ) (X : E4) :
    pull1 T.T (etaPer P lam) X = etaPer P lam X :=
  pull1_horizontal T (etaPer_horiz P lam) (etaJ_deck P hT lam X)

lemma pull1_xiPer {T : DeckCore} (hT : IsDeck T) (X : E4) :
    pull1 T.T (xiPer P) X = xiPer P X :=
  pull1_horizontal T (xiPer_horiz P) (xiPer_deck P hT X)

lemma pull2_d1_etaPer {T : DeckCore} (hT : IsDeck T) (lam : ℝ) (X : E4) :
    pull2 T.T (d1 (etaPer P lam)) X = d1 (etaPer P lam) X :=
  pull2_d1_of_pull1 T.smooth (contDiff_etaPer P lam) 0
    (fun Y => by rw [pull1_etaPer P hT, add_zero]) X

lemma pull2_d1_xiPer {T : DeckCore} (hT : IsDeck T) (X : E4) :
    pull2 T.T (d1 (xiPer P)) X = d1 (xiPer P) X :=
  pull2_d1_of_pull1 T.smooth (contDiff_xiPer P) 0
    (fun Y => by rw [pull1_xiPer P hT, add_zero]) X

lemma etaDot_apply (lam : ℝ) (X v : E4) :
    HasDerivAt (fun s => etaPer P s X v) (etaDot P lam X v) lam := by
  have hd := (contDiff_etaPerJ P).differentiable (by simp) (lam, X)
  have h := Forms.hasDerivAt_time (G := fun q => perJ (etaJ P) q v) (by fun_prop)
  rwa [fderiv_apply_const hd] at h

lemma etaDot_deck {T : DeckCore} (hT : IsDeck T) (lam : ℝ) (X v : E4) :
    etaDot P lam (T.T X) (fderiv ℝ T.T X v) = etaDot P lam X v := by
  have h1 := etaDot_apply P lam (T.T X) (fderiv ℝ T.T X v)
  have h2 := etaDot_apply P lam X v
  have e : (fun s => etaPer P s (T.T X) (fderiv ℝ T.T X v)) = fun s => etaPer P s X v := by
    funext s
    have := congrArg (fun L : E4 →L[ℝ] ℝ => L v) (pull1_etaPer P hT s X)
    simpa only [Forms.pull1_apply] using this
  rw [e] at h1
  exact h1.unique h2

/-- **The stages are preserved by the deck maps.** -/
theorem OmS1_preserves {T : DeckCore} (hT : IsDeck T) : T.Preserves (OmS1 P) (etaDot P) := by
  refine ⟨fun t X v w => ?_, fun t X v => etaDot_deck P hT t X v⟩
  have h1 := (OmegaT_preserves P T hT).1 1 X v w
  have h2 := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ => B v w) (pull2_d1_etaPer P hT t X)
  simp only [Forms.pull2_apply] at h2
  simp only [OmS1, add_apply, h1, h2]

theorem OmS2_preserves {T : DeckCore} (hT : IsDeck T) :
    T.Preserves (OmS2 P) (fun _ => xiPer P) := by
  refine ⟨fun t X v w => ?_, fun t X v => ?_⟩
  · have h1 := (OmS1_preserves P hT).1 1 X v w
    have h2 := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ => B v w) (pull2_d1_xiPer P hT X)
    simp only [Forms.pull2_apply] at h2
    simp only [OmS2, add_apply, smul_apply, smul_eq_mul, h1, h2]
  · have := congrArg (fun L : E4 →L[ℝ] ℝ => L v) (pull1_xiPer P hT X)
    simpa only [Forms.pull1_apply] using this

theorem OmS0_preserves {T : DeckCore} (hT : IsDeck T) :
    T.Preserves (OmS0 P) (fun _ => alpha1E P) := OmegaT_preserves P T hT

/-! ### The parameters of the handle Moser problem -/

open SymplecticPacking.Qhat.Cubic (Psupp)
open SymplecticPacking.Bundle (bpoints)

/-- The parameters: `R`, `P_tor = P_supp`, `h`, `δ = δ_m`, the three fibres. -/
def handleParams : MoserParams where
  R := Rrot
  Ptor := Psupp P
  h := P.h
  δ := deltam P
  F := fibreSetH
  Ptor_lt := Psupp_lt_h P
  δ_pos := deltam_pos P

/-! ### Representations as `d` of global primitives (closedness, skewness) -/

open SymplecticPacking.Return (betaLoc)

lemma OmS0_eq (t : ℝ) : OmS0 P t = d1 (betaLoc + t • alpha1E P) := by
  funext X
  have h1 : DifferentiableAt ℝ betaLoc X := (contDiff_betaLoc.differentiable (by simp)) X
  have h2 : DifferentiableAt ℝ (t • alpha1E P) X :=
    ((contDiff_alpha1E P).const_smul t).differentiable (by simp) X
  rw [Forms.d1_add_apply h1 h2, Forms.d1_smul_const, Return.d1_betaLoc]
  rfl

lemma OmS1_eq (lam : ℝ) : OmS1 P lam = d1 (betaLoc + alpha1E P + etaPer P lam) := by
  funext X
  have h1 := (contDiff_betaLoc.differentiable (by simp)) X
  have h2 := (contDiff_alpha1E P).differentiable (by simp) X
  have h3 := (contDiff_etaPer P lam).differentiable (by simp) X
  rw [Forms.d1_add_apply (h1.add h2) h3, Forms.d1_add_apply h1 h2, Return.d1_betaLoc]
  show OmegaT P 1 X + _ = _
  simp only [OmegaT, one_smul]

lemma OmS2_eq (τ : ℝ) :
    OmS2 P τ = d1 (betaLoc + alpha1E P + etaPer P 1 + τ • xiPer P) := by
  funext X
  have h1 := (contDiff_betaLoc.differentiable (by simp)) X
  have h2 := (contDiff_alpha1E P).differentiable (by simp) X
  have h3 := (contDiff_etaPer P 1).differentiable (by simp) X
  have h4 : DifferentiableAt ℝ (τ • xiPer P) X :=
    ((contDiff_xiPer P).const_smul τ).differentiable (by simp) X
  rw [Forms.d1_add_apply ((h1.add h2).add h3) h4, ← OmS1_eq, Forms.d1_smul_const]
  rfl

lemma contDiff_prim1 (lam : ℝ) : ContDiff ℝ ∞ (betaLoc + alpha1E P + etaPer P lam) :=
  (contDiff_betaLoc.add (contDiff_alpha1E P)).add (contDiff_etaPer P lam)

/-! ### Toricity near the boundary -/

/-- `ι_R Ω_t = −dp` everywhere. -/
theorem OmegaT_toric (t : ℝ) (X : E4) : OmegaT P t X (Rrot X) = -dpE X := by
  rw [Bundle.Cubic.OmegaT_split]
  obtain ⟨r0, r1, r2, r3⟩ := Rrot_apply X
  ext w
  simp only [Forms.splitForm, add_apply, smul_apply, Forms.wedge_apply, smul_eq_mul, dpE, neg_apply,
    dc_apply, r0, r1, r2, r3]
  ring

lemma etaPer_zero_p (lam : ℝ) {X : E4} (h : Psupp P < pE X) : etaPer P lam X = 0 := by
  simp only [etaPer, perJ, etaJ]
  exact (eta_eventually_zero P lam (Or.inr (by rwa [pE_Ush]))).self_of_nhds

lemma isOpen_far : IsOpen {X : E4 | Psupp P < pE X} := isOpen_lt continuous_const continuous_pE

lemma d1_etaPer_far (lam : ℝ) {X : E4} (h : Psupp P < pE X) : d1 (etaPer P lam) X = 0 := by
  apply d1_eq_zero_of
  filter_upwards [(isOpen_far P).mem_nhds h] with Y hY using etaPer_zero_p P lam hY

lemma etaDot_far (lam : ℝ) {X : E4} (h : Psupp P < pE X) : etaDot P lam X = 0 := by
  apply famDot_eq_zero
  filter_upwards [((isOpen_far P).preimage continuous_snd).mem_nhds
    (show (lam, X) ∈ Prod.snd ⁻¹' {X : E4 | Psupp P < pE X} from h)]
    with q hq using etaPer_zero_p P q.1 hq

lemma xi_e2 (Y : E4) : xi P Y (e 2) = 0 := by
  obtain ⟨c, hc⟩ := xi_horizontal P Y; rw [hc]; simp [Forms.dc]

lemma xiPer_e2 (Y : E4) : xiPer P Y (e 2) = 0 := by
  simp [xiPer, perJ, xiDJ, xi_e2, JbE, Forms.dc]

/-- The `dv`-coefficient of `ξ`. -/
def fX (Y : E4) : ℝ := xiPer P Y (e 3)

lemma xiPer_eq_fX : xiPer P = fun Y => fX P Y • dc 3 := by
  funext Y; ext v
  rw [xiPer_horiz, xiPer_e2]
  simp [fX, dc_apply, mul_comm]

lemma contDiff_fX : ContDiff ℝ ∞ (fX P) := (contDiff_xiPer P).clm_apply contDiff_const

lemma fX_far : ∃ c : ℝ → ℝ → ℝ, ∀ Y : E4, Psupp P < pE Y →
    fX P Y = c (Int.fract (Y 2)) (pE Y) * bB (Y 3) := by
  obtain ⟨c, hc⟩ := xi_toric_near_boundary P
  refine ⟨c, fun Y hY => ?_⟩
  have hZ : Psupp P < pE (Ush (-⌊Y 2⌋) Y) := by rwa [pE_Ush]
  simp only [fX, xiPer, perJ, xiDJ, add_apply, sub_apply, hc _ hZ, fract_eq_Ush, pE_Ush,
    Ush_apply3]
  simp [JbE, Forms.dc]

/-- `ι_R dξ = 0` on `{p > P_supp}`. -/
theorem d1_xiPer_toric {X : E4} (h : Psupp P < pE X) : d1 (xiPer P) X (Rrot X) = 0 := by
  obtain ⟨c, hc⟩ := fX_far P
  have hd : DifferentiableAt ℝ (fX P) X := (contDiff_fX P).differentiable (by simp) X
  have hconst : (fun s => fX P (rotE s X)) = fun _ => fX P X := by
    funext s
    obtain ⟨e2, e3, ep⟩ := rotE_coords s X
    rw [hc _ (by rw [ep]; exact h), hc _ h, e2, e3, ep]
  have h0 : rotE 0 X = X := by simp [rotE]
  have hder := ((h0 ▸ hd).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rotE X))
  have hder' : HasDerivAt (fun s => fX P (rotE s X)) (fderiv ℝ (fX P) X (Rrot X)) 0 := by
    rw [← h0]; simpa [Function.comp_def, h0] using hder
  rw [hconst] at hder'
  have hz := hder'.unique (hasDerivAt_const 0 (fX P X))
  rw [xiPer_eq_fX, d1_smul_const_form hd]
  ext w
  simp [Forms.wedge_apply, hz, (Rrot_apply X).2.2.2]

/-! ### The three fibres -/

lemma etaDot_fibre (lam : ℝ) {X : E4} (hX : X ∈ fibreSetH) : etaDot P lam X = 0 := by
  obtain ⟨j, hj, -⟩ := fract_fibre hX
  have hn : Int.fract (X 2) ∉ Icc u0 u1 := by rw [hj]; exact bpoints_fst j
  have hev := Bundle.eventually_fract_notMem u0_pos u1_lt_one hn
  apply famDot_eq_zero
  have hc : Filter.Tendsto (fun q : ℝ × E4 => q.2 2) (𝓝 (lam, X)) (𝓝 (X 2)) :=
    ((dc 2).continuous.comp continuous_snd).tendsto _
  filter_upwards [hc.eventually hev] with q hq
  apply perJ_zero (stripSupp_etaJ P)
  simp only [mem_Icc, not_and_or, not_le] at hq
  rcases hq with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

lemma xi_zero_of_bB {Z : E4} (h : bB (Z 3) = 0) : xi P Z = 0 := by
  simp [xi, xiA, JbE, h, chartInv_apply3]

lemma xiPer_fibre {X : E4} (hX : X ∈ fibreSetH) : xiPer P X = 0 := by
  have hb := bB_fibre hX
  have hb' : bB (Ush (-⌊X 2⌋) X 3) = 0 := by rwa [Ush_apply3]
  simp [xiPer, perJ, xiDJ, xi_zero_of_bB P hb', JbE, hb, hb']

lemma alpha1E_fibre {X : E4} (hX : X ∈ fibreSetH) : alpha1E P X = 0 := by
  obtain ⟨j, m, n, h2, h3⟩ := hX
  have hper := Bundle.Cubic.alpha1_periodic P
  have hu : ∀ (f : ℝ → ℝ), (∀ u, f (u + 1) = f u) → ∀ (u : ℝ) (k : ℤ), f (u + k) = f u :=
    fun f hf u k => by
      have hp : Function.Periodic f 1 := hf
      rw [show (k : ℝ) = k * 1 by ring, hp.int_mul k]
  have e1 : (Bundle.Cubic.alpha1 P).cu (X 2) (X 3) (pE X) =
      (Bundle.Cubic.alpha1 P).cu (bpoints j).1 (bpoints j).2 (pE X) := by
    rw [h2, h3, hu (fun u => (Bundle.Cubic.alpha1 P).cu u _ (pE X)) (fun u => (hper u _ _).1),
      hu (fun v => (Bundle.Cubic.alpha1 P).cu _ v (pE X)) (fun v => (hper _ v _).2.2.1)]
  have e2 : (Bundle.Cubic.alpha1 P).cv (X 2) (X 3) (pE X) =
      (Bundle.Cubic.alpha1 P).cv (bpoints j).1 (bpoints j).2 (pE X) := by
    rw [h2, h3, hu (fun u => (Bundle.Cubic.alpha1 P).cv u _ (pE X)) (fun u => (hper u _ _).2.1),
      hu (fun v => (Bundle.Cubic.alpha1 P).cv _ v (pE X)) (fun v => (hper _ v _).2.2.2)]
  have hz := Bundle.Cubic.alpha1_fibre_zero P j (pE X)
  simp only [alpha1E, dc_apply, e1, e2, hz.1, hz.2, zero_smul, add_zero]

end SymplecticPacking.Handle.Cubic
