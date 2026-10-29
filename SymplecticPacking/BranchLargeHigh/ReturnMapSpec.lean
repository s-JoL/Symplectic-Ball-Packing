import SymplecticPacking.BranchLargeHigh.SecondStageMaps
import SymplecticPacking.BranchLargeHigh.LiftPhaseSmooth
import SymplecticPacking.BranchLargeHigh.ReturnMapPullback

/-!
# Clauses of `returnMap_spec` (supplement `thm:two-packing`, step 6)

The return map is `R = chartLift ∘ (id × unmix)` with `chartLift = chartLiftExplicit`
(`ChartLift.lean`): base coordinate `φ(b, w)` (vector normal transfer), first-normal coordinate
`exp(2πiΨ(b,w)) · z₀`. This file proves, for the mixed region `(mixedModel q a rr).region`,

* `fibMoment_returnMap'`: `u ∘ R = u` (the lift is a phase rotation of `z₀`), everywhere;
* `baseMoment_returnMap'_lt_one`: `μ ∘ R < 1` everywhere (the ball chart lands in `B°(1)`);
* `returnMap'_injOn`: `R` is injective on the region (the tail of `unmix` lies in the transfer
  tube `{|p| < b₂}`, where `φ` is an embedding; the phase depends only on `(b, w)`; `unmix` is
  inverted by `mix` on `u < 1`).

The smoothness and pullback identity `R^*Ω = Ω_mix` follow from the explicit
phase derivative and the mixed-form identity in `ReturnMapPullback.lean`.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two

open Set Manifold Problem
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient openBall capacity largeModelBounds)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

variable {k : ℕ}

/-- The return map `R = chartLift ∘ (id × unmix)` (same expression as `returnMap`). -/
def returnMap' (q : ℕ) (a : ℝ) (rr : Fin k → ℝ) : Surface q × Fibre (q + 3) → E (q + 4) :=
  fun x => chartLift q (Mixed.h1 (q + 2) a rr) (Mixed.h2 (q + 2) a rr) (Prod.map id unmix x)

lemma radialArea_eq' (p : ℝ × ℝ) : radialArea p = Real.pi * (p.1 ^ 2 + p.2 ^ 2) := rfl

lemma radialArea_smul' (c : ℝ) (p : ℝ × ℝ) : radialArea (c • p) = c ^ 2 * radialArea p := by
  rw [radialArea_eq', radialArea_eq']
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Fibre moment**: `u ∘ R = u`. -/
theorem fibMoment_returnMap' (q : ℕ) (a : ℝ) (rr : Fin k → ℝ) (x : Surface q × Fibre (q + 3)) :
    fibMoment (returnMap' q a rr x) = uMom x.2 := by
  unfold returnMap' chartLift
  rw [fibMoment_chartLiftExplicit]
  simp only [Prod.map_snd, unmix_zero]
  rfl

/-- **Base moment**: `μ ∘ R < 1` (the base point lies in the open unit-capacity ball). -/
theorem baseMoment_returnMap'_lt_one (q : ℕ) (a : ℝ) (rr : Fin k → ℝ)
    (x : Surface q × Fibre (q + 3)) : baseMoment (returnMap' q a rr x) < 1 := by
  unfold returnMap' chartLift
  set h₂ := Mixed.h2 (q + 2) a rr
  set y := Prod.map id unmix x
  have h : capacity (basePhi q h₂ y.1 (tailFibre y.2)) < 1 :=
    BranchSmall.VT.transferMap_mem (parameters q) (transferHeight h₂) (y.1.val, tailFibre y.2)
  have he : baseMoment (chartLiftExplicit q (Mixed.h1 (q + 2) a rr) h₂ y) =
      capacity (basePhi q h₂ y.1 (tailFibre y.2)) := by
    simp only [baseMoment, zc_succ_chartLiftExplicit, capacity]
  rw [he]; exact h

/-- The moments of the unmixed tail: `p_j(w) = p_{j+1}(ζ)/(1 − u)`. -/
lemma planeMoments_tail_unmix {q : ℕ} (ζ : Fibre (q + 3)) (hu : uMom ζ < 1) (j : Fin (q + 2)) :
    planeMoments (tailFibre (unmix ζ)) j = planeMoments ζ j.succ / (1 - uMom ζ) := by
  have hs : 0 < 1 - uMom ζ := by linarith
  have hsq : Real.sqrt (1 - uMom ζ) ^ 2 = 1 - uMom ζ := Real.sq_sqrt hs.le
  have hu' : unmix ζ j.succ = (Real.sqrt (1 - uMom ζ))⁻¹ • ζ j.succ := by
    simp [unmix, Fin.succ_ne_zero]
  change radialArea (unmix ζ j.succ) = radialArea (ζ j.succ) / (1 - uMom ζ)
  rw [hu', radialArea_smul', inv_pow, hsq, div_eq_inv_mul]

/-- The two rows of the mixed polytope on the region: `u ≤ h₁` and `h₂ u + Σ_j p_{j+1} ≤ h₂`. -/
lemma mixed_region_bounds {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} {x : Surface q × Fibre (q + 3)}
    (hx : x ∈ (mixedModel q a rr).region) :
    uMom x.2 ≤ Mixed.h1 (q + 2) a rr ∧
      Mixed.h2 (q + 2) a rr * uMom x.2 + ∑ j : Fin (q + 2), planeMoments x.2 j.succ ≤
        Mixed.h2 (q + 2) a rr := by
  obtain ⟨-, hxr⟩ := hx
  have hreg : planeMoments x.2 ∈
      region (largeModelBounds (q + 2) (Mixed.h2 (q + 2) a rr))
        ![Mixed.h1 (q + 2) a rr, Mixed.h2 (q + 2) a rr] := hxr
  have r0 := hreg.2 0
  have r1 := hreg.2 1
  rw [Fin.sum_univ_succ] at r0 r1
  simp only [largeModelBounds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Fin.cons_zero, Fin.cons_succ, zero_mul, Finset.sum_const_zero, add_zero, one_mul] at r0 r1
  exact ⟨r0, r1⟩

/-- **Injectivity** of `R` on the mixed region. -/
theorem returnMap'_injOn {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr) :
    InjOn (returnMap' q a rr) (mixedModel q a rr).region := by
  intro x hx y hy hxy
  set h₂ := Mixed.h2 (q + 2) a rr with hh₂def
  have hh2 : h₂ < 1 / 2 := Mixed.h2_lt_half H
  have hh2p : 0 < h₂ := (Mixed.h1_pos H).trans (Mixed.h1_lt_h2 H)
  have hu1 : Mixed.h1 (q + 2) a rr < 1 := by linarith [Mixed.h1_lt H, H.half_lt]
  have htube : ∀ z ∈ (mixedModel q a rr).region,
      (z.1, tailFibre (unmix z.2)) ∈ BranchSmall.transferDomain q (transferHeight h₂) ∧
        uMom z.2 < 1 := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := mixed_region_bounds hz
    have hu : uMom z.2 < 1 := lt_of_le_of_lt hz0 hu1
    refine ⟨?_, hu⟩
    have hs : 0 < 1 - uMom z.2 := by linarith
    show ∑ j, planeMoments (tailFibre (unmix z.2)) j < transferHeight h₂
    simp only [planeMoments_tail_unmix z.2 hu]
    rw [← Finset.sum_div, div_lt_iff₀ hs]
    have hlt : h₂ * (1 - uMom z.2) < transferHeight h₂ * (1 - uMom z.2) :=
      mul_lt_mul_of_pos_right (by unfold transferHeight; linarith) hs
    linarith
  obtain ⟨hxt, hxu⟩ := htube x hx
  obtain ⟨hyt, hyu⟩ := htube y hy
  have hspec := BranchSmall.vectorTransfer_spec q hh2p
    (b := transferHeight h₂) (by unfold transferHeight; linarith)
    (by unfold transferHeight; linarith)
  have hinjT := hspec.2.1.injective
  have hbase : basePhi q h₂ x.1 (tailFibre (unmix x.2)) =
      basePhi q h₂ y.1 (tailFibre (unmix y.2)) := by
    funext i
    have hi := congrArg (fun z => zc z i.succ) hxy
    simp only [returnMap', chartLift] at hi
    rw [zc_succ_chartLiftExplicit, zc_succ_chartLiftExplicit] at hi
    exact hi
  have hpair : (x.1, tailFibre (unmix x.2)) = (y.1, tailFibre (unmix y.2)) :=
    congrArg Subtype.val (hinjT (a₁ := ⟨_, hxt⟩) (a₂ := ⟨_, hyt⟩) hbase)
  obtain ⟨hb1, hw⟩ := Prod.mk.inj hpair
  have hphase : liftPhase q h₂ x.1 (tailFibre (unmix x.2)) =
      liftPhase q h₂ y.1 (tailFibre (unmix y.2)) := by rw [hb1, hw]
  have h0 := congrArg (fun z => zc z 0) hxy
  have h0' : Complex.exp (2 * Real.pi * Complex.I *
        (liftPhase q h₂ x.1 (tailFibre (unmix x.2)) : ℂ)) * planeC (unmix x.2 0) =
      Complex.exp (2 * Real.pi * Complex.I *
        (liftPhase q h₂ y.1 (tailFibre (unmix y.2)) : ℂ)) * planeC (unmix y.2 0) := by
    simp only [returnMap', chartLift, chartLiftExplicit, zc_ofPhase, Fin.cons_zero] at h0
    exact h0
  rw [hphase] at h0'
  have hc := mul_left_cancel₀ (Complex.exp_ne_zero _) h0'
  have hz0 : unmix x.2 0 = unmix y.2 0 := by
    have e1 := congrArg Complex.re hc
    have e2 := congrArg Complex.im hc
    simp only [planeC] at e1 e2
    exact Prod.ext e1 e2
  have hun : unmix x.2 = unmix y.2 := by
    funext j
    induction j using Fin.cases with
    | zero => exact hz0
    | succ j => exact congrFun hw j
  have h2eq : x.2 = y.2 :=
    calc x.2 = mix (unmix x.2) := (mix_unmix hxu).symm
      _ = mix (unmix y.2) := by rw [hun]
      _ = y.2 := mix_unmix hyu
  exact Prod.ext hb1 h2eq

/-! ### Smoothness of the return map -/

/-- The unmixed tube coordinates `F(b, ζ) = (b, tail(unmix ζ))`. -/
def tubeCoord {q : ℕ} (x : Surface q × Fibre (q + 3)) : Surface q × Fibre (q + 2) :=
  (x.1, tailFibre (unmix x.2))

/-- The set where the return map is analysed: `u < 1` and the unmixed tail in the transfer tube. -/
def returnTube (q : ℕ) (h₂ : ℝ) : Set (Surface q × Fibre (q + 3)) :=
  {x | uMom x.2 < 1 ∧ tubeCoord x ∈ BranchSmall.transferDomain q (transferHeight h₂)}

/-- The mixed region lies in the return tube. -/
lemma region_subset_returnTube {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr) :
    (mixedModel q a rr).region ⊆ returnTube q (Mixed.h2 (q + 2) a rr) := by
  intro z hz
  set h₂ := Mixed.h2 (q + 2) a rr with hh₂def
  have hh2 : h₂ < 1 / 2 := Mixed.h2_lt_half H
  have hu1 : Mixed.h1 (q + 2) a rr < 1 := by linarith [Mixed.h1_lt H, H.half_lt]
  obtain ⟨hz0, hz1⟩ := mixed_region_bounds hz
  have hu : uMom z.2 < 1 := lt_of_le_of_lt hz0 hu1
  refine ⟨hu, ?_⟩
  have hs : 0 < 1 - uMom z.2 := by linarith
  show ∑ j, planeMoments (tailFibre (unmix z.2)) j < transferHeight h₂
  simp only [planeMoments_tail_unmix z.2 hu]
  rw [← Finset.sum_div, div_lt_iff₀ hs]
  have hlt : h₂ * (1 - uMom z.2) < transferHeight h₂ * (1 - uMom z.2) :=
    mul_lt_mul_of_pos_right (by unfold transferHeight; linarith) hs
  linarith

lemma uMom_contDiff {q : ℕ} : ContDiff ℝ ∞ (uMom (q := q)) := by
  have h : (uMom (q := q)) = fun ζ : Fibre (q + 3) =>
      Real.pi * ((ζ 0).1 ^ 2 + (ζ 0).2 ^ 2) := by
    funext ζ; exact radialArea_eq' _
  rw [h]
  have h0 : ContDiff ℝ ∞ (fun ζ : Fibre (q + 3) => ζ 0) := contDiff_apply ℝ (ℝ × ℝ) 0
  exact contDiff_const.mul ((h0.fst.pow 2).add (h0.snd.pow 2))

/-- `unmix` is smooth on `u < 1`. -/
lemma unmix_contDiffOn {q : ℕ} :
    ContDiffOn ℝ ∞ (unmix (q := q)) {ζ | uMom ζ < 1} := by
  rw [contDiffOn_pi]
  intro j
  by_cases hj : j = 0
  · subst hj
    simp only [unmix, ite_true]
    exact (contDiff_apply ℝ (ℝ × ℝ) 0).contDiffOn
  · simp only [unmix, hj, ite_false]
    have hs : ContDiffOn ℝ ∞ (fun ζ : Fibre (q + 3) => (Real.sqrt (1 - uMom ζ))⁻¹)
        {ζ | uMom ζ < 1} := by
      intro ζ hζ
      have hpos : 0 < 1 - uMom ζ := by simp only [mem_setOf_eq] at hζ; linarith
      have hsq : ContDiffAt ℝ ∞ (fun ζ : Fibre (q + 3) => Real.sqrt (1 - uMom ζ)) ζ :=
        (contDiff_const.sub uMom_contDiff).contDiffAt.sqrt hpos.ne'
      exact (hsq.inv (Real.sqrt_pos.2 hpos).ne').contDiffWithinAt
    exact hs.smul (contDiff_apply ℝ (ℝ × ℝ) j).contDiffOn

lemma tailFibre_contDiff {q : ℕ} : ContDiff ℝ ∞ (tailFibre (q := q)) :=
  contDiff_pi.2 fun j => contDiff_apply ℝ (ℝ × ℝ) j.succ

lemma srcModel_eq {q : ℕ} :
    𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) = 𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, Fibre (q + 3)) :=
  modelWithCornersSelf_prod

lemma tgtModel_eq {q : ℕ} :
    𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) = 𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, Fibre (q + 2)) :=
  modelWithCornersSelf_prod

/-- `F` is smooth on `u < 1`. -/
lemma tubeCoord_contMDiffOn {q : ℕ} :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) ∞
      (tubeCoord (q := q)) {x | uMom x.2 < 1} := by
  have h2 : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, Fibre (q + 2)) ∞
      (fun x : Surface q × Fibre (q + 3) => tailFibre (unmix x.2)) {x | uMom x.2 < 1} := by
    have hu : ContMDiffOn 𝓘(ℝ, Fibre (q + 3)) 𝓘(ℝ, Fibre (q + 2)) ∞
        (fun ζ : Fibre (q + 3) => tailFibre (unmix ζ)) {ζ | uMom ζ < 1} :=
      (tailFibre_contDiff.comp_contDiffOn unmix_contDiffOn).contMDiffOn
    rw [srcModel_eq]
    exact hu.comp contMDiff_snd.contMDiffOn (fun x hx => hx)
  have h1 : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun x : Surface q × Fibre (q + 3) => x.1) {x | uMom x.2 < 1} := by
    rw [srcModel_eq]
    exact contMDiff_fst.contMDiffOn
  have := h1.prodMk h2
  rw [← tgtModel_eq] at this
  exact this

/-- **Smoothness of the lift phase** `Ψ = zeroPhase + radialPhase` on the transfer tube: the
zero-section phase is a line integral along the smooth transfer flows (smooth in `b`), and the
radial phase is the parameter integral `∫₀¹ λ_base(φ(b,tw))(∂_t φ(b,tw)) dt` of the smooth transfer
`φ` over segments that stay in the (star-shaped) tube. -/
theorem liftPhase_contMDiffOn (q : ℕ) {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ) ∞
      (fun x : Surface q × Fibre (q + 2) => liftPhase q h₂ x.1 x.2)
      (BranchSmall.transferDomain q (transferHeight h₂)) :=
  LiftSmooth.liftPhase_contMDiffOn_aux hh hh2

lemma planeC_contDiff : ContDiff ℝ ∞ planeC := by
  have h : planeC = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; apply Complex.ext <;> simp [planeC]
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

/-- The fibre coordinate `(t, p) ↦ exp(2πit) · p` is smooth. -/
lemma phaseRot_contDiff :
    ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * (x.1 : ℂ)) * planeC x.2) := by
  refine ContDiff.mul ?_ (planeC_contDiff.comp contDiff_snd)
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst))

/-- **Smoothness** of `R` on the interior of the mixed region (from smoothness of the transfer
`φ` on the tube, of `unmix` on `u < 1`, and of the lift phase `Ψ`). -/
theorem returnMap'_contMDiffOn {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) ∞ (returnMap' q a rr)
      (interior (mixedModel q a rr).region) := by
  set h₂ := Mixed.h2 (q + 2) a rr with hh₂def
  have hh2 : h₂ < 1 / 2 := Mixed.h2_lt_half H
  have hh2p : 0 < h₂ := (Mixed.h1_pos H).trans (Mixed.h1_lt_h2 H)
  refine ContMDiffOn.mono ?_ (interior_subset.trans (region_subset_returnTube H))
  set S := returnTube q h₂
  have hF : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) ∞
      (tubeCoord (q := q)) S := tubeCoord_contMDiffOn.mono (fun x hx => hx.1)
  have hmaps : MapsTo (tubeCoord (q := q)) S (BranchSmall.transferDomain q (transferHeight h₂)) :=
    fun x hx => hx.2
  have hspec := BranchSmall.vectorTransfer_spec q hh2p
    (b := transferHeight h₂) (by unfold transferHeight; linarith)
    (by unfold transferHeight; linarith)
  -- base part
  have hB : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, Ambient (q + 3)) ∞
      (fun x => BranchSmall.vectorTransfer q h₂ (transferHeight h₂) (tubeCoord x)) S :=
    hspec.1.comp hF hmaps
  -- phase part
  have hP : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℝ) ∞
      (fun x => liftPhase q h₂ (tubeCoord x).1 (tubeCoord x).2) S :=
    (liftPhase_contMDiffOn q hh2p hh2).comp hF hmaps
  have hz0 : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun x : Surface q × Fibre (q + 3) => x.2 0) S := by
    have : ContMDiff 𝓘(ℝ, Fibre (q + 3)) 𝓘(ℝ, ℝ × ℝ) ∞ (fun ζ : Fibre (q + 3) => ζ 0) :=
      (contDiff_apply ℝ (ℝ × ℝ) 0).contMDiff
    rw [srcModel_eq]
    exact (this.comp contMDiff_snd).contMDiffOn
  have hPz := hP.prodMk_space hz0
  have hfib : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℂ) ∞
      (fun x => Complex.exp (2 * Real.pi * Complex.I *
        (liftPhase q h₂ (tubeCoord x).1 (tubeCoord x).2 : ℂ)) * planeC (x.2 0)) S := by
    have := phaseRot_contDiff.contMDiff.comp_contMDiffOn hPz
    exact this
  have hcons : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, Fin (q + 4) → ℂ) ∞
      (fun x => (Fin.cons (Complex.exp (2 * Real.pi * Complex.I *
        (liftPhase q h₂ (tubeCoord x).1 (tubeCoord x).2 : ℂ)) * planeC (x.2 0))
        (BranchSmall.vectorTransfer q h₂ (transferHeight h₂) (tubeCoord x)) :
          Fin (q + 4) → ℂ)) S := by
    rw [contMDiffOn_pi_space]
    intro i
    induction i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hfib
    | succ i =>
      simp only [Fin.cons_succ]
      exact contMDiffOn_pi_space.1 hB i
  have hfinal := ofPhase_contDiff.contMDiff.comp_contMDiffOn hcons
  refine hfinal.congr ?_
  intro x _
  simp only [returnMap', chartLift, chartLiftExplicit, Prod.map_fst, Prod.map_snd, id, unmix_zero,
    Function.comp]
  rfl

/-- **Pullback** `R^*Ω = Ω_mix` on the interior of the mixed region (`lem:two-identification`,
`lem:two-mixed`). -/
theorem returnMap'_pullback {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr) :
    ∀ x ∈ interior (mixedModel q a rr).region, ∀ v w,
      coupledForm (returnMap' q a rr x)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) (returnMap' q a rr) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) (returnMap' q a rr) x w) =
      (mixedModel q a rr).form x v w := by
  intro x hx v w
  let h₂ := Mixed.h2 (q + 2) a rr
  have hh2 : h₂ < 1 / 2 := Mixed.h2_lt_half H
  have hh : 0 < h₂ := (Mixed.h1_pos H).trans (Mixed.h1_lt_h2 H)
  have hxt := region_subset_returnTube H (interior_subset hx)
  have hT : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3))
      𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) (tubeMap (q := q)) x := by
    have ho : IsOpen {x : Surface q × Fibre (q + 3) | uMom x.2 < 1} :=
      isOpen_lt (uMom_contDiff.continuous.comp continuous_snd) continuous_const
    exact ((tubeCoord_contMDiffOn x hxt.1).contMDiffAt
      (ho.mem_nhds hxt.1)).mdifferentiableAt (by simp)
  have hΨ := ((liftPhase_contMDiffOn q hh hh2 (tubeMap x) hxt.2).contMDiffAt
    ((BranchSmall.transferDomain_isOpen q _).mem_nhds hxt.2)).mdifferentiableAt (by simp)
  have hR := ((returnMap'_contMDiffOn H x hx).contMDiffAt
    (isOpen_interior.mem_nhds hx)).mdifferentiableAt (by simp)
  have hp := chartLift_pullback_of (h₁ := Mixed.h1 (q + 2) a rr) hh hh2 x hxt.2 hT hΨ hR
    (liftPhase_mfderiv q hh hh2 (tubeMap x) hxt.2) v w
  exact hp.trans (mixedModel_form_eq a rr x hxt.1 v w).symm

end SymplecticPacking.BranchLargeHigh.Two
