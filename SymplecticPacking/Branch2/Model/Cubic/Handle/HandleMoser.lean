import SymplecticPacking.Handle.HandleMoser
import SymplecticPacking.Branch2.Model.Cubic.Handle.HandleStages

/-!
# The concrete handle Moser map

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`prop:shd4-moser`,
`lem:pre-moser`): **the concrete handle Moser map**.

The three stages (`Cubic/Handle/HandleStages.lean`) — `Ω₀ + t dα₁` (primitive `α₁`), `Ω₁ + dη_λ`
(primitive `∂_λη_λ`), `Ω^{(1)}_1 + τ dξ` (primitive `ξ`), with `η`, `ξ` periodised over the cover —
are packaged as `MoserStageB`s (`stage0`, `stage1`, `stage2`) and concatenated
(`handleData P = concat3B …`, `Handle/MoserBoxConcat.lean`) with parameters `handleParams P`:
`R = 2π(−y∂_x + x∂_y)`, `P_tor = P_supp`, `δ = δ_m`, `F = ` the three fibres (all lifts).
Hypotheses checked here: smoothness, closedness (`d` of global primitives), `∂_tΩ = da`,
nondegeneracy on `{p < h + 2δ_m}` (stage-wise nondegeneracy on the fundamental strip from
`firstStage_nondeg`, `secondStage_nondeg`, transported by the deck maps), toricity on
`{p > P_supp}`, vanishing of the primitives on the fibres, and deck invariance.

Main theorem `handleMoser`: `Φ = handlePhi P`, `Φ⁻¹ = handlePhiInv P` (global, `C^∞`, mutually
inverse) with `Φ^* Ω_final = Ω₀loc` on `{p ≤ h + δ_m}` (`Ω_final = OmegaFinalPer P`, equal to
`OmegaFinal P` over `{u₁ − 1 < u < 1 + u₀}`), invariance of `{p ≤ h}`, `{p < h}`, fixed fibres,
and commutation of `Φ`, `Φ⁻¹` with the deck maps `TuE`, `TvE`.
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc d1 pull1 pull2 Form1 Form2 e pf)
open SymplecticPacking.Bundle (pE dpE u0 u1 annulus Omega0loc)
open SymplecticPacking.Bundle.Cubic (OmegaT alpha1E)
open SymplecticPacking.Qhat.Cubic (Psupp)
open scoped ContDiff Real

set_option synthInstance.maxHeartbeats 200000

variable (P : Branch2.VCubic)

/-! ### Agreement with the stage forms of `cons:shd4-eta` and `cons:shd4-xi` over the fundamental strip -/

lemma etaPer_eventually (lam : ℝ) {X : E4} (hX : X ∈ stripU) : etaPer P lam =ᶠ[𝓝 X] eta P lam := by
  filter_upwards [isOpen_stripU.mem_nhds hX] with Y hY
  exact perJ_eq_on_strip (stripSupp_etaJ P) hY.1 hY.2

lemma xiPer_eventually {X : E4} (hX : X ∈ stripU) : xiPer P =ᶠ[𝓝 X] xi P := by
  filter_upwards [isOpen_stripU.mem_nhds hX] with Y hY
  simp only [xiPer, perJ_eq_on_strip (stripSupp_xiDJ P) hY.1 hY.2, xiDJ]
  abel

theorem OmS1_eq_firstStage (lam : ℝ) {X : E4} (hX : X ∈ stripU) :
    OmS1 P lam X = firstStage P lam X := by
  simp only [OmS1, firstStage, d1_congr (etaPer_eventually P lam hX)]

theorem OmS2_eq_secondStage (τ : ℝ) {X : E4} (hX : X ∈ stripU) :
    OmS2 P τ X = secondStage P τ X := by
  simp only [OmS2, secondStage, OmS1_eq_firstStage P 1 hX, d1_congr (xiPer_eventually P hX)]

/-- **`Ω_final` (periodised) agrees with `OmegaFinal P` over the strip** `{u₁ − 1 < u < 1 + u₀}`. -/
theorem OmegaFinalPer_eq {X : E4} (hX : X ∈ stripU) : OmegaFinalPer P X = OmegaFinal P X :=
  OmS2_eq_secondStage P 1 hX

/-! ### Nondegeneracy -/

lemma nondeg_of_strip {Om : ℝ → Form2 E4} {a : ℝ → Form1 E4}
    (h : ∀ T : DeckCore, IsDeck T → T.Preserves Om a) (hskew : ∀ t X v w, Om t X v w = -Om t X w v)
    (t : ℝ) (h0 : ∀ X, X ∈ stripU → pE X < P.h + 2 * deltam P →
      ∀ v, (∀ w, Om t X v w = 0) → v = 0) (X : E4) (hX : pE X < P.h + 2 * deltam P) :
    pf (Om t X) ≠ 0 := by
  apply pf_ne_zero_of_nondeg (hskew t X)
  revert hX
  refine deck_reduce (gens h) (Q := fun X => pE X < P.h + 2 * deltam P →
    ∀ v, (∀ w, Om t X v w = 0) → v = 0) (fun T hT Y hY hp => ?_)
    (fun Y h2 h3 hp => h0 Y (mem_stripU h2) hp) X
  rw [T.pE_eq] at hp
  exact nondeg_deck T hT t (hY hp)

/-! ### The three stages -/

lemma OmS0_skew (t : ℝ) (X v w : E4) : OmS0 P t X v w = -OmS0 P t X w v := by
  rw [OmS0_eq]; exact Forms.d1_skew _ _ _ _
lemma OmS1_skew (t : ℝ) (X v w : E4) : OmS1 P t X v w = -OmS1 P t X w v := by
  rw [OmS1_eq]; exact Forms.d1_skew _ _ _ _
lemma OmS2_skew (t : ℝ) (X v w : E4) : OmS2 P t X v w = -OmS2 P t X w v := by
  rw [OmS2_eq]; exact Forms.d1_skew _ _ _ _

lemma contDiff_OmS0 : ContDiff ℝ ∞ (fun q : ℝ × E4 => OmS0 P q.1 q.2) := by
  refine contDiff_form2 fun v w => ?_
  have e : (fun q : ℝ × E4 => OmS0 P q.1 q.2 v w) =
      fun q => Omega0loc q.2 v w + q.1 * d1 (alpha1E P) q.2 v w := by
    funext q; simp [OmS0, OmegaT]
  rw [e]
  exact (ev2 contDiff_Omega0loc v w).add (contDiff_fst.mul
    (ev2 (contDiff_d1_const (contDiff_alpha1E P)) v w))

lemma contDiff_OmS1 : ContDiff ℝ ∞ (fun q : ℝ × E4 => OmS1 P q.1 q.2) := by
  refine contDiff_form2 fun v w => ?_
  have e : (fun q : ℝ × E4 => OmS1 P q.1 q.2 v w) =
      fun q => OmS0 P 1 q.2 v w + d1 (fun Y => perJ (etaJ P) (q.1, Y)) q.2 v w := by
    funext q; simp only [OmS1, OmS0, add_apply]; rfl
  rw [e]
  exact ((contDiff_OmS0 P).comp (contDiff_const.prodMk contDiff_snd) |> fun h => ev2 h v w).add
    (ev2 (contDiff_d1_family (contDiff_etaPerJ P)) v w)

lemma contDiff_OmS2 : ContDiff ℝ ∞ (fun q : ℝ × E4 => OmS2 P q.1 q.2) := by
  refine contDiff_form2 fun v w => ?_
  have e : (fun q : ℝ × E4 => OmS2 P q.1 q.2 v w) =
      fun q => OmS1 P 1 q.2 v w + q.1 * d1 (xiPer P) q.2 v w := by
    funext q; simp [OmS2]
  rw [e]
  exact ((contDiff_OmS1 P).comp (contDiff_const.prodMk contDiff_snd) |> fun h => ev2 h v w).add
    (contDiff_fst.mul (ev2 (contDiff_d1_const (contDiff_xiPer P)) v w))

lemma OmegaT_nondeg_pf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (X : E4)
    (hX : pE X < P.h + 2 * deltam P) : pf (OmS0 P t X) ≠ 0 := by
  rw [OmS0, Bundle.Cubic.OmegaT_sq]; exact (deltam_kappaT P ht _ _ hX).ne'

/-- **Stage 0**: `Ω_t = Ω₀ + t dα₁`, primitive `α₁`. -/
def stage0 : MoserStageB (handleParams P) where
  Om := OmS0 P
  a := fun _ => alpha1E P
  smooth_Om := contDiff_OmS0 P
  smooth_a := (contDiff_alpha1E P).comp contDiff_snd
  skew := OmS0_skew P
  closed s _ := by
    rw [OmS0_eq]
    exact Forms.isClosed2_d1 ((contDiff_betaLoc.add ((contDiff_alpha1E P).const_smul s)).of_le
      (by simp))
  dt s X v w := by
    have : HasDerivAt (fun r => Omega0loc X v w + r * d1 (alpha1E P) X v w)
        (d1 (alpha1E P) X v w) s := by
      simpa using ((hasDerivAt_id s).mul_const (d1 (alpha1E P) X v w)).const_add
        (Omega0loc X v w)
    simpa [OmS0, OmegaT] using this
  nondeg s hs X hX := OmegaT_nondeg_pf P s hs X hX
  toric s _ X _ _ := OmegaT_toric P s X
  toric_a s _ X _ _ := by
    change alpha1E P X (Rrot X) = 0
    simp [alpha1E, (Rrot_apply X).2.2.1, (Rrot_apply X).2.2.2]
  fibre s _ X hX := alpha1E_fibre P hX

/-- **Stage 1**: `Ω₁ + dη_λ`, primitive `∂_λ η_λ`. -/
def stage1 : MoserStageB (handleParams P) where
  Om := OmS1 P
  a := etaDot P
  smooth_Om := contDiff_OmS1 P
  smooth_a := contDiff_etaDotJ P
  skew := OmS1_skew P
  closed s _ := by
    rw [OmS1_eq]; exact Forms.isClosed2_d1 ((contDiff_prim1 P s).of_le (by simp))
  dt s X v w := by
    have h := (hasDerivAt_d1_family (contDiff_etaPerJ P) s X v w).const_add (OmegaT P 1 X v w)
    exact h
  nondeg s hs X hX := nondeg_of_strip P (fun T hT => OmS1_preserves P hT) (OmS1_skew P) s
    (fun Y hY hp v hv => firstStage_nondeg P hs hp v fun w => by
      rw [← OmS1_eq_firstStage P s hY]; exact hv w) X hX
  toric s _ X h1 _ := by
    change OmegaT P 1 X (Rrot X) + d1 (etaPer P s) X (Rrot X) = _
    rw [d1_etaPer_far P s h1, OmegaT_toric]; simp
  toric_a s _ X h1 _ := by
    change etaDot P s X (Rrot X) = 0
    rw [etaDot_far P s h1]; rfl
  fibre s _ X hX := etaDot_fibre P s hX

/-- **Stage 2**: `Ω^{(1)}_1 + τ dξ`, primitive `ξ`. -/
def stage2 : MoserStageB (handleParams P) where
  Om := OmS2 P
  a := fun _ => xiPer P
  smooth_Om := contDiff_OmS2 P
  smooth_a := (contDiff_xiPer P).comp contDiff_snd
  skew := OmS2_skew P
  closed s _ := by
    rw [OmS2_eq]
    exact Forms.isClosed2_d1 (((contDiff_prim1 P 1).add ((contDiff_xiPer P).const_smul s)).of_le
      (by simp))
  dt s X v w := by
    have : HasDerivAt (fun r => OmS1 P 1 X v w + r * d1 (xiPer P) X v w)
        (d1 (xiPer P) X v w) s := by
      simpa using ((hasDerivAt_id s).mul_const (d1 (xiPer P) X v w)).const_add (OmS1 P 1 X v w)
    simpa [OmS2] using this
  nondeg s hs X hX := nondeg_of_strip P (fun T hT => OmS2_preserves P hT) (OmS2_skew P) s
    (fun Y hY hp v hv => secondStage_nondeg P hs hp v fun w => by
      rw [← OmS2_eq_secondStage P s hY]; exact hv w) X hX
  toric s _ X h1 _ := by
    have hx := d1_xiPer_toric P h1
    ext w
    change OmegaT P 1 X (Rrot X) w + d1 (etaPer P 1) X (Rrot X) w +
      s * d1 (xiPer P) X (Rrot X) w = -dpE X w
    rw [d1_etaPer_far P 1 h1, OmegaT_toric, hx]; simp
  toric_a s _ X _ _ := by
    change xiPer P X (Rrot X) = 0
    rw [xiPer_horiz, (Rrot_apply X).2.2.1, (Rrot_apply X).2.2.2]; ring
  fibre s _ X hX := xiPer_fibre P hX

/-! ### The concatenated Moser data and the handle Moser map -/

/-- The three stages. -/
def handleStages : Fin 3 → MoserStageB (handleParams P) := ![stage0 P, stage1 P, stage2 P]

lemma etaPer_zero : etaPer P 0 = 0 := by
  funext X; simp [etaPer, perJ, etaJ, eta_zero]

lemma handle_h01 : (handleStages P 0).Om 1 = (handleStages P 1).Om 0 := by
  funext X
  change OmS0 P 1 X = OmegaT P 1 X + d1 (etaPer P 0) X
  rw [etaPer_zero]
  ext v w
  simp [OmS0, Forms.d1_apply, Pi.zero_def]

lemma handle_h12 : (handleStages P 1).Om 1 = (handleStages P 2).Om 0 := by
  funext X
  change OmS1 P 1 X = OmS1 P 1 X + (0 : ℝ) • d1 (xiPer P) X
  ext v w; simp

/-- **The handle Moser data** (concatenation of the three stages with flat clocks). -/
def handleData : MoserBoxData (handleParams P) :=
  concat3B (handleStages P) (handle_h01 P) (handle_h12 P)

lemma handleStages_pres (T : DeckCore) (hT : IsDeck T) (i : Fin 3) :
    T.Preserves (handleStages P i).Om (handleStages P i).a := by
  fin_cases i
  · exact OmS0_preserves P hT
  · exact OmS1_preserves P hT
  · exact OmS2_preserves P hT

/-- The deck generators `TuE`, `TvE` preserve the handle Moser data. -/
theorem handleData_pres (T : DeckCore) (hT : IsDeck T) :
    T.Preserves (handleData P).Om (handleData P).a :=
  preserves_concat T (handleStages_pres P T hT)

/-- The deck generators of the handle Moser data. -/
def handleGens : DeckGens (handleData P).Om (handleData P).a := gens (handleData_pres P)

/-- **The handle Moser map** `Φ` (global, explicit). -/
def handlePhi : E4 → E4 := PhiG (handleData P)

/-- **Its inverse** `Φ⁻¹`. -/
def handlePhiInv : E4 → E4 := PhiGInv (handleData P)

lemma handleData_Om_one : (handleData P).Om 1 = OmegaFinalPer P := by
  change moserPathB (handleStages P) 1 = _
  rw [moserPathB_one (handle_h01 P) (handle_h12 P)]; rfl

lemma handleData_Om_zero : (handleData P).Om 0 = Omega0loc := by
  change moserPathB (handleStages P) 0 = _
  rw [moserPathB_zero]
  funext X
  change OmegaT P 0 X = Omega0loc X
  ext v w; simp [OmegaT]

lemma OmegaT_zero : OmegaT P 0 = Omega0loc := by funext X; ext v w; simp [OmegaT]

/-- **The handle Moser map** (`prop:shd4-moser`, `lem:pre-moser`). `Φ = handlePhi P` and
`Φ⁻¹ = handlePhiInv P` are explicit `C^∞` maps of the cover `E4`, mutually inverse, with
* (a) `Φ^*Ω_final = Ω₀` on `{p ≤ h + δ_m}`, equivalently `(Φ⁻¹)^*Ω₀ = Ω_final` there
  (`Ω_final = OmegaFinalPer P`, `Ω₀ = OmegaT P 0 = Omega0loc`);
* (b) `Ω_final = OmegaFinal P` on the strip `{u₁ − 1 < u < 1 + u₀}`;
* (c) `Φ`, `Φ⁻¹` preserve `{p ≤ h}` and `{p < h}` (indeed every `{p ≤ c}`, `{p < c}`,
  `{p = c}`, `c > P_supp`);
* (d) `Φ`, `Φ⁻¹` fix every point of the three fibres (all lifts);
* (e) `Φ`, `Φ⁻¹` commute with the deck maps `TuE`, `TvE` everywhere. -/
theorem handleMoser :
    ContDiff ℝ ∞ (handlePhi P) ∧ ContDiff ℝ ∞ (handlePhiInv P) ∧
    (∀ X, handlePhiInv P (handlePhi P X) = X) ∧ (∀ X, handlePhi P (handlePhiInv P X) = X) ∧
    (∀ X, pE X ≤ P.h + deltam P → ∀ v w,
      OmegaFinalPer P (handlePhi P X) (fderiv ℝ (handlePhi P) X v)
        (fderiv ℝ (handlePhi P) X w) = Omega0loc X v w) ∧
    (∀ X, pE X ≤ P.h + deltam P →
      pull2 (handlePhiInv P) (OmegaT P 0) X = OmegaFinalPer P X) ∧
    (∀ X, X ∈ stripU → OmegaFinalPer P X = OmegaFinal P X) ∧
    (∀ c, Psupp P < c → ∀ X,
      (pE (handlePhi P X) ≤ c ↔ pE X ≤ c) ∧ (pE (handlePhi P X) < c ↔ pE X < c) ∧
      (pE (handlePhiInv P X) ≤ c ↔ pE X ≤ c) ∧ (pE (handlePhiInv P X) < c ↔ pE X < c)) ∧
    (∀ X ∈ fibreSetH, handlePhi P X = X ∧ handlePhiInv P X = X) ∧
    (∀ X, handlePhi P (TuE X) = TuE (handlePhi P X) ∧
      handlePhi P (TvE X) = TvE (handlePhi P X) ∧
      handlePhiInv P (TuE X) = TuE (handlePhiInv P X) ∧
      handlePhiInv P (TvE X) = TvE (handlePhiInv P X)) := by
  have H := handle_moser_global (handleData P) (handleGens P)
  obtain ⟨hs, hsi, hl, hr, hpb, hlev, hfix, hdeck⟩ := H
  have hpb' : ∀ X, pE X ≤ P.h + deltam P → ∀ v w,
      OmegaFinalPer P (handlePhi P X) (fderiv ℝ (handlePhi P) X v)
        (fderiv ℝ (handlePhi P) X w) = Omega0loc X v w := fun X hX v w => by
    have := hpb X hX v w
    rwa [handleData_Om_one, handleData_Om_zero] at this
  refine ⟨hs, hsi, hl, hr, hpb', fun X hX => ?_, fun X hX => OmegaFinalPer_eq P hX,
    fun c hc X => ⟨(hlev c hc X).1, (hlev c hc X).2.1, (hlev c hc X).2.2.2.1,
      (hlev c hc X).2.2.2.2.1⟩, hfix, fun X => ⟨(hdeck deckU (handleData_pres P _ (Or.inl rfl)) X).1,
      (hdeck deckV (handleData_pres P _ (Or.inr rfl)) X).1,
      (hdeck deckU (handleData_pres P _ (Or.inl rfl)) X).2,
      (hdeck deckV (handleData_pres P _ (Or.inr rfl)) X).2⟩⟩
  -- the inverse pullback
  set x := handlePhiInv P X
  have hc : Psupp P < P.h + deltam P := by linarith [Psupp_lt_h P, deltam_pos P]
  have hx : pE x ≤ P.h + deltam P := ((hlev _ hc X).2.2.2.1).mpr hX
  have hX' : handlePhi P x = X := hr X
  have hchain : ∀ v, fderiv ℝ (handlePhi P) x (fderiv ℝ (handlePhiInv P) X v) = v := by
    intro v
    have h := ((hs.differentiable (by simp) x).hasFDerivAt.comp X
      (hsi.differentiable (by simp) X).hasFDerivAt)
    have he : (PhiG (handleData P) ∘ PhiGInv (handleData P)) = id := funext hr
    rw [he] at h
    have := congrArg (fun L : E4 →L[ℝ] E4 => L v) (h.unique (hasFDerivAt_id X))
    simp only [comp_apply, id_apply] at this
    exact this
  ext v w
  rw [Forms.pull2_apply, OmegaT_zero, ← hpb' x hx, hchain, hchain, hX']

end SymplecticPacking.Handle.Cubic
