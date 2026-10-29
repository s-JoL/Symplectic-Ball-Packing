import Mathlib
import SymplecticPacking.Qhat.Density

/-!
# Joint smoothness of the density family maps

`sec:pll-data`, `lem:pln-energy`: joint smoothness of `(s, z) ↦ f_s(z)` on `[0, 1] × ℂ`.

The parametric normalisation lemma `Inner.normalize_param_smooth` needs a density family that is
positive for `s` in an *open* interval. `J_s = X_s' Y_s'` is positive for `s ∈ [0, 1]` but in
general not for `s < 0` (`X̃'` is unbounded), so we argue locally: for every `R` we build an
auxiliary family `Ĵ_s = X̂_s' Ŷ_s'` (with `X̂_s(u) = X_s(c(u)) + a₀(u - c(u))`, `c` a smooth clamp
equal to the identity on `[-R', R']`) which is positive for `s ∈ (-δ, 1 + δ)` and agrees with
`J_s` on `{|Re w|, |Im w| ≤ R}` for `s ∈ [0, 1]`; the normalisations only see the density on the
disk of radius `√E_s(π|z|²)` (`fs_smooth_ext`). Choices here are made inside proofs only.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### Locality of the normalisations -/

section locality

variable {J J' : ℝ → ℂ → ℝ} {s R : ℝ}

lemma Jcirc_congr_ball (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') {w : ℂ} (hw : ‖w‖ ≤ R) :
    Inner.Jcirc J s w = Inner.Jcirc J' s w := by
  unfold Inner.Jcirc
  congr 1
  exact intervalIntegral.integral_congr fun φ _ => h _ (by rw [Inner.norm_Rot]; exact hw)

lemma Bfun_congr_ball (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') {w : ℂ} (hw : ‖w‖ ≤ R) :
    Inner.Bfun J s w = Inner.Bfun J' s w := by
  unfold Inner.Bfun
  congr 1
  exact intervalIntegral.integral_congr fun φ _ => by
    rw [h _ (by rw [Inner.norm_Rot]; exact hw)]

lemma Jbar_congr_ball (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') (hR : 0 ≤ R) {t : ℝ} (ht : t ≤ R ^ 2) :
    Inner.Jbar J s t = Inner.Jbar J' s t := by
  unfold Inner.Jbar
  have hsq : √t ≤ R := by
    calc √t ≤ √(R ^ 2) := Real.sqrt_le_sqrt ht
      _ = R := Real.sqrt_sq hR
  congr 1
  exact intervalIntegral.integral_congr fun φ _ => h _ (by
    rw [Inner.norm_Rot, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact hsq)

lemma Trot_congr_ball (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') {w : ℂ} (hw : ‖w‖ ≤ R) :
    Inner.Trot J s w = Inner.Trot J' s w := by
  rw [Inner.Trot_eq, Inner.Trot_eq, Bfun_congr_ball h hw, Jcirc_congr_ball h hw]

lemma mem_uIcc_le {E t : ℝ} (ht : t ∈ uIcc 0 E) : t ≤ max 0 E := by
  rcases mem_uIcc.mp ht with h | h
  · exact h.2.trans (le_max_right _ _)
  · exact h.2.trans (le_max_left _ _)

lemma Acal_congr_ball (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') (hR : 0 ≤ R) {E : ℝ} (hE : E ≤ R ^ 2) :
    Inner.Acal J s E = Inner.Acal J' s E := by
  unfold Inner.Acal
  congr 1
  exact intervalIntegral.integral_congr fun t ht =>
    Jbar_congr_ball h hR ((mem_uIcc_le ht).trans (max_le (sq_nonneg R) hE))

lemma TrotInv_congr_ball {s₁ s₂ j ρ : ℝ} (hJ' : Inner.FlatDensity J' s₁ s₂ j ρ) (hs : s ∈ Ioo s₁ s₂)
    (hinj : Function.Injective (Inner.Trot J s)) (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w')
    {y : ℂ} (hy : ‖y‖ ≤ R) : Inner.TrotInv J s y = Inner.TrotInv J' s y := by
  have h1 := Inner.Trot_TrotInv hJ' hs y
  have h2 := Inner.norm_TrotInv hJ' hs y
  apply Inner.TrotInv_eq_of hinj
  rw [Trot_congr_ball h (h2.symm ▸ hy : ‖Inner.TrotInv J' s y‖ ≤ R), h1]

lemma Einv_congr_ball {j ρ s₁ s₂ j' ρ' : ℝ}
    (hJ : Inner.FlatDensity (fun _ => J s) (-1) 1 j ρ)
    (hJ' : Inner.FlatDensity J' s₁ s₂ j' ρ') (hs : s ∈ Ioo s₁ s₂)
    (h : ∀ w', ‖w'‖ ≤ R → J s w' = J' s w') (hR : 0 ≤ R) {I : ℝ}
    (hE : Inner.Einv J s I ≤ R ^ 2) : Inner.Einv J s I = Inner.Einv J' s I := by
  have h1 : Inner.Acal J s (Inner.Einv J s I) = I := Inner.Acal_Einv hJ zero_mem_Ioo I
  have h2 : Inner.Acal J' s (Inner.Einv J s I) = I := by rw [← Acal_congr_ball h hR hE]; exact h1
  conv_rhs => rw [← h2]
  rw [Inner.Einv_Acal hJ' hs]

end locality

/-! ### A one-dimensional extension -/

lemma abs_le_of_mem_uIcc_zero {u t : ℝ} (ht : t ∈ uIcc 0 u) : |t| ≤ |u| := by
  rcases mem_uIcc.mp ht with h | h
  · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
  · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]

/-- A smooth family `X̂_s` of real-line maps with `X̂_s' ≥ μ > 0` for `s ∈ (-δ, 1 + δ)`,
`X̂_s' = a` on `|u| ≤ ε`, and `X̂_s = (1 - s) a u + s G(u)` on `|u| ≤ R`. -/
theorem ext1D {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hpos : ∀ u, 0 < deriv G u) {a ε : ℝ}
    (ha : 0 < a) (hlin : ∀ u, |u| ≤ ε → deriv G u = a) (R : ℝ) :
    ∃ δ > 0, ∃ μ > 0, ∃ X dX : ℝ → ℝ → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => X p.1 p.2) ∧ ContDiff ℝ ∞ (fun p : ℝ × ℝ => dX p.1 p.2) ∧
      (∀ s u, HasDerivAt (X s) (dX s u) u) ∧
      (∀ s ∈ Ioo (-δ) (1 + δ), ∀ u, μ ≤ dX s u) ∧
      (∀ s u, |u| ≤ ε → dX s u = a) ∧
      (∀ s u, |u| ≤ R → X s u = (1 - s) * a * u + s * G u ∧
        dX s u = (1 - s) * a + s * deriv G u) := by
  set R' := max (max R ε) 0 + 1 with hR'def
  have hR'0 : 0 < R' := by have := le_max_right (max R ε) 0; linarith
  have hRR' : R ≤ R' := by
    have := le_max_left (max R ε) 0; have := le_max_left R ε; linarith
  have hεR' : ε ≤ R' := by
    have := le_max_left (max R ε) 0; have := le_max_right R ε; linarith
  let φ : ContDiffBump (0 : ℝ) := ⟨R', R' + 1, hR'0, by linarith⟩
  have hφc : ContDiff ℝ ∞ (fun x : ℝ => φ x) := φ.contDiff
  have hφcont : Continuous (fun x : ℝ => φ x) := hφc.continuous
  have hφ1 : ∀ u, |u| ≤ R' → φ u = 1 := fun u hu =>
    φ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hu)
  have hφ0 : ∀ u, R' + 1 ≤ |u| → φ u = 0 := fun u hu =>
    φ.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu)
  have hφnn : ∀ u, 0 ≤ φ u := fun u => φ.nonneg
  have hφle : ∀ u, φ u ≤ 1 := fun u => φ.le_one
  -- the clamp `c(u) = ∫₀ᵘ φ`
  set c : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, φ t with hcdef
  have hc_der : ∀ u, HasDerivAt c (φ u) u := fun u =>
    (hφcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hc_smooth : ContDiff ℝ ∞ c := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun u => (hc_der u).differentiableAt, ?_⟩
    have : deriv c = fun x => φ x := funext fun u => (hc_der u).deriv
    rw [this]; exact hφc
  have hc_id : ∀ u, |u| ≤ R' → c u = u := by
    intro u hu
    simp only [hcdef]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
      (fun t ht => hφ1 t ((abs_le_of_mem_uIcc_zero ht).trans hu))]
    simp
  have hc_small : ∀ u, |u| ≤ R' + 1 → |c u| ≤ R' + 1 := by
    intro u hu
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u) (C := 1)
      (f := fun t => φ t) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφnn t)]; exact hφle t)
    simp only [Real.norm_eq_abs, sub_zero, one_mul] at this
    exact this.trans hu
  have hc_bd : ∀ u, |c u| ≤ R' + 1 := by
    intro u
    by_cases hu : |u| ≤ R' + 1
    · exact hc_small u hu
    push Not at hu
    set b : ℝ := if 0 < u then R' + 1 else -(R' + 1)
    have hb : |b| = R' + 1 := by
      simp only [b]; split_ifs <;> (try rw [abs_neg]) <;> exact abs_of_pos (by linarith)
    have hzero : ∫ t in b..u, φ t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => hφ0 t ?_)]
      · simp
      · rcases lt_or_ge 0 u with h0 | h0
        · have hb' : b = R' + 1 := ite_eq_left_iff.mpr (fun h => absurd h0 h)
          rw [hb'] at ht
          rw [abs_of_pos h0] at hu
          rcases mem_uIcc.mp ht with h | h
          · rw [abs_of_pos (by linarith [h.1])]; exact h.1
          · linarith [h.1, h.2]
        · have hb' : b = -(R' + 1) := ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr h0))
          rw [hb'] at ht
          rw [abs_of_nonpos h0] at hu
          rcases mem_uIcc.mp ht with h | h
          · linarith [h.1, h.2]
          · rw [abs_of_neg (by linarith [h.2])]; linarith [h.2]
    have hsplit : c u = c b + ∫ t in b..u, φ t := by
      simp only [hcdef]
      rw [intervalIntegral.integral_add_adjacent_intervals (hφcont.intervalIntegrable _ _)
        (hφcont.intervalIntegrable _ _)]
    rw [hsplit, hzero, add_zero]
    exact hc_small b hb.le
  -- bounds of `G'` on `K = [-(R'+1), R'+1]`
  have hG' : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2
  have hG'c : Continuous (deriv G) := hG'.continuous
  have hKne : (Icc (-(R' + 1)) (R' + 1)).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨xm, -, hxm⟩ := isCompact_Icc.exists_isMinOn hKne hG'c.continuousOn
  obtain ⟨xM, -, hxM⟩ := isCompact_Icc.exists_isMaxOn hKne hG'c.continuousOn
  set m := deriv G xm
  set M := deriv G xM
  have hm : 0 < m := hpos xm
  have hM : 0 < M := hpos xM
  have hcK : ∀ u, c u ∈ Icc (-(R' + 1)) (R' + 1) := fun u => abs_le.mp (hc_bd u)
  have hGm : ∀ u, m ≤ deriv G (c u) := fun u => hxm (hcK u)
  have hGM : ∀ u, deriv G (c u) ≤ M := fun u => hxM (hcK u)
  set δ := min (a / (2 * M)) (m / (2 * a))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  set μ := min a m / 2
  have hμ : 0 < μ := by positivity
  refine ⟨δ, hδ, μ, hμ, fun s u => (1 - s) * a * c u + s * G (c u) + a * (u - c u),
    fun s u => ((1 - s) * a + s * deriv G (c u)) * φ u + a * (1 - φ u), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => c p.2) := hc_smooth.comp contDiff_snd
    exact ((((contDiff_const.sub contDiff_fst).mul contDiff_const).mul h1).add
      (contDiff_fst.mul (hG.comp h1))).add (contDiff_const.mul (contDiff_snd.sub h1))
  · have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => c p.2) := hc_smooth.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.2) := hφc.comp contDiff_snd
    exact ((((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul (hG'.comp h1))).mul h2).add (contDiff_const.mul (contDiff_const.sub h2))
  · intro s u
    beta_reduce
    have hGd : HasDerivAt G (deriv G (c u)) (c u) :=
      (hG.differentiable (by simp) (c u)).hasDerivAt
    have h1 := (hc_der u).const_mul ((1 - s) * a)
    have h2 := (hGd.comp u (hc_der u)).const_mul s
    have h3 := ((hasDerivAt_id u).sub (hc_der u)).const_mul a
    have h4 := (h1.add h2).add h3
    rw [show ((1 - s) * a + s * deriv G (c u)) * φ u + a * (1 - φ u) =
      (1 - s) * a * φ u + s * (deriv G (c u) * φ u) + a * (1 - φ u) by ring]
    exact h4
  · intro s hs u
    have hφu := hφnn u; have hφu' := hφle u
    have hlow : μ ≤ (1 - s) * a + s * deriv G (c u) := by
      have hGmu := hGm u; have hGMu := hGM u
      have hμa : μ ≤ a / 2 := by
        have := min_le_left a m; simp only [μ]; linarith
      have hμm : μ ≤ m / 2 := by
        have := min_le_right a m; simp only [μ]; linarith
      rcases lt_or_ge s 0 with h0 | h0
      · have hs' : -s < a / (2 * M) := by have := hs.1; have := min_le_left (a / (2 * M)) (m / (2 * a)); linarith
        have : -s * M ≤ a / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hs'; linarith
        nlinarith
      rcases le_or_gt s 1 with h1 | h1
      · have hmin : min a m ≤ a := min_le_left _ _
        have hmin' : min a m ≤ m := min_le_right _ _
        have hμmin : μ ≤ min a m := by have := lt_min ha hm; simp only [μ]; linarith
        nlinarith
      · have hs' : s - 1 < m / (2 * a) := by have := hs.2; have := min_le_right (a / (2 * M)) (m / (2 * a)); linarith
        have : (s - 1) * a ≤ m / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hs'; linarith
        nlinarith
    have hμa : μ ≤ a := by have := min_le_left a m; simp only [μ]; linarith
    nlinarith
  · intro s u hu
    beta_reduce
    have h1 := hc_id u (hu.trans hεR')
    rw [h1, hφ1 u (hu.trans hεR'), hlin u hu]; ring
  · intro s u hu
    beta_reduce
    have h1 := hc_id u (hu.trans hRR')
    rw [h1, hφ1 u (hu.trans hRR')]
    exact ⟨by ring, by ring⟩

/-! ### The auxiliary density family -/

/-- For every `R ≥ 0` there is an auxiliary flat density family `Ĵ`, positive on
`(-δ, 1 + δ)`, with a product map `F̂_s` of Jacobian `Ĵ_s`, agreeing with `J_s, F_s` on
`{|Re w|, |Im w| ≤ R}` for every `s`. -/
theorem density_ext (R : ℝ) :
    ∃ δ > 0, ∃ (Jh : ℝ → ℂ → ℝ) (Fh : ℝ → ℂ → ℂ),
      Inner.FlatDensity Jh (-δ) (1 + δ) (j0 P) (Inner.rhoT P) ∧
      ContDiff ℝ ∞ (fun p : ℝ × ℂ => Fh p.1 p.2) ∧
      (∀ s w, LinearMap.det (fderiv ℝ (Fh s) w : ℂ →ₗ[ℝ] ℂ) = Jh s w) ∧
      (∀ s (w : ℂ), |w.re| ≤ R → |w.im| ≤ R → Jh s w = Js P s w ∧ Fh s w = Fs P s w) := by
  obtain ⟨δ1, hδ1, μ1, hμ1, X, dX, hX, hdX, hXd, hXlb, hXflat, hXag⟩ :=
    ext1D (Inner.Xtilde_smooth P) (Inner.Xtilde_deriv_pos P) (a0_pos P)
      (fun u hu => Inner.Xtilde_deriv_closed P hu) R
  obtain ⟨δ2, hδ2, μ2, hμ2, Y, dY, hY, hdY, hYd, hYlb, hYflat, hYag⟩ :=
    ext1D (Inner.Ytilde_smooth P) (Inner.Ytilde_deriv_pos P) (b0_pos P)
      (fun v hv => Inner.Ytilde_deriv_closed P hv) R
  set δ := min δ1 δ2
  have hδ : 0 < δ := lt_min hδ1 hδ2
  have hIoo1 : Ioo (-δ) (1 + δ) ⊆ Ioo (-δ1) (1 + δ1) := fun s hs =>
    ⟨by have := min_le_left δ1 δ2; linarith [hs.1], by have := min_le_left δ1 δ2; linarith [hs.2]⟩
  have hIoo2 : Ioo (-δ) (1 + δ) ⊆ Ioo (-δ2) (1 + δ2) := fun s hs =>
    ⟨by have := min_le_right δ1 δ2; linarith [hs.1], by have := min_le_right δ1 δ2; linarith [hs.2]⟩
  set Jh : ℝ → ℂ → ℝ := fun s w => dX s w.re * dY s w.im
  set Fh : ℝ → ℂ → ℂ := fun s w => (X s w.re : ℂ) + (Y s w.im : ℂ) * I
  have hJh : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Jh p.1 p.2) :=
    (hdX.comp (contDiff_fst.prodMk (reCLM.contDiff.comp contDiff_snd))).mul
      (hdY.comp (contDiff_fst.prodMk (imCLM.contDiff.comp contDiff_snd)))
  have hlb : ∀ s ∈ Ioo (-δ) (1 + δ), ∀ w, μ1 * μ2 ≤ Jh s w := fun s hs w =>
    mul_le_mul (hXlb s (hIoo1 hs) _) (hYlb s (hIoo2 hs) _) hμ2.le
      (hμ1.le.trans (hXlb s (hIoo1 hs) _))
  refine ⟨δ, hδ, Jh, Fh, ?_, ?_, ?_, ?_⟩
  · refine
      { smooth := hJh
        pos := fun s hs w => lt_of_lt_of_le (mul_pos hμ1 hμ2) (hlb s hs w)
        flat := fun s _ w hw => ?_
        j_pos := j0_pos P
        ρ₀_pos := Inner.rhoT_pos P
        tendsto := fun s hs => ?_ }
    · have hu : |w.re| ≤ Inner.uEps P := (abs_re_le_norm w).trans (hw.trans (min_le_left _ _))
      have hv : |w.im| ≤ Inner.vEps P := (abs_im_le_norm w).trans (hw.trans (min_le_right _ _))
      simp only [Jh, hXflat s _ hu, hYflat s _ hv, j0, Inner.j0]
    · have hc : Continuous (Jh s) := (Inner.contDiff_slice hJh s).continuous
      have hlin : Tendsto (fun E : ℝ => π * (μ1 * μ2) * E) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      refine tendsto_atTop_mono' _ ?_ hlin
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with E hE
      exact Acal_ge_of hc (hlb s hs) hE
  · exact (ofRealCLM.contDiff.comp
      (hX.comp (contDiff_fst.prodMk (reCLM.contDiff.comp contDiff_snd)))).add
      ((ofRealCLM.contDiff.comp
        (hY.comp (contDiff_fst.prodMk (imCLM.contDiff.comp contDiff_snd)))).mul contDiff_const)
  · intro s w
    exact det_prod_map (hXd s w.re) (hYd s w.im)
  · intro s w hu hv
    obtain ⟨hX1, hX2⟩ := hXag s w.re hu
    obtain ⟨hY1, hY2⟩ := hYag s w.im hv
    refine ⟨?_, ?_⟩
    · simp only [Jh, hX2, hY2, Js]
    · simp only [Fh, hX1, hY1, Fs, Xs, Ys]

/-! ### Joint smoothness (`lem:pln-energy`) -/

/-- `E_s(I) ≤ (I + d₀)/κ` for `s ∈ [0, 1]`, `I ≥ 0`. -/
theorem Es_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {I : ℝ} (hI : 0 ≤ I) :
    Es P s I ≤ (I + P.d0) / kappa P := by
  have hJ := JsC_flat P hs
  have hE0 : 0 ≤ Es P s I := Inner.Einv_nonneg hJ zero_mem_Ioo hI
  have h1 : As P s (Es P s I) = I := Inner.Acal_Einv hJ zero_mem_Ioo I
  have h2 := As_ge P hs hE0
  rw [le_div_iff₀ (kappa_pos P)]
  have := h2.2.trans h2.1
  rw [h1] at this
  linarith

/-- **`lem:pln-energy`, joint smoothness (local extension form).** For every `R₀` there is `δ > 0`
and a map `g`, `C^∞` on `(-δ, 1 + δ) × ℂ`, with `g(s, z) = f_s(z)` for `s ∈ [0, 1]`,
`|z| ≤ R₀`. -/
theorem fs_smooth_ext (R0 : ℝ) :
    ∃ δ > 0, ∃ g : ℝ × ℂ → ℂ, ContDiffOn ℝ ∞ g (Ioo (-δ) (1 + δ) ×ˢ univ) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ ≤ R0 → g (s, z) = fs P s z := by
  set R := √((π * R0 ^ 2 + P.d0) / kappa P)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = (π * R0 ^ 2 + P.d0) / kappa P :=
    Real.sq_sqrt (div_nonneg (by have := P.d0_nonneg; positivity) (kappa_pos P).le)
  obtain ⟨δ, hδ, Jh, Fh, hJh, hFh, hdet, hag⟩ := density_ext P R
  refine ⟨δ, hδ, fun p => Fh p.1 (Inner.TrotInv Jh p.1 (Inner.Darea Jh p.1 p.2)),
    (Inner.normalize_param_smooth hJh (hFh.contDiffOn) (fun s _ w => hdet s w)).1, ?_⟩
  intro s hs z hz
  have hs' : s ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJ := JsC_flat P hs
  have hloc : ∀ w' : ℂ, ‖w'‖ ≤ R → Js P s w' = Jh s w' := fun w' hw' =>
    ((hag s w' ((abs_re_le_norm w').trans hw') ((abs_im_le_norm w').trans hw')).1).symm
  have hE : Es P s (π * ‖z‖ ^ 2) ≤ R ^ 2 := by
    rw [hRsq]
    refine (Es_le P hs (by positivity)).trans ?_
    apply div_le_div_of_nonneg_right _ (kappa_pos P).le
    have : ‖z‖ ^ 2 ≤ R0 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    nlinarith [Real.pi_pos]
  have hEq : Es P s (π * ‖z‖ ^ 2) = Inner.Einv Jh s (π * ‖z‖ ^ 2) :=
    Einv_congr_ball (J := Js P) hJ hJh hs' hloc hR hE
  have hD : Inner.Darea (Js P) s z = Inner.Darea Jh s z := by
    unfold Inner.Darea; rw [← hEq]
  set y := Inner.Darea (Js P) s z
  have hy : ‖y‖ ≤ R := by
    have h1 : ‖y‖ ^ 2 ≤ R ^ 2 := by
      have := Inner.norm_Darea_sq hJ zero_mem_Ioo z
      rw [show ‖y‖ ^ 2 = Es P s (π * ‖z‖ ^ 2) from this]; exact hE
    exact (pow_le_pow_iff_left₀ (norm_nonneg y) hR (by norm_num)).mp h1
  have hT : Inner.TrotInv (Js P) s y = Inner.TrotInv Jh s y :=
    TrotInv_congr_ball hJh hs' (hJ.bij zero_mem_Ioo).1 hloc hy
  have hw : ‖Inner.TrotInv Jh s y‖ ≤ R := by rw [Inner.norm_TrotInv hJh hs' y]; exact hy
  have hFw := (hag s (Inner.TrotInv Jh s y) ((abs_re_le_norm _).trans hw)
    ((abs_im_le_norm _).trans hw)).2
  have hgoal : fs P s z = Fs P s (Inner.TrotInv (Js P) s y) := rfl
  show Fh s (Inner.TrotInv Jh s (Inner.Darea Jh s z)) = _
  rw [hgoal, ← hD, hT]
  exact hFw

/-- **`lem:pln-energy`.** `(s, z) ↦ f_s(z)` is `C^∞` on `[0, 1] × ℂ` (in the sense of
`ContDiffOn` on this closed set; locally it is the restriction of the `C^∞` maps of
`fs_smooth_ext`). -/
theorem fs_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fs P p.1 p.2) (Icc 0 1 ×ˢ univ) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  obtain ⟨δ, hδ, g, hg, hgeq⟩ := fs_smooth_ext P (‖x.2‖ + 1)
  refine ⟨univ ×ˢ Metric.ball 0 (‖x.2‖ + 1), isOpen_univ.prod Metric.isOpen_ball,
    ⟨mem_univ _, by simp⟩, ?_⟩
  refine (hg.mono ?_).congr ?_
  · rintro p ⟨⟨hp1, -⟩, -⟩
    exact ⟨⟨by linarith [hp1.1], by linarith [hp1.2]⟩, mem_univ _⟩
  · rintro p ⟨⟨hp1, -⟩, ⟨-, hp2⟩⟩
    rw [Metric.mem_ball, dist_zero_right] at hp2
    exact (hgeq p.1 hp1 p.2 hp2.le).symm

end SymplecticPacking.Qhat
