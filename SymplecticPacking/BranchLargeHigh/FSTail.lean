import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus

/-!
# Explicit Fubini–Study tail bound for the diagonal quadric curve

`Γ = locus a ⊂ CP^{m+1}` (affine part `w_j² = t² − a_j`), normalised FS form `curveFSForm a (1/π)`
(total area `2^m`, `compact_area_le_degree`). The compact exhaustion piece
`projectionDomain a R = {|t| ≤ R}` at the explicit radius `R = exhaustionRadius a ℓ` misses an
FS area of at most `2^m (m+2)/R²` (`exhaustion_area_defect_le`).

This is the quantitative replacement of the OpenAI library's `tendsto_normalized_exhaustion_area`
needed to make the truncation level of the toric models explicit (`Two.mixedLevel`).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Set Function MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics

section pointwise

/-- The Fubini–Study form on a complex line `(v, Jv)` is at most `c|v|²/(1+|z|²)`. -/
theorem affineFSForm_J_le {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : 0 ≤ c)
    (z v : PlanePhase ι) :
    affineFSForm c z v (phaseJ v) ≤ c * phaseSq v / (1 + phaseSq z) := by
  rw [affineFSForm_apply, phaseArea_J_right, phaseArea_J_right, phaseDot_J_right]
  have hd := fs_den_pos z
  have h1 : 0 ≤ c / (1 + phaseSq z) ^ 2 *
      (phaseDot z v * phaseDot z v - phaseArea z v * (-phaseArea z v)) := by
    apply mul_nonneg (div_nonneg hc (sq_nonneg _))
    nlinarith [sq_nonneg (phaseDot z v), sq_nonneg (phaseArea z v)]
  have h2 : c / (1 + phaseSq z) * phaseDot v v = c * phaseSq v / (1 + phaseSq z) := by
    rw [show phaseDot v v = phaseSq v from rfl]; ring
  linarith

/-- `|affinePhase w|² = |w₀|² + Σ |w_j|²`. -/
theorem phaseSq_affinePhase {m : ℕ} (w : Affine m) :
    phaseSq (affinePhase m w) = ‖w.1‖ ^ 2 + ∑ j, ‖w.2 j‖ ^ 2 := by
  have hc : ∀ z : ℂ, z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [phaseSq, phaseDot_apply, Fintype.sum_option, affinePhase_none, affinePhase_some, hc]

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

/-- The curl of the regular FS primitive in the infinity chart is the FS form on the complex
tangent line of the curve. -/
theorem planarCurl_infinityRegularPrimitive (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y ∈ infinityRegion a) :
    planarCurl (infinityRegularPrimitive a ε c) y =
      affineFSForm c (affinePhase m (infinityRegularPoint a ε (Complex.equivRealProdCLM.symm y)))
        (affinePhase m (fderiv ℂ (infinityRegularPoint a ε) (Complex.equivRealProdCLM.symm y) 1))
        (phaseJ (affinePhase m
          (fderiv ℂ (infinityRegularPoint a ε) (Complex.equivRealProdCLM.symm y) 1))) := by
  have hφ := infinityRegularPhase_contDiffAt a ε hy
  have hext := staticPullbackOneForm_exterior (α := affineFSPrimitive c)
    (affineFSPrimitive_smooth (ι := Option (Fin m)) c).contDiffAt hφ
  have hf := realPhaseDerivative_fderiv
    ((infinityRegularPoint_contDiffAt a ε hy).differentiableAt (by simp))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  change fderiv ℝ (infinityRegularPhase a ε) y = _ at hf
  have hc : planarCurl (infinityRegularPrimitive a ε c) y =
      euclideanExteriorOneForm (infinityRegularPrimitive a ε c) y (1, 0) (0, 1) := by
    simp [planarCurl, euclideanExteriorOneForm]
  rw [hc]
  change euclideanExteriorOneForm
    (staticPullbackOneForm (affineFSPrimitive c) (infinityRegularPhase a ε)) y (1, 0) (0, 1) = _
  rw [hext, ContinuousLinearMap.bilinearComp_apply, hf, realPhaseDerivative_I,
    realPhaseDerivative_one]
  simp only [euclideanExteriorOneForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply]
  exact affineFSPrimitive_exterior c _ _ _

/-- Differentiating `v_j² = 1 − a_j s²`: `v_j' v_j = −a_j s`. -/
theorem infinityRoot_deriv_mul {s : ℂ} (hs : s ∈ infinityRegion a) (j : Fin m) :
    fderiv ℂ (infinityRoot a ε) s 1 j * infinityRoot a ε s j = -(a j * s) := by
  have hd := ((infinityRoot_contDiffAt a ε hs).differentiableAt (by simp)).hasFDerivAt
  have hj : HasDerivAt (fun t => infinityRoot a ε t j) (fderiv ℂ (infinityRoot a ε) s 1 j) s := by
    have := (hasFDerivAt_pi'.mp hd j).hasDerivAt
    simpa using this
  have h2 : HasDerivAt (fun t => infinityRoot a ε t j ^ 2)
      ((2 : ℕ) * infinityRoot a ε s j ^ (2 - 1) * fderiv ℂ (infinityRoot a ε) s 1 j) s :=
    hj.pow 2
  have heq : (fun t => infinityRoot a ε t j ^ 2) = fun t => 1 - a j * t ^ 2 :=
    funext fun t => infinityRoot_sq a ε t j
  have h3 : HasDerivAt (fun t : ℂ => 1 - a j * t ^ 2) (-(a j * ((2 : ℕ) * s ^ (2 - 1)))) s :=
    ((hasDerivAt_pow 2 s).const_mul (a j)).const_sub 1
  rw [heq] at h2
  have hu := h2.unique h3
  push_cast at hu
  linear_combination hu / 2

/-- Pointwise bound for the FS density in the infinity chart on a small disc. -/
theorem planarCurl_infinityRegularPrimitive_le {c R0 : ℝ} (hc : 0 ≤ c) {y : Plane}
    (hy : radiusSq y ≤ R0) (hA : ∀ j, ‖a j‖ * R0 ≤ 3 / 16) (hB : ∀ j, ‖a j‖ ^ 2 * R0 ≤ 3 / 2) :
    planarCurl (infinityRegularPrimitive a ε c) y ≤
      c * (1 + 2 * m) / (1 + 3 * m / 4) := by
  set s := Complex.equivRealProdCLM.symm y with hsdef
  have hns : ‖s‖ ^ 2 ≤ R0 := by
    rw [Complex.sq_norm, hsdef, radiusSq_complex]; exact hy
  have hsmall : ∀ j, ‖a j‖ * ‖s‖ ^ 2 ≤ 3 / 16 := fun j =>
    (mul_le_mul_of_nonneg_left hns (norm_nonneg _)).trans (hA j)
  have hreg : s ∈ infinityRegion a := by
    intro j
    have h1 : ‖a j * s ^ 2‖ ≤ 3 / 16 := by rw [norm_mul, norm_pow]; exact hsmall j
    have h2 := Complex.re_le_norm (a j * s ^ 2)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hroot : ∀ j, 3 / 4 ≤ ‖infinityRoot a ε s j‖ ^ 2 := by
    intro j
    have he : ‖infinityRoot a ε s j‖ ^ 2 = ‖1 - a j * s ^ 2‖ := by
      rw [← norm_pow, infinityRoot_sq]
    have h1 : ‖a j * s ^ 2‖ ≤ 3 / 16 := by rw [norm_mul, norm_pow]; exact hsmall j
    have h2 := norm_sub_norm_le (1 : ℂ) (a j * s ^ 2)
    rw [norm_one] at h2
    rw [he]; linarith
  have hder : ∀ j, ‖fderiv ℂ (infinityRoot a ε) s 1 j‖ ^ 2 ≤ 2 := by
    intro j
    have hm := congrArg (fun z : ℂ => ‖z‖ ^ 2) (infinityRoot_deriv_mul a ε hreg j)
    simp only [norm_mul, norm_neg, mul_pow] at hm
    have hB' : ‖a j‖ ^ 2 * ‖s‖ ^ 2 ≤ 3 / 2 :=
      (mul_le_mul_of_nonneg_left hns (sq_nonneg _)).trans (hB j)
    have hr := hroot j
    nlinarith [sq_nonneg ‖fderiv ℂ (infinityRoot a ε) s 1 j‖]
  rw [planarCurl_infinityRegularPrimitive a ε c (hsdef ▸ hreg)]
  refine (affineFSForm_J_le hc _ _).trans ?_
  rw [phaseSq_affinePhase, phaseSq_affinePhase, infinityRegularPoint_fderiv a ε hreg]
  simp only [infinityRegularPoint, norm_one, one_pow]
  have hV : 1 + ∑ j, ‖fderiv ℂ (infinityRoot a ε) s 1 j‖ ^ 2 ≤ 1 + 2 * m := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hder j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hZ : 1 + 3 * (m : ℝ) / 4 ≤ 1 + (‖s‖ ^ 2 + ∑ j, ‖infinityRoot a ε s j‖ ^ 2) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hroot j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    nlinarith [sq_nonneg ‖s‖]
  have hpos : (0 : ℝ) < 1 + 3 * m / 4 := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact div_le_div₀ (by positivity) hV hpos hZ

end pointwise

section
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]
local instance fsTailSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

/-- **Explicit FS tail bound.** The normalised FS area missed by `{|t| ≤ R}`,
`R = exhaustionRadius a ℓ = 2 + Σ‖a_j‖ + ℓ`, is at most `2^m (m+2)/R²`.

Over `{|t| > R}` there are no branch points
(`‖a_j‖ < R²`), so `Γ` is `2^m` disjoint sheets, each a graph over the punctured disc
`{0 < |s| < 1/R}`, `s = 1/t`, with homogeneous lift `F(s) = (s, 1, v_1, …, v_m)`,
`v_j² = 1 − a_j s²`. The normalised FS density is `π⁻¹ |F ∧ F'|²/|F|⁴ ≤ π⁻¹ |F'|²/|F|²`, with
`|F|² ≥ 1` and `|F'|² = 1 + Σ |a_j|²|s|²/|v_j|² ≤ 1 + 2 Σ|a_j|²/R² ≤ 3`
(since `|v_j|² ≥ 1 − |a_j|/R² ≥ 1/2` and `Σ|a_j| < R`). Each sheet thus carries area
`≤ 3/R²`, and `3 ≤ m + 2` for `m ≥ 1` (for `m = 0` the bound is `1/R²`). The proof combines
the pointwise bound `planarCurl_infinityRegularPrimitive_le` on the disc `{|s|² ≤ 1/R²}` with
the cutoff mass formula `curveEndCutoff_surface_mass`. -/
theorem exhaustion_area_defect_le (ℓ : ℕ) :
    (2 : ℝ) ^ m - compactSurfaceFormIntegral (projectionDomain_compact a (exhaustionRadius a ℓ))
        (curveFSForm a (1 / Real.pi)) ≤
      (2 : ℝ) ^ m * (m + 2) / exhaustionRadius a ℓ ^ 2 := by
  classical
  set R := exhaustionRadius a ℓ with hRdef
  have hS : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hR2 : 2 + ∑ j, ‖a j‖ ≤ R := by
    rw [hRdef, exhaustionRadius]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hRpos : 0 < R := by linarith
  have haj : ∀ j, ‖a j‖ ≤ R - 2 := fun j => by
    have := Finset.single_le_sum (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
    linarith
  set r0 : ℝ := 1 / R ^ 2 with hr0def
  set R0 : ℝ := 3 / (2 * R ^ 2) with hR0def
  have hR2pos : 0 < R ^ 2 := by positivity
  have hr0 : 0 < r0 := by positivity
  have hR0pos : 0 < R0 := by positivity
  have hr0R0 : r0 < R0 := by
    rw [hr0def, hR0def, div_lt_div_iff₀ hR2pos (by positivity)]; nlinarith
  have hA : ∀ j, ‖a j‖ * R0 ≤ 3 / 16 := by
    intro j
    rw [hR0def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [haj j, norm_nonneg (a j), sq_nonneg (R - 4)]
  have hB : ∀ j, ‖a j‖ ^ 2 * R0 ≤ 3 / 2 := by
    intro j
    have h1 : ‖a j‖ ^ 2 ≤ R ^ 2 := by
      have := haj j
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    rw [hR0def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hreg : {s : ℂ | Complex.normSq s ≤ R0} ⊆ infinityRegion a := by
    intro s hs j
    have hs' : ‖s‖ ^ 2 ≤ R0 := by rw [Complex.sq_norm]; exact hs
    have h1 : ‖a j * s ^ 2‖ ≤ 3 / 16 := by
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_left hs' (norm_nonneg _)).trans (hA j)
    have h2 := Complex.re_le_norm (a j * s ^ 2)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  -- the cutoff
  obtain ⟨g, hg, hgc, hgs, hg1, hgb⟩ := exists_smooth_cutoff (E := ℝ)
    (isCompact_Icc : IsCompact (Icc (-r0) r0)) (isOpen_Ioo : IsOpen (Ioo (-R0) R0))
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have h1 : ∀ t ∈ Ioo (-r0) r0, g t = 1 := fun t ht =>
    hg1.self_of_nhdsSet t ⟨ht.1.le, ht.2.le⟩
  have h0 : tsupport g ⊆ Iic R0 := fun t ht => (hgs ht).2.le
  have hnear : g =ᶠ[nhds 0] fun _ => 1 :=
    hg1.filter_mono (nhds_le_nhdsSet (show (0 : ℝ) ∈ Icc (-r0) r0 from ⟨by linarith, by linarith⟩))
  have hκc : HasCompactSupport (curveEndCutoff a g) := curveEndCutoff_compact a hnear
  have hsupp : tsupport (curveEndCutoff a g) ⊆ projectionDomain a R := by
    apply closure_minimal _ (projectionDomain_closed a R)
    intro x hx
    by_contra hn
    apply hx
    have hlt : R < ‖x.val.1‖ := by
      simp only [projectionDomain, Set.mem_setOf_eq, not_le] at hn; exact hn
    have ht0 : x.val.1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hlt; linarith
    have hn2 : R ^ 2 < Complex.normSq x.val.1 := by
      rw [← Complex.sq_norm]; exact pow_lt_pow_left₀ hlt hRpos.le (by norm_num)
    have hinv : Complex.normSq (x.val.1)⁻¹ ∈ Ioo (-r0) r0 := by
      rw [Complex.normSq_inv]
      have hp : 0 < Complex.normSq x.val.1 := by linarith
      constructor
      · have := inv_pos.mpr hp; linarith
      · rw [hr0def, one_div]; exact inv_strictAnti₀ hR2pos hn2
    unfold curveEndCutoff inverseComplementCutoff curveProjection
    rw [if_neg ht0]
    show 1 - g (Complex.normSq (x.val.1)⁻¹) = 0
    rw [h1 _ hinv, sub_self]
  have hc : (0 : ℝ) < 1 / Real.pi := one_div_pos.mpr Real.pi_pos
  have hmass_le := surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions a)
    (projectionDomain_compact a R) hκc hsupp (curveEndCutoff_smooth a hg hgc)
    (fun x => (curveEndCutoff_range a hgb x).2) (curveFSForm_smooth a _) (curveFSForm_skew a _)
    (fun b y hy => (curveFSForm_positive a hc b hy).le)
  choose β hβ hβc he using fun ε : Fin m → Bool =>
    exists_infinityRegularPrimitive_extension a hreg ε (1 / Real.pi)
  have hmass := curveEndCutoff_surface_mass a hg hgc hr0 hreg h1 h0 hκc (1 / Real.pi) β hβ he
  -- the residue integrals
  set K : ℝ := 1 / Real.pi * (1 + 2 * m) / (1 + 3 * m / 4) with hKdef
  have hK : 0 ≤ K := by positivity
  set D : Set Plane := {z | radiusSq z ≤ R0} with hDdef
  have hDvol : volume.real D = R0 * Real.pi := by
    have hpre : Complex.measurableEquivRealProd.symm ⁻¹' Metric.closedBall (0 : ℂ) (Real.sqrt R0)
        = D := by
      ext z
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hDdef,
        Set.mem_setOf_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [Real.le_sqrt (norm_nonneg _) hR0pos.le, Complex.sq_norm, Complex.normSq_apply]
      simp only [radiusSq]
      ring_nf
    have hv := (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage
      (s := Metric.closedBall (0 : ℂ) (Real.sqrt R0)) measurableSet_closedBall.nullMeasurableSet
    rw [hpre, Complex.volume_closedBall] at hv
    rw [Measure.real, hv, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal
      (Real.sqrt_nonneg _), Real.sq_sqrt hR0pos.le]
    simp
  have hint : ∀ ε, ∫ z, g (radiusSq z) * planarCurl (β ε) z ≤ K * (R0 * Real.pi) := by
    intro ε
    have hpt : ∀ z, g (radiusSq z) * planarCurl (β ε) z ≤ D.indicator (fun _ => K) z := by
      intro z
      have hg0 := (hgb (radiusSq z)).1
      have hg1' := (hgb (radiusSq z)).2
      by_cases hz : radiusSq z ≤ R0
      · rw [Set.indicator_of_mem (show z ∈ D from hz)]
        have hcurl : planarCurl (β ε) z ≤ K := by
          rw [planarCurl_congr_of_eventuallyEq (regular_extension_germ a (he ε) hz), hKdef]
          exact planarCurl_infinityRegularPrimitive_le a ε hc.le hz hA hB
        calc g (radiusSq z) * planarCurl (β ε) z ≤ g (radiusSq z) * K :=
              mul_le_mul_of_nonneg_left hcurl hg0
          _ ≤ K := mul_le_of_le_one_left hK hg1'
      · rw [Set.indicator_of_notMem (show z ∉ D from hz)]
        have : g (radiusSq z) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hz (h0 h))
        rw [this, zero_mul]
    have hi1 : Integrable (fun z => g (radiusSq z) * planarCurl (β ε) z) :=
      ((hg.comp radiusSq_smooth).mul (planarCurl_contDiff (hβ ε))).continuous
        |>.integrable_of_hasCompactSupport (planarCurl_compact (hβc ε)).mul_left
    have hDm : MeasurableSet D :=
      measurableSet_le radiusSq_smooth.continuous.measurable measurable_const
    have hi2 : Integrable (D.indicator (fun _ : Plane => K)) := by
      apply (integrable_indicator_iff hDm).mpr
      have hsub : D ⊆ radialAnnulus 0 R0 := fun z hz => ⟨radiusSq_nonneg z, hz⟩
      exact integrableOn_const
        ((measure_mono hsub).trans_lt (radialAnnulus_compact 0 R0).measure_lt_top).ne
    calc ∫ z, g (radiusSq z) * planarCurl (β ε) z ≤ ∫ z, D.indicator (fun _ => K) z :=
          integral_mono hi1 hi2 hpt
      _ = K * (R0 * Real.pi) := by
          rw [integral_indicator_const _ hDm, hDvol, smul_eq_mul, mul_comm]
  have hsum : ∑ ε : Fin m → Bool, ∫ z, g (radiusSq z) * planarCurl (β ε) z ≤
      (2 : ℝ) ^ m * (K * (R0 * Real.pi)) := by
    refine (Finset.sum_le_sum fun ε _ => hint ε).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hfin : K * (R0 * Real.pi) ≤ (m + 2) / R ^ 2 := by
    have hpi := Real.pi_pos
    have hden : (0 : ℝ) < 1 + 3 * m / 4 := by positivity
    have e : K * (R0 * Real.pi) = 3 * (1 + 2 * m) / (2 * (1 + 3 * m / 4)) / R ^ 2 := by
      rw [hKdef, hR0def]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hR2pos.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((m : ℝ) - 1 / 3)]
  have htot : (2 : ℝ) ^ m * (1 / Real.pi) * Real.pi = 2 ^ m := by field_simp
  rw [htot] at hmass
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have := mul_le_mul_of_nonneg_left hfin h2m
  rw [mul_div_assoc]
  linarith

omit [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)] in
/-- `R = exhaustionRadius a ℓ ≥ ℓ + 2`, hence `R² ≥ ℓ + 2`. -/
theorem exhaustionRadius_sq_ge (ℓ : ℕ) : (ℓ : ℝ) + 2 ≤ exhaustionRadius a ℓ ^ 2 := by
  have hs : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (a j))
  have hR : (ℓ : ℝ) + 2 ≤ exhaustionRadius a ℓ := by unfold exhaustionRadius; linarith
  have h1 : (1 : ℝ) ≤ exhaustionRadius a ℓ := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  nlinarith

/-- The tail bound in terms of the level: area defect `≤ 2^m (m+2)/(ℓ+2)`. -/
theorem exhaustion_area_defect_le_level (ℓ : ℕ) :
    (2 : ℝ) ^ m - compactSurfaceFormIntegral (projectionDomain_compact a (exhaustionRadius a ℓ))
        (curveFSForm a (1 / Real.pi)) ≤
      (2 : ℝ) ^ m * (m + 2) / ((ℓ : ℝ) + 2) := by
  refine (exhaustion_area_defect_le a ℓ).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) (exhaustionRadius_sq_ge a ℓ)

end

end SymplecticPacking.BranchLargeHigh
