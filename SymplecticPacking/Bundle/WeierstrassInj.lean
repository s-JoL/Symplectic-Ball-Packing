import SymplecticPacking.Bundle.Hexagonal

/-!
# Injectivity of the Weierstrass map of the hexagonal lattice

Injectivity of the Weierstrass parametrization `z ↦ (℘ z, ℘' z)` of the hexagonal lattice.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Complex PeriodPair Filter Topology Set

/-- The complement of the hexagonal lattice is preconnected. -/
lemma hex_compl_isPreconnected : IsPreconnected ((hexPair.lattice : Set ℂ)ᶜ) := by
  have hc : (hexPair.lattice : Set ℂ).Countable := by
    have : Countable hexPair.lattice :=
      Countable.of_equiv (ℤ × ℤ) hexPair.latticeEquivProd.toEquiv.symm
    exact Set.countable_coe_iff.mp this
  exact (hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

lemma hex_isOpen_compl : IsOpen ((hexPair.lattice : Set ℂ)ᶜ) :=
  hexPair.isClosed_lattice.isOpen_compl

lemma wp_eq_except (z : ℂ) : ℘[hexPair] z = (hexPair.weierstrassPExcept 0) z + 1 / z ^ 2 := by
  have := hexPair.weierstrassPExcept_def (0 : hexPair.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero] at this
  rw [this]; simp

lemma dwp_eq_except (z : ℂ) : ℘'[hexPair] z = (hexPair.derivWeierstrassPExcept 0) z - 2 / z ^ 3 := by
  have := hexPair.derivWeierstrassPExcept_def (0 : hexPair.lattice) z
  simp only [ZeroMemClass.coe_zero, sub_zero] at this
  rw [this]; ring

lemma wpExcept_zero : (hexPair.weierstrassPExcept 0) 0 = 0 := by
  have := wp_eq_except 0
  rw [hexPair.weierstrassP_zero, zero_pow two_ne_zero, div_zero, add_zero] at this
  exact this.symm

/-- Eventually near `0`, lattice points are `0`. -/
lemma eventually_lattice_eq_zero : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ hexPair.lattice → y = 0 := by
  filter_upwards [hexPair.compl_lattice_sdiff_singleton_mem_nhds 0] with y hy hyL
  by_contra h; exact hy ⟨hyL, h⟩

lemma eventually_notMem_lattice : ∀ᶠ y in 𝓝[≠] (0 : ℂ), y ∉ hexPair.lattice := by
  filter_upwards [nhdsWithin_le_nhds eventually_lattice_eq_zero, self_mem_nhdsWithin]
    with y h1 h2 h3
  exact h2 (h1 h3)

/-- `℘'` is not identically zero off the lattice. -/
lemma exists_dwp_ne_zero : ∃ z, z ∉ hexPair.lattice ∧ ℘'[hexPair] z ≠ 0 := by
  have hk : ContinuousAt (hexPair.derivWeierstrassPExcept 0) 0 :=
    (hexPair.analyticAt_derivWeierstrassPExcept 0).continuousAt
  have hk0 : (hexPair.derivWeierstrassPExcept 0) 0 = 0 := hexPair.derivWeierstrassPExcept_zero_zero
  have h1 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖(hexPair.derivWeierstrassPExcept 0) y‖ < 1 := by
    exact hk.norm.eventually (eventually_lt_nhds (by simp [hk0]))
  have h2 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖y‖ < 1 := by
    exact (continuous_norm.tendsto (0 : ℂ)).eventually (eventually_lt_nhds (by simp))
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := ((h1.filter_mono nhdsWithin_le_nhds).and ((h2.filter_mono nhdsWithin_le_nhds).and
    (eventually_notMem_lattice.and self_mem_nhdsWithin))).exists
  refine ⟨z, hz3, ?_⟩
  rw [dwp_eq_except]
  intro h
  have hz0 : z ≠ 0 := hz4
  have hn : ‖(hexPair.derivWeierstrassPExcept 0) z‖ = ‖2 / z ^ 3‖ := by rw [sub_eq_zero.mp h]
  have : 1 < ‖2 / z ^ 3‖ := by
    rw [norm_div, norm_pow]
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have : ‖z‖ ^ 3 < 1 := pow_lt_one₀ hp.le hz2 (by norm_num)
    rw [lt_div_iff₀ (by positivity)]; simp; linarith
  linarith

lemma wp_analyticOnNhd : AnalyticOnNhd ℂ ℘[hexPair] (hexPair.lattice : Set ℂ)ᶜ :=
  hexPair.analyticOnNhd_weierstrassP

lemma dwp_analyticOnNhd : AnalyticOnNhd ℂ ℘'[hexPair] (hexPair.lattice : Set ℂ)ᶜ :=
  hexPair.analyticOnNhd_derivWeierstrassP

lemma dwp_half : ℘'[hexPair] (hexPair.ω₁ / 2) = 0 := by
  have h1 := hexPair.derivWeierstrassP_add_coe (-(hexPair.ω₁ / 2)) ⟨hexPair.ω₁, hexPair.ω₁_mem_lattice⟩
  have h2 : -(hexPair.ω₁ / 2) + ((⟨hexPair.ω₁, hexPair.ω₁_mem_lattice⟩ : hexPair.lattice) : ℂ)
      = hexPair.ω₁ / 2 := by
    show -(hexPair.ω₁ / 2) + hexPair.ω₁ = hexPair.ω₁ / 2
    ring
  rw [h2, hexPair.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2

lemma dwp_not_eventually_const {z₀ : ℂ} (hz₀ : z₀ ∉ hexPair.lattice) (c : ℂ) :
    ¬ (∀ᶠ z in 𝓝 z₀, ℘'[hexPair] z = c) := by
  intro h
  have hEq := dwp_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => c)
    analyticOnNhd_const hex_compl_isPreconnected hz₀ h
  have hc : c = 0 := by
    have := hEq (x := hexPair.ω₁ / 2) hexPair.ω₁_div_two_notMem_lattice
    simp only at this
    rw [dwp_half] at this
    exact this.symm
  obtain ⟨z, hz, hz'⟩ := exists_dwp_ne_zero
  have := hEq (x := z) hz
  simp only at this
  exact hz' (this.trans hc)

lemma wp_not_eventually_const {z₀ : ℂ} (hz₀ : z₀ ∉ hexPair.lattice) (c : ℂ) :
    ¬ (∀ᶠ z in 𝓝 z₀, ℘[hexPair] z = c) := by
  intro h
  have h' : deriv ℘[hexPair] =ᶠ[𝓝 z₀] deriv (fun _ => c) :=
    Filter.EventuallyEq.deriv (h : ℘[hexPair] =ᶠ[𝓝 z₀] fun _ => c)
  apply dwp_not_eventually_const hz₀ 0
  filter_upwards [h'] with z hz
  rw [← hexPair.deriv_weierstrassP]
  simpa using hz

lemma enat_add_one_eq_one {x : ℕ∞} (hx : x + 1 = 1) : x = 0 := by
  induction x using ENat.recTopCoe with
  | top => simp at hx
  | coe k => norm_cast at hx ⊢; omega

/-- **`g₃ ≠ 0` for the hexagonal lattice.** If `g₃ = 0` then `℘'² = 4℘³`; at the half period
`e = ω₁/2` both `℘` and `℘'` vanish, and comparing orders of vanishing (`2(n-1) = 3n`) gives a
contradiction. -/
theorem hex_g3_ne_zero : hexPair.g₃ ≠ 0 := by
  intro hg
  set e := hexPair.ω₁ / 2 with he_def
  have he : e ∉ hexPair.lattice := hexPair.ω₁_div_two_notMem_lattice
  have hrel : ∀ z ∉ hexPair.lattice, ℘'[hexPair] z ^ 2 = 4 * ℘[hexPair] z ^ 3 := fun z hz => by
    rw [hex_wp_eq z hz, hg, sub_zero]
  have hwe : ℘[hexPair] e = 0 := by
    have h := hrel e he
    rw [dwp_half] at h
    have h3 : ℘[hexPair] e ^ 3 = 0 := by linear_combination -h / 4
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3
  have hA : AnalyticAt ℂ ℘[hexPair] e := wp_analyticOnNhd e he
  have hA' : AnalyticAt ℂ ℘'[hexPair] e := dwp_analyticOnNhd e he
  have hN := hA.analyticOrderAt_deriv_add_one
  rw [hexPair.deriv_weierstrassP] at hN
  simp only [hwe, sub_zero] at hN
  have hfin : analyticOrderAt ℘[hexPair] e ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; intro h; exact wp_not_eventually_const he 0 h
  have hev : (℘'[hexPair] ^ 2) =ᶠ[𝓝 e] ((fun _ => (4 : ℂ)) * ℘[hexPair] ^ 3) := by
    filter_upwards [hex_isOpen_compl.mem_nhds he] with z hz
    simp [hrel z hz]
  have h2 := analyticOrderAt_congr hev
  rw [analyticOrderAt_pow hA', analyticOrderAt_mul analyticAt_const
    (hA.pow 3 : AnalyticAt ℂ (℘[hexPair] ^ 3) e), analyticOrderAt_pow hA,
    show analyticOrderAt (fun _ => (4 : ℂ)) e = 0 from
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num)), zero_add] at h2
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hN h2
  have hm : analyticOrderAt ℘'[hexPair] e ≠ ⊤ := by intro h; rw [h] at hN; simp at hN
  obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.mp hm
  rw [← hm'] at hN h2
  have hN' : m + 1 = n := by exact_mod_cast hN
  have h2' : 2 * m = 3 * n := by simp only [nsmul_eq_mul] at h2; exact_mod_cast h2
  omega

/-- At a zero of `℘'` (off the lattice), `℘''` does not vanish. -/
lemma deriv_dwp_ne_zero {z₀ : ℂ} (hz₀ : z₀ ∉ hexPair.lattice) (h0 : ℘'[hexPair] z₀ = 0) :
    deriv ℘'[hexPair] z₀ ≠ 0 := by
  set c := ℘[hexPair] z₀ with hc_def
  have hc3 : 4 * c ^ 3 = hexPair.g₃ := by
    have := hex_wp_eq z₀ hz₀; rw [h0] at this; linear_combination -this
  have hc : c ≠ 0 := by intro h; apply hex_g3_ne_zero; rw [← hc3, h]; ring
  have hA : AnalyticAt ℂ ℘[hexPair] z₀ := wp_analyticOnNhd z₀ hz₀
  have hA' : AnalyticAt ℂ ℘'[hexPair] z₀ := dwp_analyticOnNhd z₀ hz₀
  have hN := hA.analyticOrderAt_deriv_add_one
  rw [hexPair.deriv_weierstrassP] at hN
  have hM := hA'.analyticOrderAt_deriv_add_one
  simp only [h0, sub_zero] at hM
  set q : ℂ → ℂ := fun z => 4 * (℘[hexPair] z ^ 2 + c * ℘[hexPair] z + c ^ 2) with hq_def
  have hq : AnalyticAt ℂ q z₀ := by
    simp only [hq_def]
    exact analyticAt_const.mul (((hA.pow 2).add (analyticAt_const.mul hA)).add analyticAt_const)
  have hq0 : analyticOrderAt q z₀ = 0 := by
    refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
    simp only [hq_def, ← hc_def]
    have : (4 : ℂ) * (c ^ 2 + c * c + c ^ 2) = 12 * c ^ 2 := by ring
    rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
  have hsub : AnalyticAt ℂ (fun z => ℘[hexPair] z - c) z₀ := hA.sub analyticAt_const
  have hev : (℘'[hexPair] ^ 2) =ᶠ[𝓝 z₀] ((fun z => ℘[hexPair] z - c) * q) := by
    filter_upwards [hex_isOpen_compl.mem_nhds hz₀] with z hz
    simp only [Pi.pow_apply, Pi.mul_apply, hq_def]
    rw [hex_wp_eq z hz, ← hc3]; ring
  have h2 := analyticOrderAt_congr hev
  rw [analyticOrderAt_pow hA', analyticOrderAt_mul hsub hq, hq0, add_zero] at h2
  have hfin : analyticOrderAt (fun z => ℘[hexPair] z - c) z₀ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; intro h
    exact wp_not_eventually_const hz₀ c (h.mono fun z hz => sub_eq_zero.mp hz)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hN h2
  have hm : analyticOrderAt ℘'[hexPair] z₀ ≠ ⊤ := by intro h; rw [h] at hN; simp at hN
  obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.mp hm
  rw [← hm'] at hN h2 hM
  have hN' : m + 1 = n := by exact_mod_cast hN
  have h2' : 2 * m = n := by simp only [nsmul_eq_mul] at h2; exact_mod_cast h2
  have hm1 : m = 1 := by omega
  subst hm1
  have hz : analyticOrderAt (deriv ℘'[hexPair]) z₀ = 0 :=
    enat_add_one_eq_one (by simpa using hM)
  rcases analyticOrderAt_eq_zero.mp hz with h | h
  · exact absurd hA'.deriv h
  · exact h

/-- A holomorphic function with nonzero derivative is injective near the point. -/
lemma injOn_of_analyticAt {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (h : deriv f a ≠ 0) :
    ∃ V ∈ 𝓝 a, Set.InjOn f V := by
  have hs := hf.hasStrictDerivAt
  refine ⟨_, hs.eventually_left_inverse h, ?_⟩
  intro x hx y hy hxy
  simp only [mem_ofPred_eq] at hx hy
  rw [← hx, ← hy, hxy]

/-- Local injectivity of `z ↦ (℘ z, ℘' z)` off the lattice. -/
lemma Phi_locInj {z₀ : ℂ} (hz₀ : z₀ ∉ hexPair.lattice) :
    ∃ V ∈ 𝓝 z₀, ∀ z ∈ V, ∀ w ∈ V, ℘[hexPair] z = ℘[hexPair] w →
      ℘'[hexPair] z = ℘'[hexPair] w → z = w := by
  by_cases h0 : ℘'[hexPair] z₀ = 0
  · obtain ⟨V, hV, hinj⟩ :=
      injOn_of_analyticAt (dwp_analyticOnNhd z₀ hz₀) (deriv_dwp_ne_zero hz₀ h0)
    exact ⟨V, hV, fun z hz w hw _ h => hinj hz hw h⟩
  · obtain ⟨V, hV, hinj⟩ := injOn_of_analyticAt (wp_analyticOnNhd z₀ hz₀)
      (by rw [hexPair.deriv_weierstrassP]; exact h0)
    exact ⟨V, hV, fun z hz w hw h _ => hinj hz hw h⟩

/-- The local coordinate `℘/℘'` near the pole, written analytically. -/
def hexPsi (z : ℂ) : ℂ :=
  (z + z ^ 3 * hexPair.weierstrassPExcept 0 z) / (z ^ 3 * hexPair.derivWeierstrassPExcept 0 z - 2)

lemma hexPsi_eq {z : ℂ} (hz : z ≠ 0) : hexPsi z = ℘[hexPair] z / ℘'[hexPair] z := by
  rw [wp_eq_except, dwp_eq_except, hexPsi]
  have h3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  have e1 : hexPair.weierstrassPExcept 0 z + 1 / z ^ 2
      = (z + z ^ 3 * hexPair.weierstrassPExcept 0 z) / z ^ 3 := by
    field_simp; ring
  have e2 : hexPair.derivWeierstrassPExcept 0 z - 2 / z ^ 3
      = (z ^ 3 * hexPair.derivWeierstrassPExcept 0 z - 2) / z ^ 3 := by
    field_simp
  rw [e1, e2, div_div_div_cancel_right₀ h3]

lemma hexPsi_analyticAt : AnalyticAt ℂ hexPsi 0 := by
  have hh := hexPair.analyticAt_weierstrassPExcept 0
  have hk := hexPair.analyticAt_derivWeierstrassPExcept 0
  show AnalyticAt ℂ (fun z => (z + z ^ 3 * hexPair.weierstrassPExcept 0 z) /
    (z ^ 3 * hexPair.derivWeierstrassPExcept 0 z - 2)) 0
  apply AnalyticAt.div
  · exact analyticAt_id.add ((analyticAt_id.pow 3).mul hh)
  · exact ((analyticAt_id.pow 3).mul hk).sub analyticAt_const
  · simp

lemma hexPsi_hasDerivAt : HasDerivAt hexPsi (-1 / 2) 0 := by
  have hh := (hexPair.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  have hk := (hexPair.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hN := (hasDerivAt_id (0 : ℂ)).add ((hasDerivAt_pow 3 (0 : ℂ)).mul hh)
  have hD := ((hasDerivAt_pow 3 (0 : ℂ)).mul hk).sub_const 2
  have := hN.div hD (by simp)
  convert this using 1
  · funext z; simp [hexPsi]
  · simp; norm_num

/-- Local injectivity of `z ↦ (℘ z, ℘' z)` on a punctured neighbourhood of the pole `0`. -/
lemma Phi_locInj_zero : ∃ V ∈ 𝓝 (0 : ℂ), ∀ z ∈ V, ∀ w ∈ V, z ≠ 0 → w ≠ 0 →
    ℘[hexPair] z = ℘[hexPair] w → ℘'[hexPair] z = ℘'[hexPair] w → z = w := by
  obtain ⟨V, hV, hinj⟩ :=
    injOn_of_analyticAt hexPsi_analyticAt (by rw [hexPsi_hasDerivAt.deriv]; norm_num)
  refine ⟨V, hV, fun z hz w hw hz0 hw0 h1 h2 => hinj hz hw ?_⟩
  rw [hexPsi_eq hz0, hexPsi_eq hw0, h1, h2]

/-- `℘` blows up at the pole `0`. -/
lemma wp_large_near_zero (M : ℝ) : ∀ᶠ y in 𝓝[≠] (0 : ℂ), M < ‖℘[hexPair] y‖ := by
  have hh : ContinuousAt (hexPair.weierstrassPExcept 0) 0 :=
    (hexPair.analyticAt_weierstrassPExcept 0).continuousAt
  have h1 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖hexPair.weierstrassPExcept 0 y‖ < 1 :=
    hh.norm.eventually (eventually_lt_nhds (by simp))
  have h2 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖y‖ ^ 2 * (|M| + 1) < 1 := by
    have : ContinuousAt (fun y : ℂ => ‖y‖ ^ 2 * (|M| + 1)) 0 := by fun_prop
    exact this.eventually (eventually_lt_nhds (by simp))
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy1 hy2 hy3
  have hy0 : (y : ℂ) ≠ 0 := hy3
  rw [wp_eq_except]
  have hp : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hbig : |M| + 1 < ‖1 / y ^ 2‖ := by
    rw [norm_div, norm_one, norm_pow, lt_div_iff₀ (by positivity)]; linarith
  have htri := norm_sub_le (hexPair.weierstrassPExcept 0 y + 1 / y ^ 2)
    (hexPair.weierstrassPExcept 0 y)
  rw [add_sub_cancel_left] at htri
  linarith [le_abs_self M]

/-- `℘` blows up at every lattice point. -/
lemma wp_large_near_lattice {l : ℂ} (hl : l ∈ hexPair.lattice) (M : ℝ) :
    ∀ᶠ y in 𝓝 l, y ∉ hexPair.lattice → M < ‖℘[hexPair] y‖ := by
  have ht : Tendsto (fun y => y - l) (𝓝 l) (𝓝 0) := by
    have : Tendsto (fun y : ℂ => y - l) (𝓝 l) (𝓝 (l - l)) := tendsto_id.sub tendsto_const_nhds
    rwa [sub_self] at this
  have := ht.eventually (eventually_nhdsWithin_iff.mp (wp_large_near_zero M))
  filter_upwards [this] with y hy hyL
  have hne : y - l ≠ 0 := fun h => hyL (by rw [sub_eq_zero.mp h]; exact hl)
  have h := hy hne
  rwa [show ℘[hexPair] (y - l) = ℘[hexPair] y from hexPair.weierstrassP_sub_coe y ⟨l, hl⟩] at h

/-- A radius such that every point is congruent to a point of the closed ball. -/
def hexR : ℝ := ∑ i, ‖hexPair.basis i‖

lemma exists_reduce (w : ℂ) : ∃ l ∈ hexPair.lattice, w - l ∈ Metric.closedBall (0 : ℂ) hexR := by
  refine ⟨ZSpan.floor hexPair.basis w, ?_, ?_⟩
  · have := (ZSpan.floor hexPair.basis w).2
    rw [hexPair.lattice_eq_span_range_basis]; exact this
  · have := ZSpan.norm_fract_le hexPair.basis w
    rw [ZSpan.fract_apply] at this
    simpa [hexR] using this

/-- `z` has a partner: a point `w`, not congruent to `z`, with the same `(℘, ℘')`. -/
def HasPartner (z : ℂ) : Prop :=
  ∃ w, w ∉ hexPair.lattice ∧ w - z ∉ hexPair.lattice ∧
    ℘[hexPair] w = ℘[hexPair] z ∧ ℘'[hexPair] w = ℘'[hexPair] z

lemma hasPartner_bounded {z : ℂ} (h : HasPartner z) :
    ∃ w ∈ Metric.closedBall (0 : ℂ) hexR, w ∉ hexPair.lattice ∧ w - z ∉ hexPair.lattice ∧
      ℘[hexPair] w = ℘[hexPair] z ∧ ℘'[hexPair] w = ℘'[hexPair] z := by
  obtain ⟨w, h1, h2, h3, h4⟩ := h
  obtain ⟨l, hl, hK⟩ := exists_reduce w
  refine ⟨w - l, hK, ?_, ?_, ?_, ?_⟩
  · intro h; apply h1
    have := hexPair.lattice.add_mem h hl
    simpa using this
  · intro h; apply h2
    have := hexPair.lattice.add_mem h hl
    have e : w - l - z + l = w - z := by ring
    rwa [e] at this
  · rw [hexPair.weierstrassP_sub_coe w ⟨l, hl⟩]; exact h3
  · rw [hexPair.derivWeierstrassP_sub_coe w ⟨l, hl⟩]; exact h4

lemma exists_local_partner {F : ℂ → ℂ} {z₀ w₀ : ℂ} (hFz : ContinuousAt F z₀)
    (hF : AnalyticAt ℂ F w₀) (hd : deriv F w₀ ≠ 0) (hFe : F w₀ = F z₀) :
    ∃ W : ℂ → ℂ, Tendsto W (𝓝 z₀) (𝓝 w₀) ∧ ∀ᶠ z in 𝓝 z₀, F (W z) = F z := by
  have hs := hF.hasStrictDerivAt
  set g := hs.localInverse F _ w₀ hd
  have hgc : ContinuousAt g (F w₀) := (HasStrictDerivAt.hasDerivAt (hs.to_localInverse hd)).continuousAt
  have hgw : g (F w₀) = w₀ := (hs.eventually_left_inverse hd).self_of_nhds
  have tF : Tendsto F (𝓝 z₀) (𝓝 (F w₀)) := by rw [hFe]; exact hFz.tendsto
  refine ⟨fun z => g (F z), ?_, tF.eventually (hs.eventually_right_inverse hd)⟩
  have := hgc.tendsto.comp tF
  rwa [hgw] at this

lemma eventually_eq_of_sq {l : Filter ℂ} {a b : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (ha : Tendsto a l (𝓝 c)) (hb : Tendsto b l (𝓝 c)) (h : ∀ᶠ z in l, a z ^ 2 = b z ^ 2) :
    ∀ᶠ z in l, a z = b z := by
  have ht : Tendsto (fun z => a z + b z) l (𝓝 (c + c)) := ha.add hb
  have hne : ∀ᶠ z in l, a z + b z ≠ 0 :=
    ht.eventually_ne (by intro h; apply hc; linear_combination h / 2)
  filter_upwards [h, hne] with z h1 h2
  have : (a z - b z) * (a z + b z) = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)

lemma eventually_eq_of_cube {l : Filter ℂ} {a b : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (ha : Tendsto a l (𝓝 c)) (hb : Tendsto b l (𝓝 c)) (h : ∀ᶠ z in l, a z ^ 3 = b z ^ 3) :
    ∀ᶠ z in l, a z = b z := by
  have ht : Tendsto (fun z => a z ^ 2 + a z * b z + b z ^ 2) l (𝓝 (c ^ 2 + c * c + c ^ 2)) :=
    ((ha.pow 2).add (ha.mul hb)).add (hb.pow 2)
  have hne : ∀ᶠ z in l, a z ^ 2 + a z * b z + b z ^ 2 ≠ 0 := by
    refine ht.eventually_ne ?_
    have : c ^ 2 + c * c + c ^ 2 = 3 * c ^ 2 := by ring
    rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
  filter_upwards [h, hne] with z h1 h2
  have : (a z - b z) * (a z ^ 2 + a z * b z + b z ^ 2) = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)

lemma wp_continuousAt {x : ℂ} (hx : x ∉ hexPair.lattice) : ContinuousAt ℘[hexPair] x :=
  (wp_analyticOnNhd x hx).continuousAt

lemma dwp_continuousAt {x : ℂ} (hx : x ∉ hexPair.lattice) : ContinuousAt ℘'[hexPair] x :=
  (dwp_analyticOnNhd x hx).continuousAt

lemma eventually_notMem {x : ℂ} (hx : x ∉ hexPair.lattice) :
    ∀ᶠ z in 𝓝 x, z ∉ hexPair.lattice :=
  hex_isOpen_compl.mem_nhds hx

/-- (a) Having a partner is an open condition (off the lattice). -/
lemma hasPartner_eventually {z₀ : ℂ} (hz₀ : z₀ ∉ hexPair.lattice) (h : HasPartner z₀) :
    ∀ᶠ z in 𝓝 z₀, HasPartner z := by
  obtain ⟨w₀, hw₀, hd₀, h1, h2⟩ := h
  have hU := eventually_notMem hz₀
  obtain ⟨W, hW, hWe⟩ : ∃ W : ℂ → ℂ, Tendsto W (𝓝 z₀) (𝓝 w₀) ∧
      ∀ᶠ z in 𝓝 z₀, ℘[hexPair] (W z) = ℘[hexPair] z ∧ ℘'[hexPair] (W z) = ℘'[hexPair] z := by
    by_cases h0 : ℘'[hexPair] w₀ = 0
    · obtain ⟨W, hW, hF⟩ := exists_local_partner (dwp_continuousAt hz₀)
        (dwp_analyticOnNhd _ hw₀) (deriv_dwp_ne_zero hw₀ h0) h2
      refine ⟨W, hW, ?_⟩
      have hc : ℘[hexPair] w₀ ≠ 0 := by
        intro hc; apply hex_g3_ne_zero
        have := hex_wp_eq w₀ hw₀; rw [h0, hc] at this; linear_combination this
      have hcube : ∀ᶠ z in 𝓝 z₀, ℘[hexPair] (W z) ^ 3 = ℘[hexPair] z ^ 3 := by
        filter_upwards [hF, hU, hW.eventually (eventually_notMem hw₀)] with z hz1 hz2 hz3
        have e1 := hex_wp_eq _ hz3
        have e2 := hex_wp_eq _ hz2
        rw [hz1] at e1
        linear_combination (e2 - e1) / 4
      have ha : Tendsto (fun z => ℘[hexPair] (W z)) (𝓝 z₀) (𝓝 (℘[hexPair] w₀)) :=
        (wp_continuousAt hw₀).tendsto.comp hW
      have hb : Tendsto ℘[hexPair] (𝓝 z₀) (𝓝 (℘[hexPair] w₀)) := by
        rw [h1]; exact (wp_continuousAt hz₀).tendsto
      filter_upwards [eventually_eq_of_cube hc ha hb hcube, hF] with z e1 e2
      exact ⟨e1, e2⟩
    · obtain ⟨W, hW, hF⟩ := exists_local_partner (wp_continuousAt hz₀)
        (wp_analyticOnNhd _ hw₀) (by rw [hexPair.deriv_weierstrassP]; exact h0) h1
      refine ⟨W, hW, ?_⟩
      have hsq : ∀ᶠ z in 𝓝 z₀, ℘'[hexPair] (W z) ^ 2 = ℘'[hexPair] z ^ 2 := by
        filter_upwards [hF, hU, hW.eventually (eventually_notMem hw₀)] with z hz1 hz2 hz3
        rw [hex_wp_eq _ hz3, hex_wp_eq _ hz2, hz1]
      have ha : Tendsto (fun z => ℘'[hexPair] (W z)) (𝓝 z₀) (𝓝 (℘'[hexPair] w₀)) :=
        (dwp_continuousAt hw₀).tendsto.comp hW
      have hb : Tendsto ℘'[hexPair] (𝓝 z₀) (𝓝 (℘'[hexPair] w₀)) := by
        rw [h2]; exact (dwp_continuousAt hz₀).tendsto
      filter_upwards [eventually_eq_of_sq h0 ha hb hsq, hF] with z e1 e2
      exact ⟨e2, e1⟩
  have hWd : Tendsto (fun z => W z - z) (𝓝 z₀) (𝓝 (w₀ - z₀)) := hW.sub tendsto_id
  filter_upwards [hW.eventually (eventually_notMem hw₀), hWd.eventually (eventually_notMem hd₀),
    hWe] with z e1 e2 e3
  exact ⟨W z, e1, e2, e3.1, e3.2⟩

/-- (b) Having a partner is a closed condition (off the lattice). -/
lemma hasPartner_of_mem_closure {z : ℂ} (hz : z ∉ hexPair.lattice)
    (hcl : z ∈ closure {x | HasPartner x}) : HasPartner z := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hcl
  choose p hpK hpL hpd hp1 hp2 using fun n => hasPartner_bounded (hu n)
  obtain ⟨w, -, φ, hφ, hpt⟩ := (isCompact_closedBall (0 : ℂ) hexR).tendsto_subseq hpK
  have hut' : Tendsto (u ∘ φ) atTop (𝓝 z) := hut.comp hφ.tendsto_atTop
  have hPz : Tendsto (fun n => ℘[hexPair] (p (φ n))) atTop (𝓝 (℘[hexPair] z)) := by
    have := (wp_continuousAt hz).tendsto.comp hut'
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]; exact (hp1 (φ n)).symm
  have hP'z : Tendsto (fun n => ℘'[hexPair] (p (φ n))) atTop (𝓝 (℘'[hexPair] z)) := by
    have := (dwp_continuousAt hz).tendsto.comp hut'
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]; exact (hp2 (φ n)).symm
  by_cases hw : w ∈ hexPair.lattice
  · exfalso
    have hbig := hpt.eventually (wp_large_near_lattice hw (‖℘[hexPair] z‖ + 1))
    have hsmall := hPz.norm.eventually (eventually_lt_nhds (lt_add_one ‖℘[hexPair] z‖))
    obtain ⟨n, hn1, hn2⟩ := (hbig.and hsmall).exists
    have := hn1 (hpL _)
    simp only [Function.comp_apply] at this
    linarith
  · have hP1 : ℘[hexPair] w = ℘[hexPair] z :=
      tendsto_nhds_unique ((wp_continuousAt hw).tendsto.comp hpt) hPz
    have hP2 : ℘'[hexPair] w = ℘'[hexPair] z :=
      tendsto_nhds_unique ((dwp_continuousAt hw).tendsto.comp hpt) hP'z
    by_cases hwz : w - z ∈ hexPair.lattice
    · exfalso
      obtain ⟨V, hV, hinj⟩ := Phi_locInj hz
      have hy : Tendsto (fun n => p (φ n) - (w - z)) atTop (𝓝 z) := by
        have := hpt.sub_const (w - z)
        simpa using this
      obtain ⟨n, hn1, hn2⟩ := ((hy.eventually hV).and (hut'.eventually hV)).exists
      have heq := hinj _ hn1 _ hn2
        (by rw [hexPair.weierstrassP_sub_coe _ ⟨w - z, hwz⟩]; exact hp1 _)
        (by rw [hexPair.derivWeierstrassP_sub_coe _ ⟨w - z, hwz⟩]; exact hp2 _)
      apply hpd (φ n)
      simp only [Function.comp_apply] at heq
      rw [← heq]
      simpa using hwz
    · exact ⟨w, hw, hwz, hP1, hP2⟩

/-- (c) Points close to the pole have no partner. -/
lemma eventually_not_hasPartner_zero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ¬ HasPartner z := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨u, hut, hu⟩ := Filter.exists_seq_forall_of_frequently hcon
  have hu' : ∀ n, HasPartner (u n) := fun n => not_not.mp (hu n)
  choose p hpK hpL hpd hp1 hp2 using fun n => hasPartner_bounded (hu' n)
  obtain ⟨w, -, φ, hφ, hpt⟩ := (isCompact_closedBall (0 : ℂ) hexR).tendsto_subseq hpK
  have hut' : Tendsto (u ∘ φ) atTop (𝓝[≠] 0) := hut.comp hφ.tendsto_atTop
  by_cases hw : w ∈ hexPair.lattice
  · obtain ⟨V, hV, hinj⟩ := Phi_locInj_zero
    have hy : Tendsto (fun n => p (φ n) - w) atTop (𝓝 0) := by
      have := hpt.sub_const w
      simpa using this
    obtain ⟨n, hn1, hn2, hn3⟩ := ((hy.eventually hV).and
      (((hut'.mono_right nhdsWithin_le_nhds).eventually hV).and
        (hut'.eventually self_mem_nhdsWithin))).exists
    have hy0 : p (φ n) - w ≠ 0 := fun h => hpL _ (by rw [sub_eq_zero.mp h]; exact hw)
    have heq := hinj _ hn1 _ hn2 hy0 hn3
      (by rw [hexPair.weierstrassP_sub_coe _ ⟨w, hw⟩]; exact hp1 _)
      (by rw [hexPair.derivWeierstrassP_sub_coe _ ⟨w, hw⟩]; exact hp2 _)
    apply hpd (φ n)
    simp only [Function.comp_apply] at heq
    rw [← heq]
    simpa using hw
  · have hPw : Tendsto (fun n => ℘[hexPair] (p (φ n))) atTop (𝓝 (℘[hexPair] w)) :=
      (wp_continuousAt hw).tendsto.comp hpt
    have hsmall := hPw.norm.eventually (eventually_lt_nhds (lt_add_one ‖℘[hexPair] w‖))
    have hbig := hut'.eventually (wp_large_near_zero (‖℘[hexPair] w‖ + 1))
    obtain ⟨n, hn1, hn2⟩ := (hsmall.and hbig).exists
    simp only [Function.comp_apply] at hn1 hn2
    rw [hp1] at hn1
    linarith

/-- No point off the lattice has a partner. -/
theorem not_hasPartner {z : ℂ} (hz : z ∉ hexPair.lattice) : ¬ HasPartner z := by
  intro hzP
  set B : Set ℂ := {x | x ∉ hexPair.lattice ∧ HasPartner x} with hB
  have hBopen : IsOpen B := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    filter_upwards [eventually_notMem hx.1, hasPartner_eventually hx.1 hx.2] with y h1 h2
    exact ⟨h1, h2⟩
  have hcover : (hexPair.lattice : Set ℂ)ᶜ ⊆ B ∪ (closure B)ᶜ := by
    intro x hx
    by_cases hc : x ∈ closure B
    · left
      exact ⟨hx, hasPartner_of_mem_closure hx (closure_mono (fun y hy => hy.2) hc)⟩
    · right; exact hc
  obtain ⟨x₀, hx₀L, hx₀B⟩ : ∃ x₀, x₀ ∉ hexPair.lattice ∧ x₀ ∉ closure B := by
    have h := eventually_not_hasPartner_zero.and eventually_notMem_lattice
    obtain ⟨O, hOo, hO0, hOs⟩ := mem_nhdsWithin.mp h
    have hO' : O ∩ {0}ᶜ ∈ 𝓝[≠] (0 : ℂ) := inter_mem (mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds hO0)) self_mem_nhdsWithin
    obtain ⟨x₀, hx₀⟩ := (Filter.nonempty_of_mem hO')
    refine ⟨x₀, (hOs hx₀).2, ?_⟩
    rw [mem_closure_iff]
    push Not
    refine ⟨O ∩ {0}ᶜ, hOo.inter isOpen_compl_singleton, hx₀, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    exact (hOs hy1).1 hy2.2
  obtain ⟨y, -, hy1, hy2⟩ := hex_compl_isPreconnected B (closure B)ᶜ hBopen
    isClosed_closure.isOpen_compl hcover ⟨z, hz, hz, hzP⟩ ⟨x₀, hx₀L, hx₀B⟩
  exact hy2 (subset_closure hy1)

/-- **Injectivity of the Weierstrass parametrization** of the hexagonal lattice:
`(℘ z, ℘' z) = (℘ w, ℘' w)` forces `z ≡ w` modulo the lattice. -/
theorem wp_injective (z w : ℂ) (hz : z ∉ hexPair.lattice) (hw : w ∉ hexPair.lattice)
    (h1 : ℘[hexPair] z = ℘[hexPair] w) (h2 : ℘'[hexPair] z = ℘'[hexPair] w) :
    z - w ∈ hexPair.lattice := by
  by_contra h
  exact not_hasPartner hw ⟨z, hz, h, h1, h2⟩

end SymplecticPacking.Bundle
