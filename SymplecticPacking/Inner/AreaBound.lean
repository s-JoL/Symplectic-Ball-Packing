import Mathlib
import SymplecticPacking.Inner.Morse

/-!
# The area identity and the area lower bound

`sec:pll`, `lem:pll-morse-density` (the area identity) and `lem:pll-area` (the area lower bound)
for the Morse density `J = X̃'(u) Ỹ'(v)`.

`𝓐_J(E) = π ∫₀^E J̄` (`Acal`) is identified, via polar coordinates, with the integral of `J`
over the disk `u² + v² ≤ E` (`Acal_eq_disk`) and, via Fubini, with the slice integral
`∫_{-√E}^{√E} Ỹ'(v) (X̃(√(E-v²)) - X̃(-√(E-v²))) dv` (`Acal_eq_slices`). The lower bound
`𝓐_J(E) ≥ E - d₀` (`Acal_ge`) follows from the slice formula by the substitution `y = Ỹ(v)`.
-/

noncomputable section

namespace SymplecticPacking.Inner

open Filter Topology Set MeasureTheory Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### Sublevel sets of `R̃` and `Ṽ` -/

/-- `{R̃ ≤ s} = [X̃(-√s), X̃(√s)]`. -/
theorem Rtilde_le_iff {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Rtilde P x ≤ s ↔ Xtilde P (-√s) ≤ x ∧ x ≤ Xtilde P √s := by
  rw [← SigmaR_sq, Real.sq_le hs,
    ← (Xtilde_strictMono P).le_iff_le (a := -√s) (b := SigmaR P x),
    ← (Xtilde_strictMono P).le_iff_le (a := SigmaR P x) (b := √s), Xtilde_SigmaR]

/-- `{Ṽ ≤ s} = [Ỹ(-√s), Ỹ(√s)]`. -/
theorem Vtilde_le_iff {s : ℝ} (hs : 0 ≤ s) (y : ℝ) :
    Vtilde P y ≤ s ↔ Ytilde P (-√s) ≤ y ∧ y ≤ Ytilde P √s := by
  rw [← SigmaV_sq, Real.sq_le hs,
    ← (Ytilde_strictMono P).le_iff_le (a := -√s) (b := SigmaV P y),
    ← (Ytilde_strictMono P).le_iff_le (a := SigmaV P y) (b := √s), Ytilde_SigmaV]

/-- The length `X̃(√s) - X̃(-√s)` of the sublevel interval `{R̃ ≤ s}`. -/
def Lx (s : ℝ) : ℝ := Xtilde P √s - Xtilde P (-√s)

lemma Lx_continuous : Continuous (Lx P) := by
  have := (Xtilde_smooth P).continuous
  unfold Lx; fun_prop

lemma Lx_nonneg (s : ℝ) : 0 ≤ Lx P s := by
  unfold Lx
  have := (Xtilde_strictMono P).monotone (show -√s ≤ √s by linarith [Real.sqrt_nonneg s])
  linarith

/-- **Slicing bound.** `X̃(√s) - X̃(-√s) ≥ s - δ'`: the sublevel `{R̃ ≤ s}` contains
`{Rcal(p* + x) ≤ s - δ'} - p*`, an interval of length `s - δ'`. -/
theorem Lx_ge (s : ℝ) : s - deltaPrime P ≤ Lx P s := by
  rcases le_or_gt s (deltaPrime P) with h | h
  · linarith [Lx_nonneg P s]
  set b := s - deltaPrime P
  have hb : 0 ≤ b := by simp only [b]; linarith
  have hs : 0 ≤ s := by linarith [P.deltaPrime_pos]
  have key : ∀ x, P.Rcal x ≤ b → Rtilde P (x - P.pstar) ≤ s := by
    intro x hx
    have := (abs_le.mp (Rtilde_Rcal_close P x)).2
    simp only [b] at hx; linarith
  have hA := div_nonneg hb P.A_pos.le
  have hB := div_nonneg hb P.B_pos.le
  have hle : P.a - b / P.A ≤ P.a + b / P.B := by linarith
  have h0 := (Rtilde_le_iff P hs _).mp (key _ ((P.Rcal_le_iff hb _).mpr ⟨le_refl _, hle⟩))
  have h1 := (Rtilde_le_iff P hs _).mp (key _ ((P.Rcal_le_iff hb _).mpr ⟨hle, le_refl _⟩))
  have hlen := P.sublevel_length b
  unfold Lx; linarith [h0.1, h1.2]

/-! ### Polar coordinates: `𝓐_J(E) = ∫_{u²+v² ≤ E} J` -/

/-- The density in Cartesian coordinates `(u, v) ∈ ℝ × ℝ`. -/
def Kmor (p : ℝ × ℝ) : ℝ := deriv (Xtilde P) p.1 * deriv (Ytilde P) p.2

lemma Kmor_continuous : Continuous (Kmor P) := by
  have h1 := (contDiff_deriv_Xtilde P).continuous
  have h2 := (contDiff_deriv_Ytilde P).continuous
  unfold Kmor; fun_prop

lemma Jmor_continuous : Continuous (Jmor P) := (Jmor_smooth P).continuous

/-- The closed disk `{u² + v² ≤ E}` in `ℝ × ℝ`. -/
def diskR (E : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ E}

lemma measurableSet_diskR (E : ℝ) : MeasurableSet (diskR E) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

lemma Rot_ofReal_re (φ ρ : ℝ) : (Rot φ (ρ : ℂ)).re = ρ * Real.cos φ := by
  simp [Rot, Complex.mul_re, Complex.exp_re, Complex.exp_im, mul_comm]

lemma Rot_ofReal_im (φ ρ : ℝ) : (Rot φ (ρ : ℂ)).im = ρ * Real.sin φ := by
  simp [Rot, Complex.mul_im, Complex.exp_re, Complex.exp_im, mul_comm]

lemma Jbar_JmorF_sq (s : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Jbar (JmorF P) s (ρ ^ 2) =
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, Kmor P (ρ * Real.cos φ, ρ * Real.sin φ) := by
  unfold Jbar JmorF
  rw [Real.sqrt_sq hρ]
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [Jmor, Kmor, Rot_ofReal_re, Rot_ofReal_im]

lemma Jbar_JmorF_continuous (s : ℝ) : Continuous (Jbar (JmorF P) s) := by
  unfold Jbar JmorF
  refine continuous_const.mul ?_
  have hR := contDiff_Rot.continuous
  have hJ := Jmor_continuous P
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hJ.comp (hR.comp (continuous_snd.prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst))))

/-- The angular integral over `(-π, π)` equals the one over `(0, 2π)` (periodicity). -/
lemma angular_shift (ρ : ℝ) :
    ∫ θ in (-π)..π, Kmor P (ρ * Real.cos θ, ρ * Real.sin θ) =
      ∫ θ in (0 : ℝ)..2 * π, Kmor P (ρ * Real.cos θ, ρ * Real.sin θ) := by
  have hper : Function.Periodic (fun θ => Kmor P (ρ * Real.cos θ, ρ * Real.sin θ)) (2 * π) := by
    intro θ; simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  exact this

/-- Polar coordinates: `∫_{u²+v² ≤ E} J = ∫₀^{√E} ρ ∫_{-π}^{π} J(ρ e^{iθ}) dθ dρ`. -/
theorem disk_integral_polar {E : ℝ} (hE : 0 ≤ E) :
    ∫ p, (diskR E).indicator (Kmor P) p =
      ∫ ρ in (0 : ℝ)..√E, ρ * ∫ θ in (-π)..π, Kmor P (ρ * Real.cos θ, ρ * Real.sin θ) := by
  rw [← integral_comp_polarCoord_symm]
  set g : ℝ × ℝ → ℝ := fun p => p.1 * Kmor P (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  have hg : Continuous g := by
    have := Kmor_continuous P
    simp only [g]; fun_prop
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • (diskR E).indicator (Kmor P) (polarCoord.symm p) =
        (Iic √E ×ˢ univ).indicator g p := by
    rintro ⟨ρ, θ⟩ ⟨hρ, -⟩
    simp only [mem_Ioi] at hρ
    have hmem : polarCoord.symm (ρ, θ) ∈ diskR E ↔ (ρ, θ) ∈ Iic √E ×ˢ (univ : Set ℝ) := by
      simp only [diskR, polarCoord_symm_apply, mem_ofPred_eq, mem_prod, mem_Iic, mem_univ,
        and_true]
      rw [show (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 by
        nlinarith [Real.cos_sq_add_sin_sq θ]]
      rw [Real.le_sqrt hρ.le hE]
    by_cases h : polarCoord.symm (ρ, θ) ∈ diskR E
    · rw [indicator_of_mem h, indicator_of_mem (hmem.mp h)]
      simp [g, polarCoord_symm_apply, Kmor, smul_eq_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mpr h')), smul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr,
    setIntegral_indicator (measurableSet_Iic.prod MeasurableSet.univ)]
  have hset : polarCoord.target ∩ Iic √E ×ˢ (univ : Set ℝ) = Ioc 0 √E ×ˢ Ioo (-π) π := by
    rw [polarCoord_target, prod_inter_prod, Ioi_inter_Iic, inter_univ]
  rw [hset, Measure.volume_eq_prod, setIntegral_prod]
  · rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg E)]
    refine setIntegral_congr_fun measurableSet_Ioc fun ρ _ => ?_
    simp only [g]
    rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  · have hc : IntegrableOn g (Icc 0 √E ×ˢ Icc (-π) π) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hc.mono_set (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)

/-- `𝓐_J(E) = π ∫₀^E J̄ = ∫₀^{√E} 2π ρ J̄(ρ²) dρ = ∫_{u²+v² ≤ E} J`. -/
theorem Acal_eq_disk (s : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    Acal (JmorF P) s E = ∫ p, (diskR E).indicator (Kmor P) p := by
  rw [disk_integral_polar P hE]
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := √E)
    (f := fun ρ : ℝ => ρ ^ 2) (f' := fun ρ => 2 * ρ) (g := Jbar (JmorF P) s)
    (fun ρ _ => by simpa using hasDerivAt_pow 2 ρ) (by fun_prop) (Jbar_JmorF_continuous P s)
  simp only [Function.comp_def, Real.sq_sqrt hE, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hsub
  rw [Acal, ← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ρ hρ => ?_
  rw [uIcc_of_le (Real.sqrt_nonneg E)] at hρ
  rw [Jbar_JmorF_sq P s hρ.1, angular_shift]
  field_simp

/-! ### Fubini: the slice formula -/

lemma integrable_disk (E : ℝ) : Integrable ((diskR E).indicator (Kmor P)) (volume.prod volume) := by
  rw [← Measure.volume_eq_prod, integrable_indicator_iff (measurableSet_diskR E)]
  have hc : IntegrableOn (Kmor P) (Icc (-√E) √E ×ˢ Icc (-√E) √E) :=
    (Kmor_continuous P).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine hc.mono_set fun p hp => ?_
  simp only [diskR, mem_ofPred_eq] at hp
  have hE : 0 ≤ E := le_trans (by positivity) hp
  exact ⟨(Real.sq_le hE).mp (by nlinarith [sq_nonneg p.2]),
    (Real.sq_le hE).mp (by nlinarith [sq_nonneg p.1])⟩

lemma slice_integral {E : ℝ} (hE : 0 ≤ E) (v : ℝ) :
    ∫ u, (diskR E).indicator (Kmor P) (u, v) =
      (Icc (-√E) √E).indicator (fun v => deriv (Ytilde P) v * Lx P (E - v ^ 2)) v := by
  by_cases hv : v ^ 2 ≤ E
  · have hvmem : v ∈ Icc (-√E) √E := (Real.sq_le hE).mp hv
    rw [indicator_of_mem hvmem]
    set r := √(E - v ^ 2)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hset : ∀ u, (u, v) ∈ diskR E ↔ u ∈ Icc (-r) r := by
      intro u
      simp only [diskR, mem_ofPred_eq]
      rw [mem_Icc, ← Real.sq_le (by linarith)]
      constructor <;> intro h <;> linarith
    have hfun : (fun u => (diskR E).indicator (Kmor P) (u, v)) =
        (Icc (-r) r).indicator (fun u => deriv (Ytilde P) v * deriv (Xtilde P) u) := by
      funext u
      by_cases hu : u ∈ Icc (-r) r
      · rw [indicator_of_mem ((hset u).mpr hu), indicator_of_mem hu, Kmor, mul_comm]
      · rw [indicator_of_notMem (fun h => hu ((hset u).mp h)), indicator_of_notMem hu]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
    congr 1
    have hd := (Xtilde_smooth P).differentiable (by simp)
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x)
      ((contDiff_deriv_Xtilde P).continuous.intervalIntegrable _ _)]
    rfl
  · have hvmem : v ∉ Icc (-√E) √E := fun h => hv ((Real.sq_le hE).mpr h)
    rw [indicator_of_notMem hvmem]
    have : ∀ u, (u, v) ∉ diskR E := by
      intro u hu; simp only [diskR, mem_ofPred_eq] at hu; apply hv; nlinarith [sq_nonneg u]
    simp [indicator_of_notMem (this _)]

/-- **Slice formula.** `𝓐_J(E) = ∫_{-√E}^{√E} Ỹ'(v) (X̃(√(E-v²)) - X̃(-√(E-v²))) dv`. -/
theorem Acal_eq_slices (s : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    Acal (JmorF P) s E =
      ∫ v in (-√E)..√E, deriv (Ytilde P) v * Lx P (E - v ^ 2) := by
  rw [Acal_eq_disk P s hE, Measure.volume_eq_prod, integral_prod_symm _ (integrable_disk P E)]
  simp_rw [slice_integral P hE]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.sqrt_nonneg E])]

/-! ### The area lower bound (`lem:pll-area`) -/

/-- The integrand `(E - δ' - Ṽ(y))₊` of the slicing argument. -/
def gpos (E y : ℝ) : ℝ := max (E - deltaPrime P - Vtilde P y) 0

lemma gpos_continuous (E : ℝ) : Continuous (gpos P E) := by
  have := (contDiff_Vtilde P).continuous
  unfold gpos; fun_prop

lemma gpos_eq_zero {E y : ℝ} (h : E ≤ Vtilde P y) : gpos P E y = 0 := by
  unfold gpos; have := P.deltaPrime_pos; exact max_eq_right (by linarith)

/-- `Ṽ ≥ E` outside `(Ỹ(-√E), Ỹ(√E))`. -/
lemma Vtilde_ge_of_le {E y : ℝ} (hE : 0 ≤ E) (hy : y ≤ Ytilde P (-√E)) : E ≤ Vtilde P y := by
  by_contra h
  push Not at h
  have := ((Vtilde_le_iff P hE y).mp h.le).1
  have hy' : y = Ytilde P (-√E) := le_antisymm hy this
  rw [hy', Vtilde_Ytilde, neg_sq, Real.sq_sqrt hE] at h
  exact lt_irrefl _ h

lemma Vtilde_ge_of_ge {E y : ℝ} (hE : 0 ≤ E) (hy : Ytilde P √E ≤ y) : E ≤ Vtilde P y := by
  by_contra h
  push Not at h
  have := ((Vtilde_le_iff P hE y).mp h.le).2
  have hy' : y = Ytilde P √E := le_antisymm this hy
  rw [hy', Vtilde_Ytilde, Real.sq_sqrt hE] at h
  exact lt_irrefl _ h

/-- **`lem:pll-area`.** `𝓐_J(E) ≥ E - d₀` for `E ≥ 0`. -/
theorem Acal_ge (s : ℝ) {E : ℝ} (hE : 0 ≤ E) : E - P.d0 ≤ Acal (JmorF P) s E := by
  rw [Acal_eq_slices P s hE]
  set a := Ytilde P (-√E)
  set b := Ytilde P √E
  have hYd : ∀ v, HasDerivAt (Ytilde P) (deriv (Ytilde P) v) v := fun v =>
    ((Ytilde_smooth P).differentiable (by simp) v).hasDerivAt
  have hYc := (contDiff_deriv_Ytilde P).continuous
  have hg := gpos_continuous P E
  -- Step 1: pointwise slicing bound and substitution `y = Ỹ(v)`.
  have h1 : ∫ y in a..b, gpos P E y ≤ ∫ v in (-√E)..√E, deriv (Ytilde P) v * Lx P (E - v ^ 2) := by
    rw [← intervalIntegral.integral_comp_mul_deriv (fun v _ => hYd v) hYc.continuousOn hg]
    refine intervalIntegral.integral_mono_on (by linarith [Real.sqrt_nonneg E])
      (((hg.comp (Ytilde_smooth P).continuous).mul hYc).intervalIntegrable _ _)
      ((hYc.mul ((Lx_continuous P).comp (continuous_const.sub (continuous_pow 2)))).intervalIntegrable
        _ _) fun v _ => ?_
    simp only [Function.comp_apply, gpos, Vtilde_Ytilde]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Ytilde_deriv_pos P v).le
    exact max_le (by linarith [Lx_ge P (E - v ^ 2)]) (Lx_nonneg P _)
  -- Step 2: `g` vanishes outside `[a, b]`, so the integral over `[a, b]` dominates the one over
  -- `[-1/2, 1/2]`.
  have hab : a ≤ b := (Ytilde_strictMono P).monotone (by linarith [Real.sqrt_nonneg E])
  set c := min a (-1 / 2)
  set d := max b (1 / 2)
  have hint : ∀ x y : ℝ, IntervalIntegrable (gpos P E) volume x y :=
    fun x y => hg.intervalIntegrable x y
  have hca : ∫ y in c..a, gpos P E y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro y hy
      rw [uIcc_of_le (min_le_left _ _)] at hy
      exact gpos_eq_zero P (Vtilde_ge_of_le P hE hy.2)
  have hbd : ∫ y in b..d, gpos P E y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro y hy
      rw [uIcc_of_le (le_max_left _ _)] at hy
      exact gpos_eq_zero P (Vtilde_ge_of_ge P hE hy.1)
  have h2 : ∫ y in c..d, gpos P E y = ∫ y in a..b, gpos P E y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint c a) (hint a d),
      ← intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b d), hca, hbd]
    ring
  have h3 : ∫ y in (-1 / 2 : ℝ)..(1 / 2), gpos P E y ≤ ∫ y in c..d, gpos P E y :=
    intervalIntegral.integral_mono_interval (min_le_right _ _) (by norm_num) (le_max_right _ _)
      (Eventually.of_forall fun y => le_max_right _ _) (hint c d)
  -- Step 3: drop the positive part.
  have hV := (contDiff_Vtilde P).continuous
  have h4 : ∫ y in (-1 / 2 : ℝ)..(1 / 2), (E - deltaPrime P - Vtilde P y) ≤
      ∫ y in (-1 / 2 : ℝ)..(1 / 2), gpos P E y :=
    intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop) (hint _ _) fun y _ => le_max_left _ _
  have h5 : ∫ y in (-1 / 2 : ℝ)..(1 / 2), (E - deltaPrime P - Vtilde P y) = E - P.d0 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hV.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, Params.d0, muV]
    ring
  linarith

/-- **`lem:pll-morse-density`.** `𝓐_J(E) → ∞` as `E → ∞`. -/
theorem Acal_tendsto (s : ℝ) : Tendsto (Acal (JmorF P) s) atTop atTop := by
  have hlin : Tendsto (fun E : ℝ => E - P.d0) atTop atTop := tendsto_atTop_add_const_right _ _
    tendsto_id
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with E hE
  exact Acal_ge P s hE

/-! ### The area identity -/

end SymplecticPacking.Inner
