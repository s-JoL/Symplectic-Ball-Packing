import Mathlib

/-!
# Smoothing the comparison function (m = 1)

`K_N` is continuous, convex and `M`-Lipschitz on `[0, h]` but has no closed polyhedral form in
this formalisation (it is defined through `sInf`). It is smoothed in two explicit steps:

1. **Convex Lipschitz extension** to `ℝ` by inf-convolution,
   `K^ext(p) = inf_{x ∈ [0,h]} (K_N(x) + M|p - x|)`; equal to `K_N` on `[0,h]`, convex and
   `M`-Lipschitz on `ℝ`.
2. **Mollification** with the explicit bump `β(t) = expNegInvGlue(1 - t²)` (support `[-1,1]`):
   `K(p) = (∫β)⁻¹ ∫_{-1}^{1} K^ext(p - w t) β(t) dt`; `C^∞`, convex, `|K - K^ext| ≤ M w`.

This is the scalar mollifier construction in the supplement, `sec:scalar-iteration`,
`eq:scalar-mollifier` and `prop:scalar-cmp-gap`. The general finite-dimensional polyhedral
comparator instead uses log-sum-exp (`lem:fcp-smoothing`); that is a separate construction
and is not the definition of `smoothK` in this scalar branch.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Cmp

open Set
open scoped ContDiff

/-- **Inf-convolution extension** `K^ext(p) = inf_{x ∈ [0,h]} (f(x) + M|p - x|)`. -/
def infExt (h M : ℝ) (f : ℝ → ℝ) (p : ℝ) : ℝ := sInf ((fun x => f x + M * |p - x|) '' Icc 0 h)

/-- The bump `β(t) = expNegInvGlue(1 - t²)`, positive exactly on `(-1, 1)`. -/
def bump (t : ℝ) : ℝ := expNegInvGlue (1 - t ^ 2)

/-- `∫_{-1}^{1} β`. -/
def bumpMass : ℝ := ∫ t in (-1 : ℝ)..1, bump t

/-- **Mollification** at scale `w`: `(∫β)⁻¹ ∫_{-1}^{1} g(p - w t) β(t) dt`. -/
def mollify (w : ℝ) (g : ℝ → ℝ) (p : ℝ) : ℝ := bumpMass⁻¹ * ∫ t in (-1 : ℝ)..1, g (p - w * t) * bump t

/-- The smoothed comparison function `K = mollify_w (K^ext)`. -/
def smoothK (h M w : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := mollify w (infExt h M f)

variable {h M w : ℝ} {f g : ℝ → ℝ}

/-! ### The extension -/

private lemma infExt_set_compact (hf : ContinuousOn f (Icc 0 h)) (p : ℝ) :
    IsCompact ((fun x => f x + M * |p - x|) '' Icc 0 h) :=
  isCompact_Icc.image_of_continuousOn
    (hf.add ((continuous_const.mul (continuous_const.sub continuous_id).abs).continuousOn))

private lemma infExt_le (hf : ContinuousOn f (Icc 0 h)) (p : ℝ) {x : ℝ} (hx : x ∈ Icc 0 h) :
    infExt h M f p ≤ f x + M * |p - x| :=
  csInf_le (infExt_set_compact hf p).bddBelow ⟨x, hx, rfl⟩

private lemma infExt_attained (hh : 0 ≤ h) (hf : ContinuousOn f (Icc 0 h)) (p : ℝ) :
    ∃ x ∈ Icc 0 h, infExt h M f p = f x + M * |p - x| := by
  have hne : ((fun x => f x + M * |p - x|) '' Icc 0 h).Nonempty :=
    ⟨_, ⟨0, ⟨le_rfl, hh⟩, rfl⟩⟩
  obtain ⟨x, hx, hxe⟩ := (infExt_set_compact (M := M) hf p).sInf_mem hne
  exact ⟨x, hx, hxe.symm⟩

lemma infExt_eq (hh : 0 ≤ h) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc 0 h))
    (hLip : ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |f x - f y| ≤ M * |x - y|) {p : ℝ} (hp : p ∈ Icc 0 h) :
    infExt h M f p = f p := by
  refine IsLeast.csInf_eq ⟨⟨p, hp, by simp⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hLip p hp x hx
  have h2 := le_abs_self (f p - f x)
  show f p ≤ f x + M * |p - x|
  linarith

lemma infExt_lipschitz (hh : 0 ≤ h) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc 0 h)) (p q : ℝ) :
    |infExt h M f p - infExt h M f q| ≤ M * |p - q| := by
  have key : ∀ p q : ℝ, infExt h M f p ≤ infExt h M f q + M * |p - q| := by
    intro p q
    obtain ⟨y, hy, hye⟩ := infExt_attained (M := M) hh hf q
    have h1 := infExt_le (M := M) hf p hy
    have h2 : |p - y| ≤ |p - q| + |q - y| := abs_sub_le p q y
    have h3 := mul_le_mul_of_nonneg_left h2 hM
    nlinarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [key p q]
  · have := key q p
    rw [abs_sub_comm] at this
    linarith

lemma infExt_convex (hh : 0 ≤ h) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc 0 h))
    (hconv : ConvexOn ℝ (Icc 0 h) f) : ConvexOn ℝ univ (infExt h M f) := by
  refine ⟨convex_univ, fun p _ q _ a b ha hb hab => ?_⟩
  obtain ⟨x, hx, hxe⟩ := infExt_attained (M := M) hh hf p
  obtain ⟨y, hy, hye⟩ := infExt_attained (M := M) hh hf q
  have hz := (convex_Icc (0 : ℝ) h) hx hy ha hb hab
  have h1 := infExt_le (M := M) hf (a • p + b • q) hz
  have h2 := hconv.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h1 h2 ⊢
  have h3 : |a * p + b * q - (a * x + b * y)| ≤ a * |p - x| + b * |q - y| := by
    have : a * p + b * q - (a * x + b * y) = a * (p - x) + b * (q - y) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h4 := mul_le_mul_of_nonneg_left h3 hM
  rw [hxe, hye]
  nlinarith

lemma infExt_continuous (hh : 0 ≤ h) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc 0 h)) :
    Continuous (infExt h M f) := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨M, hM⟩) fun p q => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact infExt_lipschitz (M := M) hh hM hf p q

/-! ### The mollifier -/

lemma bump_nonneg (t : ℝ) : 0 ≤ bump t := expNegInvGlue.nonneg _

lemma bump_contDiff {n : ℕ∞} : ContDiff ℝ n bump :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma bump_continuous : Continuous bump := (bump_contDiff (n := 0)).continuous

lemma bump_eq_zero {t : ℝ} (ht : t ≤ -1 ∨ 1 ≤ t) : bump t = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  rcases ht with ht | ht <;> nlinarith

lemma bump_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < bump t := by
  apply expNegInvGlue.pos_of_pos
  obtain ⟨h1, h2⟩ := ht
  nlinarith

/-- The normalised average `(∫β)⁻¹ ∫_{-1}^{1} φ β`. -/
private def avg (φ : ℝ → ℝ) : ℝ := bumpMass⁻¹ * ∫ t in (-1 : ℝ)..1, φ t * bump t

private lemma ii {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun t => φ t * bump t) MeasureTheory.volume (-1) 1 :=
  (hφ.mul bump_continuous).intervalIntegrable _ _

lemma bumpMass_pos : 0 < bumpMass :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (bump_continuous.intervalIntegrable _ _)
    (fun _ ht => bump_pos ht) (by norm_num)

private lemma avg_mono {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hle : ∀ t ∈ Icc (-1 : ℝ) 1, φ t ≤ ψ t) : avg φ ≤ avg ψ := by
  unfold avg
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 bumpMass_pos.le)
  exact intervalIntegral.integral_mono_on (by norm_num) (ii hφ) (ii hψ)
    (fun t ht => mul_le_mul_of_nonneg_right (hle t ht) (bump_nonneg t))

private lemma avg_lin {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (a b : ℝ) :
    avg (fun t => a * φ t + b * ψ t) = a * avg φ + b * avg ψ := by
  unfold avg
  have e : (fun t => (a * φ t + b * ψ t) * bump t)
      = fun t => a * (φ t * bump t) + b * (ψ t * bump t) := by funext t; ring
  rw [e, intervalIntegral.integral_add ((ii hφ).const_mul a) ((ii hψ).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

private lemma avg_const (c : ℝ) : avg (fun _ => c) = c := by
  unfold avg
  rw [intervalIntegral.integral_const_mul]
  change bumpMass⁻¹ * (c * bumpMass) = c
  field_simp [bumpMass_pos.ne']

private lemma avg_add_const {φ : ℝ → ℝ} (hφ : Continuous φ) (c : ℝ) :
    avg (fun t => φ t + c) = avg φ + c := by
  have := avg_lin hφ (continuous_const (y := (1 : ℝ))) 1 c
  simp only [one_mul, mul_one] at this
  rw [this, avg_const, mul_one]

private lemma lip_cont (hM : 0 ≤ M) (hg : ∀ p q, |g p - g q| ≤ M * |p - q|) : Continuous g :=
  (LipschitzWith.of_dist_le_mul (K := ⟨M, hM⟩) fun p q => by
    rw [Real.dist_eq, Real.dist_eq]; exact hg p q).continuous

private lemma mollify_eq_avg (w : ℝ) (g : ℝ → ℝ) (p : ℝ) :
    mollify w g p = avg (fun t => g (p - w * t)) := rfl

lemma mollify_contDiff (hw : 0 < w) (hg : Continuous g) :
    ContDiff ℝ ∞ (mollify w g) := by
  set φ : ℝ → ℝ := fun s => bump (s / w) with hφdef
  have hφc : ContDiff ℝ (⊤ : ℕ∞) φ := bump_contDiff.comp (contDiff_id.div_const w)
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -w) (b := w)) fun s hs => ?_
    apply bump_eq_zero
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · left; rw [div_le_iff₀ hw]; linarith
    · right; rw [le_div_iff₀ hw]; linarith
  have hconv := hφs.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hφc
    (μ := MeasureTheory.volume) hg.locallyIntegrable
  have key : mollify w g = fun p =>
      (bumpMass⁻¹ * w⁻¹) *
        MeasureTheory.convolution φ g (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume p := by
    funext p
    rw [MeasureTheory.convolution_mul]
    unfold mollify
    rw [intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · have e : (fun t => g (p - w * t) * bump t)
          = fun t => φ (w * t) * g (p - w * t) := by
        funext t
        simp only [hφdef]
        rw [mul_div_cancel_left₀ t hw.ne', mul_comm]
      have hc := MeasureTheory.Measure.integral_comp_mul_left (fun s => φ s * g (p - s)) w
      rw [e]
      rw [hc, abs_of_pos (inv_pos.2 hw), smul_eq_mul]
      ring
    · intro t ht
      rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rw [bump_eq_zero (by rcases ht with ht | ht <;> [left; right] <;> linarith), mul_zero]
  rw [key]
  exact contDiff_const.mul hconv

lemma mollify_convex (hw : 0 < w) (hg : Continuous g) (hconv : ConvexOn ℝ univ g) :
    ConvexOn ℝ univ (mollify w g) := by
  refine ⟨convex_univ, fun p _ q _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, mollify_eq_avg]
  have hcp : Continuous fun t => g (p - w * t) := hg.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hcq : Continuous fun t => g (q - w * t) := hg.comp (continuous_const.sub (continuous_const.mul continuous_id))
  rw [← avg_lin hcp hcq]
  refine avg_mono (hg.comp (continuous_const.sub (continuous_const.mul continuous_id)))
    ((continuous_const.mul hcp).add (continuous_const.mul hcq)) fun t _ => ?_
  have e : a * p + b * q - w * t = a • (p - w * t) + b • (q - w * t) := by
    simp only [smul_eq_mul]
    have : a * p + b * q - w * t = a * (p - w * t) + b * (q - w * t) + (a + b - 1) * (w * t) := by
      ring
    rw [this, hab]; ring
  rw [e]
  simpa only [smul_eq_mul] using hconv.2 (mem_univ _) (mem_univ _) ha hb hab

lemma mollify_close (hw : 0 < w) (hM : 0 ≤ M) (hg : ∀ p q, |g p - g q| ≤ M * |p - q|) (p : ℝ) :
    |mollify w g p - g p| ≤ M * w := by
  have hgc := lip_cont hM hg
  have hc : Continuous fun t => g (p - w * t) :=
    hgc.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have bnd : ∀ t ∈ Icc (-1 : ℝ) 1, |g (p - w * t) - g p| ≤ M * w := by
    intro t ht
    refine (hg _ _).trans ?_
    have : |p - w * t - p| ≤ w := by
      rw [show p - w * t - p = -(w * t) by ring, abs_neg, abs_mul, abs_of_pos hw]
      have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
      nlinarith
    exact mul_le_mul_of_nonneg_left this hM
  rw [mollify_eq_avg, abs_sub_le_iff]
  constructor
  · have := avg_mono hc (continuous_const (y := g p + M * w)) fun t ht => by
      linarith [(abs_sub_le_iff.1 (bnd t ht)).1]
    rw [avg_const] at this
    linarith
  · have := avg_mono continuous_const hc (φ := fun _ => g p - M * w)
      fun t ht => by linarith [(abs_sub_le_iff.1 (bnd t ht)).2]
    rw [avg_const] at this
    linarith

lemma mollify_lipschitz (hw : 0 < w) (hM : 0 ≤ M) (hg : ∀ p q, |g p - g q| ≤ M * |p - q|)
    (p q : ℝ) : |mollify w g p - mollify w g q| ≤ M * |p - q| := by
  have hgc := lip_cont hM hg
  have key : ∀ p q : ℝ, mollify w g p ≤ mollify w g q + M * |p - q| := by
    intro p q
    have hcp : Continuous fun t => g (p - w * t) :=
      hgc.comp (continuous_const.sub (continuous_const.mul continuous_id))
    have hcq : Continuous fun t => g (q - w * t) :=
      hgc.comp (continuous_const.sub (continuous_const.mul continuous_id))
    have := avg_mono hcp (hcq.add continuous_const) (ψ := fun t => g (q - w * t) + M * |p - q|)
      fun t _ => by
        have h1 := hg (p - w * t) (q - w * t)
        rw [show p - w * t - (q - w * t) = p - q by ring] at h1
        linarith [le_abs_self (g (p - w * t) - g (q - w * t))]
    rw [avg_add_const hcq] at this
    simpa only [mollify_eq_avg] using this
  rw [abs_sub_le_iff]
  constructor
  · linarith [key p q]
  · have := key q p
    rw [abs_sub_comm] at this
    linarith

/-! ### The smoothed comparison function -/

theorem smoothK_contDiff (hh : 0 ≤ h) (hM : 0 ≤ M) (hw : 0 < w) (hf : ContinuousOn f (Icc 0 h)) :
    ContDiff ℝ ∞ (smoothK h M w f) :=
  mollify_contDiff hw (infExt_continuous hh hM hf)

theorem smoothK_convex (hh : 0 ≤ h) (hM : 0 ≤ M) (hw : 0 < w) (hf : ContinuousOn f (Icc 0 h))
    (hconv : ConvexOn ℝ (Icc 0 h) f) : ConvexOn ℝ univ (smoothK h M w f) :=
  mollify_convex hw (infExt_continuous hh hM hf) (infExt_convex hh hM hf hconv)

theorem smoothK_close (hh : 0 ≤ h) (hM : 0 ≤ M) (hw : 0 < w) (hf : ContinuousOn f (Icc 0 h))
    (hLip : ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |f x - f y| ≤ M * |x - y|) {p : ℝ}
    (hp : p ∈ Icc 0 h) : |smoothK h M w f p - f p| ≤ M * w := by
  have := mollify_close hw hM (infExt_lipschitz hh hM hf) p
  rwa [infExt_eq hh hM hf hLip hp] at this

theorem smoothK_lipschitz (hh : 0 ≤ h) (hM : 0 ≤ M) (hw : 0 < w) (hf : ContinuousOn f (Icc 0 h))
    (p q : ℝ) : |smoothK h M w f p - smoothK h M w f q| ≤ M * |p - q| :=
  mollify_lipschitz hw hM (infExt_lipschitz hh hM hf) p q

end SymplecticPacking.Branch2.Cmp
