import Mathlib

/-!
# The argument principle for parallelograms

For the parallelogram `P = {a + s ω₁ + t ω₂ : s, t ∈ [0,1]}` with `Im (ω₂/ω₁) > 0`, its
counterclockwise boundary contour `∂P` (four segments), and an entire function `f` without
zeros on `∂P`,
`(2πi)⁻¹ ∮_{∂P} f'/f = ∑_{b ∈ int P} ord_b f`.

Proof: (1) segment integrals of `(z - b)⁻¹` are computed with a branch of `log` on a half-plane;
(2) hence `∮_{∂P} (z - b)⁻¹` is `2πi` for `b ∈ int P` (sum of four angles in `(0, π)` whose
exponential is `1`) and `0` for `b ∉ P` (one half-plane contains `P`);
(3) on a disc `U ⊇ P`, `f = (∏ (z - u)^{m_u}) g` with `g` holomorphic and zero-free on `U`
(Mathlib's `MeromorphicOn.extract_zeros_poles`), so `f'/f = ∑ m_u/(z - u) + g'/g` on `∂P`, and
`g'/g` has a primitive on `U` (Mathlib's `DifferentiableOn.isExactOn_ball`).
-/

noncomputable section

namespace SymplecticPacking.Complex

open _root_.Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real ComplexConjugate

/-! ## Segment and parallelogram contour integrals -/

/-- `∫_{[p,q]} F(z) dz = ∫₀¹ F(p + t(q-p)) (q-p) dt`. -/
def segInt (F : ℂ → ℂ) (p q : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, F (p + t * (q - p)) * (q - p)

/-- The segment `[p,q]` lies in `S`. -/
def SegOn (S : Set ℂ) (p q : ℂ) : Prop := ∀ t ∈ Icc (0 : ℝ) 1, p + t * (q - p) ∈ S

/-- The counterclockwise boundary integral over the parallelogram with vertices
`a, a + ω₁, a + ω₁ + ω₂, a + ω₂`. -/
def paraContour (a ω₁ ω₂ : ℂ) (F : ℂ → ℂ) : ℂ :=
  segInt F a (a + ω₁) + segInt F (a + ω₁) (a + ω₁ + ω₂) +
    segInt F (a + ω₁ + ω₂) (a + ω₂) + segInt F (a + ω₂) a

/-- The closed parallelogram. -/
def paraSet (a ω₁ ω₂ : ℂ) : Set ℂ :=
  {z | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, z = a + s * ω₁ + t * ω₂}

/-- The open parallelogram. -/
def paraInterior (a ω₁ ω₂ : ℂ) : Set ℂ :=
  {z | ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1, z = a + s * ω₁ + t * ω₂}

/-- The boundary of the parallelogram. -/
def paraBoundary (a ω₁ ω₂ : ℂ) : Set ℂ :=
  {z | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) ∧
    z = a + s * ω₁ + t * ω₂}

/-- `Im (conj ω₁ · ω₂)`, positive iff `(ω₁, ω₂)` is positively oriented. -/
def kap (ω₁ ω₂ : ℂ) : ℝ := ω₁.re * ω₂.im - ω₁.im * ω₂.re

/-! ## Basic segment calculus -/

lemma hasDerivAt_segPath (p q : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => p + (t : ℂ) * (q - p)) (q - p) t := by
  have h := ((hasDerivAt_id t).ofReal_comp).mul_const (q - p)
  simpa using h.const_add p

lemma continuous_segPath (p q : ℂ) : Continuous (fun t : ℝ => p + (t : ℂ) * (q - p)) := by
  fun_prop

lemma SegOn.mono {S T : Set ℂ} {p q : ℂ} (h : SegOn S p q) (hST : S ⊆ T) : SegOn T p q :=
  fun t ht => hST (h t ht)

lemma SegOn.continuousOn {S : Set ℂ} {p q : ℂ} {F : ℂ → ℂ} (h : SegOn S p q)
    (hF : ContinuousOn F S) : ContinuousOn (fun t : ℝ => F (p + t * (q - p))) (Icc 0 1) :=
  hF.comp (continuous_segPath p q).continuousOn h

lemma SegOn.intervalIntegrable {S : Set ℂ} {p q : ℂ} {F : ℂ → ℂ} (h : SegOn S p q)
    (hF : ContinuousOn F S) :
    IntervalIntegrable (fun t : ℝ => F (p + t * (q - p)) * (q - p)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact (h.continuousOn hF).mul continuousOn_const

/-- Fundamental theorem of calculus along a segment. -/
theorem segInt_eq_sub {S : Set ℂ} {F f : ℂ → ℂ} {p q : ℂ} (hseg : SegOn S p q)
    (hF : ∀ z ∈ S, HasDerivAt F (f z) z) (hc : ContinuousOn f S) :
    segInt f p q = F q - F p := by
  unfold segInt
  have key : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => F (p + t * (q - p)))
      (f (p + t * (q - p)) * (q - p)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hF _ (hseg t ht)).comp t (hasDerivAt_segPath p q t)
  rw [integral_eq_sub_of_hasDerivAt key (hseg.intervalIntegrable hc)]
  simp

theorem segInt_congr {S : Set ℂ} {F G : ℂ → ℂ} {p q : ℂ} (hseg : SegOn S p q)
    (h : ∀ z ∈ S, F z = G z) : segInt F p q = segInt G p q := by
  unfold segInt
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h _ (hseg t ht)]

theorem segInt_add {S : Set ℂ} {F G : ℂ → ℂ} {p q : ℂ} (hseg : SegOn S p q)
    (hF : ContinuousOn F S) (hG : ContinuousOn G S) :
    segInt (fun z => F z + G z) p q = segInt F p q + segInt G p q := by
  unfold segInt
  simp only [add_mul]
  exact integral_add (hseg.intervalIntegrable hF) (hseg.intervalIntegrable hG)

theorem segInt_const_mul (c : ℂ) (F : ℂ → ℂ) (p q : ℂ) :
    segInt (fun z => c * F z) p q = c * segInt F p q := by
  unfold segInt
  simp only [mul_assoc]
  exact integral_const_mul c _

theorem segInt_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} {S : Set ℂ} {p q : ℂ}
    (hseg : SegOn S p q) (hF : ∀ i ∈ s, ContinuousOn (F i) S) :
    segInt (fun z => ∑ i ∈ s, F i z) p q = ∑ i ∈ s, segInt (F i) p q := by
  unfold segInt
  simp only [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum (fun i hi => hseg.intervalIntegrable (hF i hi))

/-! ## Parallelogram contour calculus -/

lemma segOn_edges (a ω₁ ω₂ : ℂ) :
    SegOn (paraBoundary a ω₁ ω₂) a (a + ω₁) ∧
    SegOn (paraBoundary a ω₁ ω₂) (a + ω₁) (a + ω₁ + ω₂) ∧
    SegOn (paraBoundary a ω₁ ω₂) (a + ω₁ + ω₂) (a + ω₂) ∧
    SegOn (paraBoundary a ω₁ ω₂) (a + ω₂) a := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have h1t : ∀ t ∈ Icc (0 : ℝ) 1, 1 - t ∈ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨fun t ht => ⟨t, ht, 0, h0, Or.inr (Or.inr (Or.inl rfl)), by push_cast; ring⟩,
    fun t ht => ⟨1, h1, t, ht, Or.inr (Or.inl rfl), by push_cast; ring⟩,
    fun t ht => ⟨1 - t, h1t t ht, 1, h1, Or.inr (Or.inr (Or.inr rfl)), by push_cast; ring⟩,
    fun t ht => ⟨0, h0, 1 - t, h1t t ht, Or.inl rfl, by push_cast; ring⟩⟩

lemma paraBoundary_subset (a ω₁ ω₂ : ℂ) : paraBoundary a ω₁ ω₂ ⊆ paraSet a ω₁ ω₂ := by
  rintro z ⟨s, hs, t, ht, -, rfl⟩
  exact ⟨s, hs, t, ht, rfl⟩

lemma paraInterior_subset (a ω₁ ω₂ : ℂ) : paraInterior a ω₁ ω₂ ⊆ paraSet a ω₁ ω₂ := by
  rintro z ⟨s, hs, t, ht, rfl⟩
  exact ⟨s, Ioo_subset_Icc_self hs, t, Ioo_subset_Icc_self ht, rfl⟩

lemma mem_paraInterior_of_not_boundary {a ω₁ ω₂ z : ℂ} (hz : z ∈ paraSet a ω₁ ω₂)
    (hb : z ∉ paraBoundary a ω₁ ω₂) : z ∈ paraInterior a ω₁ ω₂ := by
  obtain ⟨s, hs, t, ht, rfl⟩ := hz
  have hs0 : s ≠ 0 := fun h => hb ⟨s, hs, t, ht, Or.inl h, rfl⟩
  have hs1 : s ≠ 1 := fun h => hb ⟨s, hs, t, ht, Or.inr (Or.inl h), rfl⟩
  have ht0 : t ≠ 0 := fun h => hb ⟨s, hs, t, ht, Or.inr (Or.inr (Or.inl h)), rfl⟩
  have ht1 : t ≠ 1 := fun h => hb ⟨s, hs, t, ht, Or.inr (Or.inr (Or.inr h)), rfl⟩
  exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩, t,
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, rfl⟩

theorem paraContour_eq_zero_of_hasDerivAt {S : Set ℂ} {F f : ℂ → ℂ} {a ω₁ ω₂ : ℂ}
    (hS : paraBoundary a ω₁ ω₂ ⊆ S) (hF : ∀ z ∈ S, HasDerivAt F (f z) z)
    (hc : ContinuousOn f S) : paraContour a ω₁ ω₂ f = 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := segOn_edges a ω₁ ω₂
  unfold paraContour
  rw [segInt_eq_sub (e0.mono hS) hF hc, segInt_eq_sub (e1.mono hS) hF hc,
    segInt_eq_sub (e2.mono hS) hF hc, segInt_eq_sub (e3.mono hS) hF hc]
  ring

theorem paraContour_congr {a ω₁ ω₂ : ℂ} {F G : ℂ → ℂ}
    (h : ∀ z ∈ paraBoundary a ω₁ ω₂, F z = G z) :
    paraContour a ω₁ ω₂ F = paraContour a ω₁ ω₂ G := by
  obtain ⟨e0, e1, e2, e3⟩ := segOn_edges a ω₁ ω₂
  unfold paraContour
  rw [segInt_congr e0 h, segInt_congr e1 h, segInt_congr e2 h, segInt_congr e3 h]

theorem paraContour_add {a ω₁ ω₂ : ℂ} {F G : ℂ → ℂ}
    (hF : ContinuousOn F (paraBoundary a ω₁ ω₂)) (hG : ContinuousOn G (paraBoundary a ω₁ ω₂)) :
    paraContour a ω₁ ω₂ (fun z => F z + G z) = paraContour a ω₁ ω₂ F + paraContour a ω₁ ω₂ G := by
  obtain ⟨e0, e1, e2, e3⟩ := segOn_edges a ω₁ ω₂
  unfold paraContour
  rw [segInt_add e0 hF hG, segInt_add e1 hF hG, segInt_add e2 hF hG, segInt_add e3 hF hG]
  ring

theorem paraContour_finset_sum {ι : Type*} (s : Finset ι) {a ω₁ ω₂ : ℂ} {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ s, ContinuousOn (F i) (paraBoundary a ω₁ ω₂)) :
    paraContour a ω₁ ω₂ (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, paraContour a ω₁ ω₂ (F i) := by
  obtain ⟨e0, e1, e2, e3⟩ := segOn_edges a ω₁ ω₂
  unfold paraContour
  rw [segInt_finset_sum s e0 hF, segInt_finset_sum s e1 hF, segInt_finset_sum s e2 hF,
    segInt_finset_sum s e3 hF]
  simp only [Finset.sum_add_distrib]

theorem paraContour_const_mul (a ω₁ ω₂ c : ℂ) (F : ℂ → ℂ) :
    paraContour a ω₁ ω₂ (fun z => c * F z) = c * paraContour a ω₁ ω₂ F := by
  unfold paraContour
  simp only [segInt_const_mul]
  ring

/-- **Cauchy's theorem** for a parallelogram inside a disc. -/
theorem paraContour_eq_zero_of_differentiableOn {a ω₁ ω₂ : ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hP : paraBoundary a ω₁ ω₂ ⊆ Metric.ball c r) :
    paraContour a ω₁ ω₂ f = 0 := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  exact paraContour_eq_zero_of_hasDerivAt hP hF hf.continuousOn

/-! ## Integrals of `(z - b)⁻¹` -/

lemma ne_of_halfplane {b c z : ℂ} (hz : 0 < (c * (z - b)).re) : z - b ≠ 0 := by
  intro h0; rw [h0, mul_zero, zero_re] at hz; exact lt_irrefl _ hz

lemma c_ne_of_halfplane {b c z : ℂ} (hz : 0 < (c * (z - b)).re) : c ≠ 0 := by
  intro h0; rw [h0, zero_mul, zero_re] at hz; exact lt_irrefl _ hz

lemma hasDerivAt_log_halfplane {b c z : ℂ} (hz : 0 < (c * (z - b)).re) :
    HasDerivAt (fun z => log (c * (z - b))) ((z - b)⁻¹) z := by
  have hd : HasDerivAt (fun z => c * (z - b)) c z := by
    simpa using ((hasDerivAt_id z).sub_const b).const_mul c
  have := hd.clog (mem_slitPlane_iff.mpr (Or.inl hz))
  convert this using 1
  field_simp [c_ne_of_halfplane hz, ne_of_halfplane hz]

lemma continuousOn_inv_halfplane (b c : ℂ) :
    ContinuousOn (fun z => (z - b)⁻¹) {z : ℂ | 0 < (c * (z - b)).re} :=
  ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun _ hz => ne_of_halfplane hz

theorem segInt_inv_eq_log {p q b c : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (p + t * (q - p) - b)).re) :
    segInt (fun z => (z - b)⁻¹) p q = log (c * (q - b)) - log (c * (p - b)) :=
  segInt_eq_sub (S := {z : ℂ | 0 < (c * (z - b)).re}) (F := fun z => log (c * (z - b))) h
    (fun _ hz => hasDerivAt_log_halfplane hz) (continuousOn_inv_halfplane b c)

/-- If `P` lies in an open half-plane `Re (c (z - b)) > 0`, then `∮_{∂P} (z - b)⁻¹ = 0`. -/
theorem paraContour_inv_halfplane {a ω₁ ω₂ b c : ℂ}
    (h : ∀ z ∈ paraSet a ω₁ ω₂, 0 < (c * (z - b)).re) :
    paraContour a ω₁ ω₂ (fun z => (z - b)⁻¹) = 0 :=
  paraContour_eq_zero_of_hasDerivAt (S := {z : ℂ | 0 < (c * (z - b)).re})
    (F := fun z => log (c * (z - b))) (fun z hz => h z (paraBoundary_subset a ω₁ ω₂ hz))
    (fun _ hz => hasDerivAt_log_halfplane hz) (continuousOn_inv_halfplane b c)

lemma arg_sub_arg_mem {X Y : ℂ} (hX : 0 < X.re) (hY : 0 < Y.re)
    (h : 0 < X.re * Y.im - X.im * Y.re) : 0 < arg Y - arg X ∧ arg Y - arg X < π := by
  have hX0 : X ≠ 0 := fun h0 => by rw [h0, zero_re] at hX; exact lt_irrefl _ hX
  have hY0 : Y ≠ 0 := fun h0 => by rw [h0, zero_re] at hY; exact lt_irrefl _ hY
  have aX := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hX)
  have aY := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hY)
  rw [abs_lt] at aX aY
  refine ⟨?_, by linarith⟩
  have nX : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  have nY : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
  have hsin : 0 < Real.sin (arg Y - arg X) := by
    rw [Real.sin_sub, sin_arg, sin_arg, cos_arg hX0, cos_arg hY0]
    rw [show Y.im / ‖Y‖ * (X.re / ‖X‖) - Y.re / ‖Y‖ * (X.im / ‖X‖) =
      (X.re * Y.im - X.im * Y.re) / (‖X‖ * ‖Y‖) by field_simp]
    positivity
  by_contra hle
  push Not at hle
  have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hle (by linarith)
  linarith

/-- One edge `p → q` with `b` strictly to its left. -/
lemma edge_left {p q b : ℂ} (h : 0 < (conj (q - p) * (b - p)).im) :
    ∃ L : ℂ, segInt (fun z => (z - b)⁻¹) p q = L ∧ 0 < L.im ∧ L.im < π ∧
      exp L = (q - b) / (p - b) ∧ p - b ≠ 0 := by
  set c : ℂ := I * conj (q - p)
  have key : ∀ t : ℝ, (c * (p + t * (q - p) - b)).re = (conj (q - p) * (b - p)).im := by
    intro t; simp only [c, mul_re, mul_im, I_re, I_im, conj_re, conj_im, sub_re, sub_im, add_re,
      add_im, ofReal_re, ofReal_im]; ring
  have hX : 0 < (c * (p - b)).re := by
    have := key 0; simp only [ofReal_zero, zero_mul, add_zero] at this; rw [this]; exact h
  have hY : 0 < (c * (q - b)).re := by
    have := key 1; simp only [ofReal_one, one_mul, add_sub_cancel] at this; rw [this]; exact h
  have hd : (q - p) ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul, zero_im] at h; exact lt_irrefl _ h
  have hnd : 0 < (q - p).re * (q - p).re + (q - p).im * (q - p).im := by
    have := normSq_pos.mpr hd; rwa [normSq_apply] at this
  have hcross : (c * (p - b)).re * (c * (q - b)).im - (c * (p - b)).im * (c * (q - b)).re =
      (c * (p - b)).re * ((q - p).re * (q - p).re + (q - p).im * (q - p).im) := by
    simp only [c, mul_re, mul_im, I_re, I_im, conj_re, conj_im, sub_re, sub_im]; ring
  have hang := arg_sub_arg_mem hX hY (by rw [hcross]; exact mul_pos hX hnd)
  have hc : c ≠ 0 := c_ne_of_halfplane hX
  have hpb : p - b ≠ 0 := ne_of_halfplane hX
  have hqb : q - b ≠ 0 := ne_of_halfplane hY
  refine ⟨log (c * (q - b)) - log (c * (p - b)),
    segInt_inv_eq_log (fun t _ => by rw [key]; exact h), ?_, ?_, ?_, hpb⟩
  · rw [sub_im, log_im, log_im]; exact hang.1
  · rw [sub_im, log_im, log_im]; exact hang.2
  · rw [exp_sub, exp_log (mul_ne_zero hc hqb), exp_log (mul_ne_zero hc hpb)]
    field_simp

/-- Real coordinates with respect to an `ℝ`-basis `(ω₁, ω₂)`. -/
lemma exists_coords {ω₁ ω₂ : ℂ} (hκ : kap ω₁ ω₂ ≠ 0) (a z : ℂ) :
    ∃ s t : ℝ, z = a + s * ω₁ + t * ω₂ := by
  have hk : kap ω₁ ω₂ = ω₁.re * ω₂.im - ω₁.im * ω₂.re := rfl
  have hinv : kap ω₁ ω₂ * (kap ω₁ ω₂)⁻¹ = 1 := mul_inv_cancel₀ hκ
  refine ⟨((z - a).re * ω₂.im - (z - a).im * ω₂.re) / kap ω₁ ω₂,
    (ω₁.re * (z - a).im - ω₁.im * (z - a).re) / kap ω₁ ω₂, ?_⟩
  apply Complex.ext <;> simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    sub_re, sub_im]
  · linear_combination (-(z.re - a.re)) * hinv + (z.re - a.re) * (kap ω₁ ω₂)⁻¹ * hk
  · linear_combination (-(z.im - a.im)) * hinv + (z.im - a.im) * (kap ω₁ ω₂)⁻¹ * hk

lemma im_conj_mul_comb (ω₁ ω₂ : ℂ) (σ ρ : ℝ) :
    (conj ω₁ * (σ * ω₁ + ρ * ω₂)).im = ρ * kap ω₁ ω₂ ∧
    (conj ω₂ * (σ * ω₁ + ρ * ω₂)).im = -(σ * kap ω₁ ω₂) := by
  constructor <;> simp only [kap, mul_re, mul_im, conj_re, conj_im, add_re, add_im, ofReal_re,
    ofReal_im] <;> ring

/-- `∮_{∂P} (z - b)⁻¹ = 2πi` for `b` in the open parallelogram. -/
theorem paraContour_inv_interior {a ω₁ ω₂ b : ℂ} (hκ : 0 < kap ω₁ ω₂)
    (hb : b ∈ paraInterior a ω₁ ω₂) :
    paraContour a ω₁ ω₂ (fun z => (z - b)⁻¹) = 2 * π * I := by
  obtain ⟨s, hs, t, ht, hbst⟩ := hb
  have c0 : 0 < (conj ((a + ω₁) - a) * (b - a)).im := by
    have e : b - a = (s : ℂ) * ω₁ + (t : ℂ) * ω₂ := by rw [hbst]; ring
    rw [e, show (a + ω₁) - a = ω₁ by ring, (im_conj_mul_comb ω₁ ω₂ s t).1]
    exact mul_pos ht.1 hκ
  have c1 : 0 < (conj ((a + ω₁ + ω₂) - (a + ω₁)) * (b - (a + ω₁))).im := by
    have e : b - (a + ω₁) = ((s - 1 : ℝ) : ℂ) * ω₁ + (t : ℂ) * ω₂ := by
      rw [hbst]; push_cast; ring
    rw [e, show (a + ω₁ + ω₂) - (a + ω₁) = ω₂ by ring, (im_conj_mul_comb ω₁ ω₂ _ _).2]
    nlinarith [hs.2]
  have c2 : 0 < (conj ((a + ω₂) - (a + ω₁ + ω₂)) * (b - (a + ω₁ + ω₂))).im := by
    have e : b - (a + ω₁ + ω₂) = ((s - 1 : ℝ) : ℂ) * ω₁ + ((t - 1 : ℝ) : ℂ) * ω₂ := by
      rw [hbst]; push_cast; ring
    rw [e, show (a + ω₂) - (a + ω₁ + ω₂) = -ω₁ by ring, map_neg, neg_mul, neg_im,
      (im_conj_mul_comb ω₁ ω₂ _ _).1]
    nlinarith [ht.2]
  have c3 : 0 < (conj (a - (a + ω₂)) * (b - (a + ω₂))).im := by
    have e : b - (a + ω₂) = (s : ℂ) * ω₁ + ((t - 1 : ℝ) : ℂ) * ω₂ := by
      rw [hbst]; push_cast; ring
    rw [e, show a - (a + ω₂) = -ω₂ by ring, map_neg, neg_mul, neg_im,
      (im_conj_mul_comb ω₁ ω₂ _ _).2, neg_neg]
    exact mul_pos hs.1 hκ
  obtain ⟨L0, e0, l0, u0, x0, n0⟩ := edge_left c0
  obtain ⟨L1, e1, l1, u1, x1, n1⟩ := edge_left c1
  obtain ⟨L2, e2, l2, u2, x2, n2⟩ := edge_left c2
  obtain ⟨L3, e3, l3, u3, x3, n3⟩ := edge_left c3
  unfold paraContour
  rw [e0, e1, e2, e3]
  have hexp : exp (L0 + L1 + L2 + L3) = 1 := by
    rw [exp_add, exp_add, exp_add, x0, x1, x2, x3]
    field_simp
  obtain ⟨n, hn⟩ := exp_eq_one_iff.mp hexp
  have him : (L0 + L1 + L2 + L3).im = 2 * π * n := by
    rw [hn]; simp; ring
  simp only [add_im] at him
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) < n := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : (n : ℝ) < 2 := by
    by_contra hc; push Not at hc; nlinarith
  have hn1 : n = 1 := by
    have a1 : 0 < n := by exact_mod_cast h1
    have a2 : n < 2 := by exact_mod_cast h2
    omega
  rw [hn, hn1]; simp

/-- `∮_{∂P} (z - b)⁻¹ = 0` for `b` outside the closed parallelogram. -/
theorem paraContour_inv_exterior {a ω₁ ω₂ b : ℂ} (hκ : 0 < kap ω₁ ω₂)
    (hb : b ∉ paraSet a ω₁ ω₂) :
    paraContour a ω₁ ω₂ (fun z => (z - b)⁻¹) = 0 := by
  obtain ⟨s, t, hbst⟩ := exists_coords hκ.ne' a b
  have key : ∀ z ∈ paraSet a ω₁ ω₂, ∃ s' ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1,
      z - b = ((s' - s : ℝ) : ℂ) * ω₁ + ((t' - t : ℝ) : ℂ) * ω₂ := by
    rintro z ⟨s', hs', t', ht', rfl⟩
    exact ⟨s', hs', t', ht', by rw [hbst]; push_cast; ring⟩
  have r : ∀ (σ ρ : ℝ), (-I * conj ω₁ * (σ * ω₁ + ρ * ω₂)).re = ρ * kap ω₁ ω₂ ∧
      (I * conj ω₁ * (σ * ω₁ + ρ * ω₂)).re = -(ρ * kap ω₁ ω₂) ∧
      (I * conj ω₂ * (σ * ω₁ + ρ * ω₂)).re = σ * kap ω₁ ω₂ ∧
      (-I * conj ω₂ * (σ * ω₁ + ρ * ω₂)).re = -(σ * kap ω₁ ω₂) := by
    intro σ ρ
    obtain ⟨h1, h2⟩ := im_conj_mul_comb ω₁ ω₂ σ ρ
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      rw [mul_assoc] <;> simp only [neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul,
        zero_sub, h1, h2, neg_neg]
  have hcase : s < 0 ∨ 1 < s ∨ t < 0 ∨ 1 < t := by
    by_contra hc
    push Not at hc
    exact hb ⟨s, ⟨hc.1, hc.2.1⟩, t, ⟨hc.2.2.1, hc.2.2.2⟩, hbst⟩
  rcases hcase with h | h | h | h
  · apply paraContour_inv_halfplane (c := I * conj ω₂)
    intro z hz
    obtain ⟨s', hs', t', ht', hzb⟩ := key z hz
    rw [hzb, (r _ _).2.2.1]
    exact mul_pos (by linarith [hs'.1]) hκ
  · apply paraContour_inv_halfplane (c := -I * conj ω₂)
    intro z hz
    obtain ⟨s', hs', t', ht', hzb⟩ := key z hz
    rw [hzb, (r _ _).2.2.2]
    nlinarith [hs'.2]
  · apply paraContour_inv_halfplane (c := -I * conj ω₁)
    intro z hz
    obtain ⟨s', hs', t', ht', hzb⟩ := key z hz
    rw [hzb, (r _ _).1]
    exact mul_pos (by linarith [ht'.1]) hκ
  · apply paraContour_inv_halfplane (c := I * conj ω₁)
    intro z hz
    obtain ⟨s', hs', t', ht', hzb⟩ := key z hz
    rw [hzb, (r _ _).2.1]
    nlinarith [ht'.2]

/-! ## The argument principle -/

lemma kap_pos_of_im_div {ω₁ ω₂ : ℂ} (h : 0 < (ω₂ / ω₁).im) : 0 < kap ω₁ ω₂ := by
  have hω : ω₁ ≠ 0 := by rintro rfl; simp at h
  have hn : 0 < normSq ω₁ := normSq_pos.mpr hω
  have e : kap ω₁ ω₂ = (ω₂ / ω₁).im * normSq ω₁ := by
    rw [div_im]; unfold kap; field_simp
  rw [e]; exact mul_pos h hn

lemma paraSet_subset_ball (a ω₁ ω₂ : ℂ) :
    paraSet a ω₁ ω₂ ⊆ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  rintro z ⟨s, hs, t, ht, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have e : a + s * ω₁ + t * ω₂ - a = s * ω₁ + t * ω₂ := by ring
  rw [e]
  have hs' : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  calc ‖(s : ℂ) * ω₁ + t * ω₂‖ ≤ ‖(s : ℂ) * ω₁‖ + ‖(t : ℂ) * ω₂‖ := norm_add_le _ _
    _ = |s| * ‖ω₁‖ + |t| * ‖ω₂‖ := by
      rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖ω₁‖ + 1 * ‖ω₂‖ := by gcongr
    _ < ‖ω₁‖ + ‖ω₂‖ + 1 := by linarith

/-- `∮_{∂P} (z - b)⁻¹` for `b ∉ ∂P`. -/
theorem paraContour_inv {a ω₁ ω₂ b : ℂ} (hκ : 0 < kap ω₁ ω₂) (hb : b ∉ paraBoundary a ω₁ ω₂) :
    paraContour a ω₁ ω₂ (fun z => (z - b)⁻¹) =
      (paraInterior a ω₁ ω₂).indicator (fun _ => 2 * π * I) b := by
  by_cases hi : b ∈ paraInterior a ω₁ ω₂
  · rw [indicator_of_mem hi]; exact paraContour_inv_interior hκ hi
  · rw [indicator_of_notMem hi]
    exact paraContour_inv_exterior hκ fun hP => hi (mem_paraInterior_of_not_boundary hP hb)

/-- **The argument principle for parallelograms.** For an entire function `f` without zeros on
the boundary of the parallelogram `P = {a + s ω₁ + t ω₂ : s, t ∈ [0,1]}` (`Im (ω₂/ω₁) > 0`),
`(2πi)⁻¹ ∮_{∂P} f'/f` is the number of zeros of `f` in the interior of `P`, counted with
multiplicity. -/
theorem argument_principle {a ω₁ ω₂ : ℂ} (hω : 0 < (ω₂ / ω₁).im) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hbd : ∀ z ∈ paraBoundary a ω₁ ω₂, f z ≠ 0) :
    (2 * π * I)⁻¹ * paraContour a ω₁ ω₂ (fun z => deriv f z / f z) =
      ∑ᶠ b ∈ paraInterior a ω₁ ω₂, (analyticOrderNatAt f b : ℂ) := by
  classical
  have hκ := kap_pos_of_im_div hω
  set U := Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) with hU_def
  have hPU : paraSet a ω₁ ω₂ ⊆ U := paraSet_subset_ball a ω₁ ω₂
  have hBU : paraBoundary a ω₁ ω₂ ⊆ U := (paraBoundary_subset a ω₁ ω₂).trans hPU
  have hIU : paraInterior a ω₁ ω₂ ⊆ U := (paraInterior_subset a ω₁ ω₂).trans hPU
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hfaU : AnalyticOnNhd ℂ f U := fun z _ => hf.analyticAt z
  have ha : a ∈ paraBoundary a ω₁ ω₂ :=
    ⟨0, left_mem_Icc.mpr zero_le_one, 0, left_mem_Icc.mpr zero_le_one, Or.inl rfl, by simp⟩
  have hord : ∀ u, analyticOrderAt f u ≠ ⊤ := by
    intro u
    apply hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ a)
      (mem_univ u)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (hbd a ha))]
    exact ENat.zero_ne_top
  have hmord : ∀ u, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf.analyticAt u).meromorphicOrderAt_eq]
    simpa using hord u
  have hmero : MeromorphicOn f U := fun z _ => (hf.analyticAt z).meromorphicAt
  have hfin : (MeromorphicOn.divisor f U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite (fun z _ => (hf.analyticAt z).meromorphicAt)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hmero.extract_zeros_poles (fun u => hmord u) hfin
  set D := MeromorphicOn.divisor f U with hD_def
  set T := hfin.toFinset with hT_def
  have hD_nonneg : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfaU u
  set φ : ℂ → ℂ := fun x => ∏ u ∈ T, (x - u) ^ D u with hφ_def
  have hφ : (∏ᶠ u, (· - u) ^ D u) = φ := by
    rw [Function.FactorizedRational.finprod_eq_fun hfin]
    ext x
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    simp only [Function.mem_mulSupport] at hu
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
    intro h0; apply hu; simp [h0]
  have hφ_an : ∀ x, AnalyticAt ℂ φ x := by
    intro x
    have := Function.FactorizedRational.analyticAt (d := D) (x := x) (hD_nonneg x)
    rwa [hφ] at this
  have hfg' : f =ᶠ[codiscreteWithin U] fun x => φ x * g x := by
    filter_upwards [hfg] with x hx
    rw [hx, hφ]; simp
  -- `f = φ g` on all of `U`
  have hpt : ∀ x ∈ U, f x = φ x * g x := by
    intro x hx
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg') x hx
    have h2 : f =ᶠ[𝓝[≠] x] fun y => φ y * g y := by
      have hU : U ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hx)
      filter_upwards [h1, hU] with y hy hyU
      rcases hy with hy | hy
      · exact hy
      · exact absurd hyU hy
    have t1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
      (hf.continuous.tendsto x).mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (fun y => φ y * g y) (𝓝[≠] x) (𝓝 (φ x * g x)) :=
      ((hφ_an x).continuousAt.mul (hg_an x hx).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (t1.congr' h2) t2
  -- points of `T` are zeros of `f` in `U`
  have hT_zero : ∀ u ∈ T, f u = 0 ∧ u ∈ U := by
    intro u hu
    simp only [T, Set.Finite.mem_toFinset, Function.mem_support] at hu
    have huU : u ∈ U := D.supportWithinDomain (Function.mem_support.mpr hu)
    refine ⟨?_, huU⟩
    by_contra hne
    apply hu
    rw [MeromorphicOn.divisor_apply hmero huU, (hf.analyticAt u).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    simp
  have hT_bd : ∀ u ∈ T, u ∉ paraBoundary a ω₁ ω₂ := fun u hu hub =>
    hbd u hub (hT_zero u hu).1
  -- the logarithmic derivative on `∂P`
  have hdecomp : ∀ z ∈ paraBoundary a ω₁ ω₂, deriv f z / f z =
      ∑ u ∈ T, (D u : ℂ) * (z - u)⁻¹ + deriv g z / g z := by
    intro z hz
    have hzU := hBU hz
    have hzT : ∀ u ∈ T, z - u ≠ 0 := fun u hu h0 =>
      hT_bd u hu (by rw [← sub_eq_zero.mp h0]; exact hz)
    have hev : f =ᶠ[𝓝 z] fun x => φ x * g x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzU] with x hx using hpt x hx
    have hφz : φ z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun u hu => zpow_ne_zero _ (hzT u hu)
    have hgz : g z ≠ 0 := hg_ne ⟨z, hzU⟩
    have e1 : deriv f z / f z = logDeriv (φ * g) z := by
      rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]; rfl
    rw [e1, logDeriv_mul z hφz hgz (hφ_an z).differentiableAt
      (hg_an z hzU).differentiableAt, logDeriv_apply g]
    congr 1
    have eφ : φ = ∏ u ∈ T, (fun x => (x - u) ^ D u) := by
      ext x; simp [φ, Finset.prod_apply]
    rw [eφ, logDeriv_prod (fun u hu => by simpa using zpow_ne_zero (D u) (hzT u hu))
      (fun u hu => (by fun_prop : DifferentiableAt ℂ (fun x => x - u) z).zpow
        (Or.inl (hzT u hu)))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [logDeriv_fun_zpow (by fun_prop : DifferentiableAt ℂ (fun x => x - u) z), logDeriv_apply]
    simp [div_eq_mul_inv]
  -- assemble
  have hcont_inv : ∀ u ∈ T, ContinuousOn (fun z => (D u : ℂ) * (z - u)⁻¹)
      (paraBoundary a ω₁ ω₂) := by
    intro u hu
    refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_)
    intro z hz h0
    exact hT_bd u hu (by rw [← sub_eq_zero.mp h0]; exact hz)
  have hgd : DifferentiableOn ℂ (fun z => deriv g z / g z) U :=
    hg_an.deriv.differentiableOn.div hg_an.differentiableOn (fun z hz => hg_ne ⟨z, hz⟩)
  rw [paraContour_congr hdecomp,
    paraContour_add (F := fun z => ∑ u ∈ T, (D u : ℂ) * (z - u)⁻¹)
      (G := fun z => deriv g z / g z) (continuousOn_finsetSum T hcont_inv)
      (hgd.continuousOn.mono hBU),
    paraContour_finset_sum T hcont_inv, paraContour_eq_zero_of_differentiableOn hgd hBU, add_zero]
  simp only [paraContour_const_mul]
  have hord_eq : ∀ b ∈ U, (analyticOrderNatAt f b : ℂ) = (D b : ℂ) := by
    intro b hb
    rw [hD_def, MeromorphicOn.divisor_apply hmero hb, (hf.analyticAt b).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (hord b)]
    simp
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [paraContour_inv hκ (hT_bd u hu)]
    by_cases hi : u ∈ paraInterior a ω₁ ω₂
    · rw [indicator_of_mem hi, indicator_of_mem hi, hord_eq u (hIU hi)]
      field_simp [two_pi_I_ne_zero]
    · rw [indicator_of_notMem hi, indicator_of_notMem hi]; simp
  · intro b hb
    rw [Function.mem_support] at hb
    have hbI : b ∈ paraInterior a ω₁ ω₂ := by
      by_contra hc; exact hb (indicator_of_notMem hc _)
    rw [indicator_of_mem hbI, hord_eq b (hIU hbI)] at hb
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
    exact fun h0 => hb (by simp [h0])

/-- The zeros of `f` in the open parallelogram form a finite set. -/
theorem finite_zeros_paraInterior {a ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hbd : ∀ z ∈ paraBoundary a ω₁ ω₂, f z ≠ 0) :
    {b ∈ paraInterior a ω₁ ω₂ | f b = 0}.Finite := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have ha : a ∈ paraBoundary a ω₁ ω₂ :=
    ⟨0, left_mem_Icc.mpr zero_le_one, 0, left_mem_Icc.mpr zero_le_one, Or.inl rfl, by simp⟩
  set U := Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1)
  have hmero : MeromorphicOn f U := fun z _ => (hf.analyticAt z).meromorphicAt
  have hfin : (MeromorphicOn.divisor f U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite (fun z _ => (hf.analyticAt z).meromorphicAt)
  apply hfin.subset
  rintro b ⟨hbI, hb0⟩
  have hbU : b ∈ U := paraSet_subset_ball a ω₁ ω₂ (paraInterior_subset a ω₁ ω₂ hbI)
  have hord : analyticOrderAt f b ≠ ⊤ := by
    apply hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ a)
      (mem_univ b)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (hbd a ha))]
    exact ENat.zero_ne_top
  have hpos : analyticOrderAt f b ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨hf.analyticAt b, hb0⟩
  rw [Function.mem_support, MeromorphicOn.divisor_apply hmero hbU,
    (hf.analyticAt b).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hord]
  have : analyticOrderNatAt f b ≠ 0 := by
    intro h0; apply hpos; rw [← Nat.cast_analyticOrderNatAt hord, h0]; rfl
  simpa using this

end SymplecticPacking.Complex
