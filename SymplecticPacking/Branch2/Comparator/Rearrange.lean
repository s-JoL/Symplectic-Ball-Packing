import Mathlib
import OAI.Geometry.BallPacking.Moments.ConvexRearrangement

/-!
# The increasing rearrangement on an interval (`lem:fcp-interval`, `lem:cmp-rearrangement`, m = 1)

For `f : ℝ → ℝ` continuous on `[0, h]` and `I ∈ [0, h]`,
`(R f)(I) = min_{0 ≤ a ≤ h - I} max(f(a), f(a + I))`.
For convex `f` the sublevel sets of `f` in `[0,h]` are intervals and `R f` is the increasing
rearrangement of `f` (`rearr_integral`). The definition is an infimum of a compact set of reals
(Mathlib's `sInf` on `ℝ`, whitelisted).

Properties used later:
* `rearr_le`, `rearr_attained` — the minimum is attained;
* `rearr_le_add` — sup-norm nonexpansiveness;
* `rearr_sublevel` — for convex `f`, an interval of length `I` lies in `{f ≤ R f(I)}`
  (this is what the planar realisation uses);
* `rearr_monotoneOn`, `rearr_convexOn`, `rearr_lipschitz` — shape of `R f`;
* `rearr_integral` — `∫₀ʰ R f = ∫₀ʰ f` (from the vendored `IntervalMinimum.integral_eq`).
-/

noncomputable section

namespace SymplecticPacking.Branch2.Cmp

open Set MeasureTheory

/-- The two-endpoint value `max(f(a), f(a + I))`. -/
def endVal (f : ℝ → ℝ) (I a : ℝ) : ℝ := max (f a) (f (a + I))

/-- **The rearrangement** `(R f)(I) = inf_{0 ≤ a ≤ h - I} max(f(a), f(a + I))`. -/
def rearr (h : ℝ) (f : ℝ → ℝ) (I : ℝ) : ℝ := sInf (endVal f I '' Icc 0 (h - I))

variable {h : ℝ} {f g : ℝ → ℝ} {I : ℝ}

lemma endVal_continuousOn (hf : ContinuousOn f (Icc 0 h)) (hI : 0 ≤ I) :
    ContinuousOn (endVal f I) (Icc 0 (h - I)) := by
  have h1 : ContinuousOn f (Icc 0 (h - I)) :=
    hf.mono (Icc_subset_Icc le_rfl (by linarith))
  have h2 : ContinuousOn (fun a => f (a + I)) (Icc 0 (h - I)) :=
    hf.comp (continuous_id.add continuous_const).continuousOn
      (fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩)
  exact h1.sup h2

lemma image_compact (hf : ContinuousOn f (Icc 0 h)) (hI : 0 ≤ I) :
    IsCompact (endVal f I '' Icc 0 (h - I)) :=
  isCompact_Icc.image_of_continuousOn (endVal_continuousOn hf hI)

lemma rearr_le (hf : ContinuousOn f (Icc 0 h)) (hI : 0 ≤ I) {a : ℝ} (ha : a ∈ Icc 0 (h - I)) :
    rearr h f I ≤ max (f a) (f (a + I)) :=
  csInf_le (image_compact hf hI).bddBelow ⟨a, ha, rfl⟩

lemma rearr_attained (hf : ContinuousOn f (Icc 0 h)) (hI : I ∈ Icc 0 h) :
    ∃ a ∈ Icc 0 (h - I), rearr h f I = max (f a) (f (a + I)) := by
  have hne : (endVal f I '' Icc 0 (h - I)).Nonempty :=
    ⟨_, 0, ⟨le_rfl, by linarith [hI.2]⟩, rfl⟩
  obtain ⟨a, ha, he⟩ := (image_compact hf hI.1).sInf_mem hne
  exact ⟨a, ha, he.symm⟩

/-- Monotonicity in `f` (up to an additive constant): `f ≤ g + ε` on `[0,h]` implies
`R f ≤ R g + ε` (sup-norm nonexpansiveness). -/
lemma rearr_le_add (hf : ContinuousOn f (Icc 0 h)) (hg : ContinuousOn g (Icc 0 h))
    (hI : I ∈ Icc 0 h) {ε : ℝ} (hfg : ∀ x ∈ Icc 0 h, f x ≤ g x + ε) :
    rearr h f I ≤ rearr h g I + ε := by
  obtain ⟨a, ha, he⟩ := rearr_attained hg hI
  have h1 : a ∈ Icc 0 h := ⟨ha.1, by linarith [ha.2, hI.1]⟩
  have h2 : a + I ∈ Icc 0 h := ⟨by linarith [ha.1, hI.1], by linarith [ha.2]⟩
  calc rearr h f I ≤ max (f a) (f (a + I)) := rearr_le hf hI.1 ha
    _ ≤ max (g a + ε) (g (a + I) + ε) := max_le_max (hfg a h1) (hfg _ h2)
    _ = max (g a) (g (a + I)) + ε := max_add_add_right _ _ _
    _ = rearr h g I + ε := by rw [he]

/-- For convex `f`, an interval of length `I` lies in the sublevel set `{f ≤ R f(I)}`. -/
lemma rearr_sublevel (hf : ContinuousOn f (Icc 0 h)) (hconv : ConvexOn ℝ (Icc 0 h) f)
    (hI : I ∈ Icc 0 h) :
    ∃ α ∈ Icc 0 (h - I), ∀ x ∈ Icc α (α + I), f x ≤ rearr h f I := by
  obtain ⟨a, ha, he⟩ := rearr_attained hf hI
  refine ⟨a, ha, fun x hx => ?_⟩
  rw [he]
  have h1 : a ∈ Icc 0 h := ⟨ha.1, by linarith [ha.2, hI.1]⟩
  have h2 : a + I ∈ Icc 0 h := ⟨by linarith [ha.1, hI.1], by linarith [ha.2]⟩
  exact hconv.le_max_of_mem_Icc h1 h2 hx

/-- `R f` is nondecreasing on `[0, h]` for convex `f`. -/
lemma rearr_monotoneOn (hf : ContinuousOn f (Icc 0 h)) (hconv : ConvexOn ℝ (Icc 0 h) f) :
    MonotoneOn (rearr h f) (Icc 0 h) := by
  intro I hI I' hI' hII
  obtain ⟨a, ha, he⟩ := rearr_attained hf hI'
  have ha' : a ∈ Icc 0 (h - I) := ⟨ha.1, by linarith [ha.2]⟩
  have h1 : a ∈ Icc 0 h := ⟨ha.1, by linarith [ha.2, hI'.1]⟩
  have h2 : a + I' ∈ Icc 0 h := ⟨by linarith [ha.1, hI'.1], by linarith [ha.2]⟩
  calc rearr h f I ≤ max (f a) (f (a + I)) := rearr_le hf hI.1 ha'
    _ ≤ max (f a) (f (a + I')) := max_le (le_max_left _ _)
        (hconv.le_max_of_mem_Icc h1 h2 ⟨by linarith [hI.1], by linarith⟩)
    _ = rearr h f I' := he.symm

/-- `R f` is convex on `[0, h]` for convex `f`. -/
lemma rearr_convexOn (hf : ContinuousOn f (Icc 0 h)) (hconv : ConvexOn ℝ (Icc 0 h) f) :
    ConvexOn ℝ (Icc 0 h) (rearr h f) := by
  refine ⟨convex_Icc 0 h, ?_⟩
  intro I hI J hJ a b ha hb hab
  obtain ⟨A, hA, hAe⟩ := rearr_attained hf hI
  obtain ⟨B, hB, hBe⟩ := rearr_attained hf hJ
  have hK : a • I + b • J ∈ Icc 0 h := convex_Icc 0 h hI hJ ha hb hab
  simp only [smul_eq_mul] at hK ⊢
  have hC : a * A + b * B ∈ Icc 0 (h - (a * I + b * J)) := by
    refine ⟨add_nonneg (mul_nonneg ha hA.1) (mul_nonneg hb hB.1), ?_⟩
    have e : h = a * h + b * h := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hA.2 ha, mul_le_mul_of_nonneg_left hB.2 hb]
  have hA0 : A ∈ Icc 0 h := ⟨hA.1, by linarith [hA.2, hI.1]⟩
  have hB0 : B ∈ Icc 0 h := ⟨hB.1, by linarith [hB.2, hJ.1]⟩
  have hA1 : A + I ∈ Icc 0 h := ⟨by linarith [hA.1, hI.1], by linarith [hA.2]⟩
  have hB1 : B + J ∈ Icc 0 h := ⟨by linarith [hB.1, hJ.1], by linarith [hB.2]⟩
  have c1 := hconv.2 hA0 hB0 ha hb hab
  have c2 := hconv.2 hA1 hB1 ha hb hab
  simp only [smul_eq_mul] at c1 c2
  have hx1 : f A ≤ rearr h f I := by rw [hAe]; exact le_max_left _ _
  have hx2 : f (A + I) ≤ rearr h f I := by rw [hAe]; exact le_max_right _ _
  have hy1 : f B ≤ rearr h f J := by rw [hBe]; exact le_max_left _ _
  have hy2 : f (B + J) ≤ rearr h f J := by rw [hBe]; exact le_max_right _ _
  refine (rearr_le hf hK.1 hC).trans (max_le ?_ ?_)
  · exact c1.trans (add_le_add (mul_le_mul_of_nonneg_left hx1 ha)
      (mul_le_mul_of_nonneg_left hy1 hb))
  · have e : a * A + b * B + (a * I + b * J) = a * (A + I) + b * (B + J) := by ring
    rw [e]
    exact c2.trans (add_le_add (mul_le_mul_of_nonneg_left hx2 ha)
      (mul_le_mul_of_nonneg_left hy2 hb))

/-- One-sided bound used for `rearr_lipschitz`: for `0 ≤ x ≤ y ≤ h`,
`R f(x) ≤ R f(y) + L(y-x)` and `R f(y) ≤ R f(x) + L(y-x)`. -/
lemma rearr_lip_aux (hf : ContinuousOn f (Icc 0 h)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |f x - f y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc 0 h) (hy : y ∈ Icc 0 h) (hxy : x ≤ y) :
    rearr h f x ≤ rearr h f y + L * (y - x) ∧ rearr h f y ≤ rearr h f x + L * (y - x) := by
  have hup : ∀ u ∈ Icc 0 h, ∀ v ∈ Icc 0 h, |u - v| ≤ y - x → f u ≤ f v + L * (y - x) := by
    intro u hu v hv huv
    have h1 := (abs_sub_le_iff.1 (hLip u hu v hv)).1
    nlinarith [mul_le_mul_of_nonneg_left huv hL]
  constructor
  · obtain ⟨a, ha, he⟩ := rearr_attained hf hy
    have ha' : a ∈ Icc 0 (h - x) := ⟨ha.1, by linarith [ha.2]⟩
    have h1 : a + x ∈ Icc 0 h := ⟨by linarith [ha.1, hx.1], by linarith [ha.2]⟩
    have h2 : a + y ∈ Icc 0 h := ⟨by linarith [ha.1, hy.1], by linarith [ha.2]⟩
    have h3 := hup (a + x) h1 (a + y) h2 (by rw [abs_le]; constructor <;> linarith)
    calc rearr h f x ≤ max (f a) (f (a + x)) := rearr_le hf hx.1 ha'
      _ ≤ max (f a) (f (a + y)) + L * (y - x) := by
          have hL' : 0 ≤ L * (y - x) := mul_nonneg hL (by linarith)
          apply max_le
          · linarith [le_max_left (f a) (f (a + y))]
          · linarith [le_max_right (f a) (f (a + y))]
      _ = rearr h f y + L * (y - x) := by rw [he]
  · obtain ⟨a, ha, he⟩ := rearr_attained hf hx
    set a' := min a (h - y) with ha'def
    have ha'1 : a' ≤ a := min_le_left _ _
    have ha'2 : a' ≤ h - y := min_le_right _ _
    have ha'3 : a - (y - x) ≤ a' := le_min (by linarith) (by linarith [ha.2])
    have ha'0 : 0 ≤ a' := le_min ha.1 (by linarith [hy.2])
    have hmem : a' ∈ Icc 0 (h - y) := ⟨ha'0, ha'2⟩
    have h1 : a' ∈ Icc 0 h := ⟨ha'0, by linarith [hy.1]⟩
    have h2 : a ∈ Icc 0 h := ⟨ha.1, by linarith [ha.2, hx.1]⟩
    have h3 : a' + y ∈ Icc 0 h := ⟨by linarith [hy.1], by linarith⟩
    have h4 : a + x ∈ Icc 0 h := ⟨by linarith [ha.1, hx.1], by linarith [ha.2]⟩
    have e1 := hup a' h1 a h2 (by rw [abs_le]; constructor <;> linarith)
    have e2 := hup (a' + y) h3 (a + x) h4 (by rw [abs_le]; constructor <;> linarith)
    calc rearr h f y ≤ max (f a') (f (a' + y)) := rearr_le hf hy.1 hmem
      _ ≤ max (f a) (f (a + x)) + L * (y - x) := by
          apply max_le
          · linarith [le_max_left (f a) (f (a + x))]
          · linarith [le_max_right (f a) (f (a + x))]
      _ = rearr h f x + L * (y - x) := by rw [he]

/-- `R` preserves Lipschitz bounds on `[0, h]`. -/
lemma rearr_lipschitz (hf : ContinuousOn f (Icc 0 h)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |f x - f y| ≤ L * |x - y|) :
    ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |rearr h f x - rearr h f y| ≤ L * |x - y| := by
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · obtain ⟨h1, h2⟩ := rearr_lip_aux hf hL hLip hx hy hxy
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := rearr_lip_aux hf hL hLip hy hx hxy
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_le]
    constructor <;> linarith

lemma rearr_continuousOn (hf : ContinuousOn f (Icc 0 h)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc 0 h, ∀ y ∈ Icc 0 h, |f x - f y| ≤ L * |x - y|) :
    ContinuousOn (rearr h f) (Icc 0 h) := by
  have hR := rearr_lipschitz hf hL hLip
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (L + 1), div_pos hε (by linarith), fun y hy hxy => ?_⟩
  rw [Real.dist_eq] at hxy ⊢
  have := hR y hy x hx
  calc |rearr h f y - rearr h f x| ≤ L * |y - x| := this
    _ ≤ (L + 1) * |y - x| := by nlinarith [abs_nonneg (y - x)]
    _ < (L + 1) * (ε / (L + 1)) := by
        apply mul_lt_mul_of_pos_left hxy (by linarith)
    _ = ε := by field_simp

/-- Variant of the vendored `IntervalMinimum.integral_eq` in which `g` is only required to be
measurable (the vendored proof uses continuity of `g` only through measurability). -/
lemma integral_eq_aux {D : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Measurable g) (hconv : ConvexOn ℝ (Set.Icc 0 D) f)
    (hchar : ∀ h ∈ Set.Icc 0 D, ∀ c, g h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + h ≤ D ∧ f a ≤ c ∧ f (a+h) ≤ c) :
    ∫ h in Set.Icc 0 D, g h = ∫ h in Set.Icc 0 D, f h := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 D)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hm : μ.map g = μ.map f := by
    apply Measure.ext_of_Iic
    intro c
    rw [Measure.map_apply hg measurableSet_Iic,
      Measure.map_apply hf.measurable measurableSet_Iic]
    dsimp [μ]
    rw [Measure.restrict_apply (hg measurableSet_Iic),
      Measure.restrict_apply (hf.measurable measurableSet_Iic)]
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, and_comm] using
      OAI.PackingSufficiencySupport.Comparison.IntervalMinimum.sublevel_volume_eq hf hconv hchar c
  have h := congrArg (fun ν : Measure ℝ => ∫ t, t ∂ν) hm
  rw [MeasureTheory.integral_map (f := fun t : ℝ => t) hg.aemeasurable (by fun_prop),
    MeasureTheory.integral_map (f := fun t : ℝ => t) hf.measurable.aemeasurable (by fun_prop)] at h
  exact h

/-- **Equimeasurability.** `∫₀ʰ R f = ∫₀ʰ f` for continuous convex `f`
(`IntervalMinimum.integral_eq` of the vendored library). -/
lemma rearr_integral (hf : ContinuousOn f (Icc 0 h)) (hconv : ConvexOn ℝ (Icc 0 h) f)
    (hh : 0 ≤ h) : ∫ x in (0 : ℝ)..h, rearr h f x = ∫ x in (0 : ℝ)..h, f x := by
  set cl : ℝ → ℝ := fun x => max 0 (min h x) with hcl
  have cl_mem : ∀ x, cl x ∈ Icc 0 h := fun x =>
    ⟨le_max_left _ _, max_le hh (min_le_left _ _)⟩
  have cl_id : ∀ x ∈ Icc 0 h, cl x = x := fun x hx => by
    simp only [hcl, min_eq_right hx.2, max_eq_right hx.1]
  have cl_cont : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have cl_mono : Monotone cl := fun x y hxy => max_le_max le_rfl (min_le_min le_rfl hxy)
  set F : ℝ → ℝ := fun x => f (cl x) with hF
  set G : ℝ → ℝ := fun x => rearr h f (cl x) with hG
  have hFc : Continuous F := hf.comp_continuous cl_cont cl_mem
  have hGm : Measurable G := by
    have hmono : Monotone G := fun x y hxy =>
      rearr_monotoneOn hf hconv (cl_mem x) (cl_mem y) (cl_mono hxy)
    exact hmono.measurable
  have hFeq : EqOn f F (Icc 0 h) := fun x hx => by simp only [hF, cl_id x hx]
  have hGeq : EqOn (rearr h f) G (Icc 0 h) := fun x hx => by simp only [hG, cl_id x hx]
  have hFconv : ConvexOn ℝ (Icc 0 h) F := hconv.congr hFeq
  have hchar : ∀ t ∈ Icc 0 h, ∀ c, G t ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + t ≤ h ∧ F a ≤ c ∧ F (a + t) ≤ c := by
    intro t ht c
    rw [← hGeq ht]
    constructor
    · intro hc
      obtain ⟨a, ha, he⟩ := rearr_attained hf ht
      have h1 : a ∈ Icc 0 h := ⟨ha.1, by linarith [ha.2, ht.1]⟩
      have h2 : a + t ∈ Icc 0 h := ⟨by linarith [ha.1, ht.1], by linarith [ha.2]⟩
      refine ⟨a, ha.1, by linarith [ha.2], ?_, ?_⟩
      · rw [← hFeq h1]; exact (le_max_left _ _).trans (he.symm.le.trans hc)
      · rw [← hFeq h2]; exact (le_max_right _ _).trans (he.symm.le.trans hc)
    · rintro ⟨a, ha, hat, hfa, hfat⟩
      have h1 : a ∈ Icc 0 h := ⟨ha, by linarith [ht.1]⟩
      have h2 : a + t ∈ Icc 0 h := ⟨by linarith [ht.1], hat⟩
      rw [← hFeq h1] at hfa
      rw [← hFeq h2] at hfat
      exact (rearr_le hf ht.1 ⟨ha, by linarith⟩).trans (max_le hfa hfat)
  have key : ∫ x in Icc 0 h, G x = ∫ x in Icc 0 h, F x :=
    integral_eq_aux hFc hGm hFconv hchar
  rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
    setIntegral_congr_fun measurableSet_Icc hGeq, setIntegral_congr_fun measurableSet_Icc hFeq]
  exact key

end SymplecticPacking.Branch2.Cmp
