import Mathlib
import SymplecticPacking.Return.Flow

/-!
# Global flows of globally Lipschitz fields

`sec:shd-four` (`cons:shd4-moser`), generic ODE layer: global flows of smooth, globally Lipschitz,
time-compactly supported fields on a finite-dimensional space (`LField`). Unlike the fields of
`Return/Flow.lean` (`CSField`, compact support in `(t, y)`), these need not be compactly
supported in space — e.g. Moser fields on the universal cover `ℝ⁴` of the closed bundle, which
are periodic in `(u, v)`.

The flow is `Return.flowFrom V t₀ y t`, the value at `t` of the *unique* global integral curve
through `y` at time `t₀` (definite description `Explicit.the`); `Return.flow V t = flowFrom V 0 · t`
and `Return.flowInv V t = flowFrom V t · 0`.

Proved here, for `LField V`: existence/uniqueness, cocycle, inverse, first integrals, fixed points
(`flowFrom_of_stationary`), joint smoothness (comparison with OAI `timeSteps`), and preservation
of a time-dependent 2-form satisfying the OAI transport equation (`flow_preserves_form`, from OAI
`timeSteps_preserves_form`).
-/

noncomputable section

namespace SymplecticPacking.Handle

open Filter Topology Set Metric
open SymplecticPacking.Return (flowFrom flow flowInv IsSolFrom clampR clampR_contDiff clampR_eq
  abs_clampR_le)
open scoped ContDiff NNReal

section flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A time-dependent field that is jointly `C^∞`, globally Lipschitz in `(t, y)`, and vanishes
for `|t| ≥ R`. -/
structure LField (V : ℝ → E → E) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => V p.1 p.2)
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K (fun p : ℝ × E => V p.1 p.2)
  time : ∃ R : ℝ, 0 < R ∧ ∀ t y, R ≤ |t| → V t y = 0

variable {V : ℝ → E → E} (hV : LField V)
include hV

theorem LField.lipschitz_slice : ∃ K : ℝ≥0, ∀ t, LipschitzWith K (V t) := by
  obtain ⟨K, hK⟩ := hV.lipschitz
  refine ⟨K, fun t => LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  have := hK.dist_le_mul (t, y) (t, z)
  simpa [Prod.dist_eq] using this

theorem LField.bound : ∃ C : ℝ≥0, ∀ t y, ‖V t y‖ ≤ C := by
  obtain ⟨K, hK⟩ := hV.lipschitz
  obtain ⟨R, hR0, hRt⟩ := hV.time
  refine ⟨⟨K * (2 * R), mul_nonneg K.coe_nonneg (by linarith)⟩, fun t y => ?_⟩
  by_cases ht : R ≤ |t|
  · rw [hRt t y ht, norm_zero]; exact NNReal.coe_nonneg _
  push Not at ht
  have h1 := hK.dist_le_mul (t, y) (R, y)
  have h0 : V R y = 0 := hRt R y (by rw [abs_of_pos hR0])
  simp only [h0, dist_zero_right, Prod.dist_eq, dist_self] at h1
  have h2 : dist t R ≤ 2 * R := by
    rw [Real.dist_eq]
    have := abs_lt.mp ht
    rw [abs_le]; constructor <;> linarith
  calc ‖V t y‖ ≤ K * max (dist t R) 0 := h1
    _ ≤ K * (2 * R) := by
        gcongr
        exact max_le h2 (by positivity)
    _ = _ := rfl

/-- Existence of global integral curves (Picard–Lindelöf on `[-R', R']`, constant outside). -/
theorem LField.exists_sol (t₀ : ℝ) (x : E) [CompleteSpace E] :
    ∃ u : ℝ → E, IsSolFrom V t₀ x u := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  obtain ⟨C, hC⟩ := hV.bound
  obtain ⟨R, hR0, hRt⟩ := hV.time
  set b : ℝ := max R |t₀| + 1 with hb
  set a : ℝ := -b with ha
  have hab : a ≤ b := by have := le_max_left R |t₀|; linarith
  have hta : t₀ ∈ Icc a b := by
    have h1 := le_max_right R |t₀|
    constructor <;> [linarith [neg_abs_le t₀]; linarith [le_abs_self t₀]]
  have hbR : R + 1 ≤ b := by have := le_max_left R |t₀|; linarith
  have hVa : ∀ s ≤ a, ∀ y, V s y = 0 := fun s hs y => hRt s y (by
    rw [abs_of_neg (by linarith)]; linarith)
  have hVb : ∀ s ≥ b, ∀ y, V s y = 0 := fun s hs y => hRt s y (by
    rw [abs_of_pos (by linarith)]; linarith)
  set rad : ℝ≥0 := C * ⟨b - a, by linarith⟩
  have hPL : IsPicardLindelof (fun t y => V t y) (tmin := a) (tmax := b)
      ⟨t₀, hta⟩ x rad 0 C K := by
    refine ⟨fun t _ => (hlip t).lipschitzOnWith, fun y _ => ?_, fun t _ y _ => hC _ _, ?_⟩
    · exact (hV.smooth.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · simp only [NNReal.coe_zero, sub_zero, rad]
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      exact max_le (by linarith [hta.1]) (by linarith [hta.2])
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  set γ : ℝ → E := fun t => α (max a (min t b)) with hγdef
  have hγα : ∀ t ∈ Icc a b, γ t = α t := by
    intro t ht; simp [hγdef, min_eq_left ht.2, max_eq_right ht.1]
  have hγ0 : γ t₀ = x := by rw [hγα t₀ hta]; exact hα0
  refine ⟨γ, hγ0, fun t => ?_⟩
  have hlo : ∀ s ≤ a, γ s = α a := by
    intro s hs; simp only [hγdef]
    rw [min_eq_left (hs.trans hab), max_eq_left hs]
  have hhi : ∀ s ≥ b, γ s = α b := by
    intro s hs; simp [hγdef, min_eq_right hs, max_eq_right hab]
  have hIcc : ∀ s ∈ Icc a b, HasDerivWithinAt γ (V s (γ s)) (Icc a b) s := by
    intro s hs
    rw [hγα s hs]
    exact (hα s hs).congr (fun r hr => hγα r hr) (hγα s hs)
  have hab' : a < b := by have := le_max_left R |t₀|; linarith
  rcases lt_trichotomy t a with ht | ht' | ht
  · rw [hVa t ht.le]
    apply (hasDerivAt_const t (α a)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs using hlo s hs.le
  · rw [ht', hVa a le_rfl]
    have hleft : HasDerivWithinAt γ 0 (Iic a) a :=
      (hasDerivWithinAt_const a (Iic a) (α a)).congr (fun s hs => hlo s hs) (hlo a le_rfl)
    have hright : HasDerivWithinAt γ 0 (Ici a) a := by
      have h := hIcc a (left_mem_Icc.mpr hab)
      rw [hVa a le_rfl] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab')
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy t b with ht1 | ht1' | ht1
    · exact (hIcc t ⟨ht.le, ht1.le⟩).hasDerivAt (Icc_mem_nhds ht ht1)
    · rw [ht1', hVb b le_rfl]
      have hright : HasDerivWithinAt γ 0 (Ici b) b :=
        (hasDerivWithinAt_const b (Ici b) (α b)).congr (fun s hs => hhi s hs) (hhi b le_rfl)
      have hleft : HasDerivWithinAt γ 0 (Iic b) b := by
        have h := hIcc b (right_mem_Icc.mpr hab)
        rw [hVb b le_rfl] at h
        exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab')
      have := hleft.union hright
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [hVb t ht1.le]
      apply (hasDerivAt_const t (α b)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht1] with s hs using hhi s hs.le

/-- Uniqueness of global integral curves. -/
theorem LField.sol_unique {t₀ : ℝ} {x : E} {u v : ℝ → E} (hu : IsSolFrom V t₀ x u)
    (hv : IsSolFrom V t₀ x v) : u = v := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  exact ODE_solution_unique_univ (s := fun _ => univ) (t₀ := t₀)
    (fun t => (hlip t).lipschitzOnWith) (fun t => ⟨hu.2 t, mem_univ _⟩)
    (fun t => ⟨hv.2 t, mem_univ _⟩) (hu.1.trans hv.1.symm)

variable [CompleteSpace E]

theorem LField.existsUnique (t₀ : ℝ) (x : E) : ∃! u : ℝ → E, IsSolFrom V t₀ x u := by
  obtain ⟨u, hu⟩ := hV.exists_sol t₀ x
  exact ⟨u, hu, fun v hv => hV.sol_unique hv hu⟩

theorem LField.flowFrom_eq {t₀ : ℝ} {x : E} {u : ℝ → E} (hu : IsSolFrom V t₀ x u) (t : ℝ) :
    flowFrom V t₀ x t = u t := by
  unfold flowFrom
  rw [dif_pos (hV.existsUnique t₀ x), Explicit.the_eq (hV.existsUnique t₀ x) hu]

theorem LField.flowFrom_isSol (t₀ : ℝ) (x : E) : IsSolFrom V t₀ x (flowFrom V t₀ x) := by
  obtain ⟨u, hu⟩ := hV.exists_sol t₀ x
  have : flowFrom V t₀ x = u := funext fun t => hV.flowFrom_eq hu t
  rw [this]; exact hu

theorem LField.flowFrom_self (t₀ : ℝ) (x : E) : flowFrom V t₀ x t₀ = x :=
  (hV.flowFrom_isSol t₀ x).1

theorem LField.flowFrom_hasDerivAt (t₀ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun s => flowFrom V t₀ x s) (V t (flowFrom V t₀ x t)) t :=
  (hV.flowFrom_isSol t₀ x).2 t

theorem LField.flowFrom_continuous (t₀ : ℝ) (x : E) : Continuous (flowFrom V t₀ x) :=
  continuous_iff_continuousAt.mpr fun t => (hV.flowFrom_hasDerivAt t₀ x t).continuousAt

/-- Cocycle property. -/
theorem LField.flowFrom_flowFrom (t₀ t₁ : ℝ) (x : E) (t : ℝ) :
    flowFrom V t₁ (flowFrom V t₀ x t₁) t = flowFrom V t₀ x t :=
  hV.flowFrom_eq ⟨rfl, (hV.flowFrom_isSol t₀ x).2⟩ t

theorem LField.flow_zero (x : E) : flow V 0 x = x := hV.flowFrom_self 0 x

theorem LField.flow_hasDerivAt (x : E) (t : ℝ) :
    HasDerivAt (fun s => flow V s x) (V t (flow V t x)) t := hV.flowFrom_hasDerivAt 0 x t

theorem LField.flowInv_flow (t : ℝ) (x : E) : flowInv V t (flow V t x) = x := by
  unfold flowInv flow
  rw [hV.flowFrom_flowFrom, hV.flowFrom_self]

theorem LField.flow_flowInv (t : ℝ) (y : E) : flow V t (flowInv V t y) = y := by
  unfold flowInv flow
  rw [hV.flowFrom_flowFrom, hV.flowFrom_self]

theorem LField.flow_injective (t : ℝ) : Function.Injective (flow V t) :=
  Function.LeftInverse.injective (hV.flowInv_flow t)

/-- A point where the field vanishes at all times is fixed. -/
theorem LField.flowFrom_of_stationary {x : E} (hx : ∀ s, V s x = 0) (t₀ t : ℝ) :
    flowFrom V t₀ x t = x :=
  hV.flowFrom_eq (u := fun _ => x) ⟨rfl, fun s => by rw [hx]; exact hasDerivAt_const s x⟩ t

/-- A first integral of the field is constant along the flow. -/
theorem LField.flowFrom_firstIntegral {Q : E → ℝ} {Q' : E → E →L[ℝ] ℝ}
    (hQ : ∀ y, HasFDerivAt Q (Q' y) y) (hQV : ∀ t y, Q' y (V t y) = 0) (t₀ : ℝ) (x : E)
    (t : ℝ) : Q (flowFrom V t₀ x t) = Q x := by
  have hd : ∀ s, HasDerivAt (fun s => Q (flowFrom V t₀ x s)) 0 s := fun s => by
    have := (hQ _).comp_hasDerivAt s (hV.flowFrom_hasDerivAt t₀ x s)
    rwa [hQV] at this
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv)
    t t₀
  rw [this, hV.flowFrom_self]

end flow

/-! ### Joint smoothness and form preservation, by comparison with OAI's `timeSteps` -/

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {V : ℝ → E → E} (hV : LField V)
include hV

open OAI.PackingSufficiencySupport.Hamiltonian in
/-- On `[-R, R] × E` the flow and its inverse are given by OAI's `timeSteps`. -/
theorem LField.exists_timeSteps {R : ℝ} (hR : 0 ≤ R) : ∃ Φ : ℝ → E ≃ₜ E,
    ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
    ∀ t ∈ Icc (-R) R, ∀ x, Φ t x = flow V t x := by
  obtain ⟨L, hL⟩ := hV.lipschitz
  let X : C(ℝ × E, E) := ⟨fun p => V p.1 p.2, hV.smooth.continuous⟩
  have hX : LipschitzWith L X := hL
  have hXs : ContDiff ℝ ∞ X := hV.smooth
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + 1) * (L : ℝ))
  have hN0 : (0 : ℝ) < N := by have := L.coe_nonneg; nlinarith
  let hf : ℝ → ℝ := fun t => clampR R t / N
  have hh (t : ℝ) : ‖hf t‖ * L < 1 := by
    change ‖clampR R t / (N : ℝ)‖ * L < 1
    rw [norm_div, Real.norm_of_nonneg hN0.le, Real.norm_eq_abs, div_mul_eq_mul_div,
      div_lt_one hN0]
    calc |clampR R t| * L ≤ (R + 1) * L := by gcongr; exact abs_clampR_le hR t
      _ < N := hN
  have hhs : ContDiff ℝ ∞ hf := (clampR_contDiff R).div_const _
  let Φ : ℝ → E ≃ₜ E := fun t => timeSteps X hX hXs (hh t) 0 N
  have hsm := timeSteps_variable_smooth X hX hXs hhs (contDiff_const (c := (0 : ℝ))) hh N
  refine ⟨Φ, hsm.1, hsm.2, fun t ht x => ?_⟩
  have hu := hV.flowFrom_isSol 0 x
  have he := timeSteps_eq_solution X hX hXs (hh t) (flowFrom V 0 x)
    (hV.flowFrom_continuous 0 x) hu.2 0 N
  change timeSteps X hX hXs (hh t) 0 N (flowFrom V 0 x 0) = _ at he
  rw [hu.1] at he
  change timeSteps X hX hXs (hh t) 0 N x = flowFrom V 0 x t
  rw [he]
  congr 1
  change 0 + (N : ℝ) * (clampR R t / N) = t
  rw [clampR_eq ht.1 ht.2]; field_simp; ring

/-- **Joint smoothness of the flow.** -/
theorem LField.flow_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => flow V p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  obtain ⟨Φ, hΦ, -, hΦe⟩ := hV.exists_timeSteps (R := |t| + 1) (by positivity)
  have hO : Prod.fst ⁻¹' Ioo (-(|t| + 1)) (|t| + 1) ∈ 𝓝 ((t, x) : ℝ × E) :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  apply hΦ.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hO] with p hp
  exact (hΦe p.1 ⟨hp.1.le, hp.2.le⟩ p.2).symm

/-- **Joint smoothness of the backward flow.** -/
theorem LField.flowInv_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => flowInv V p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  obtain ⟨Φ, -, hΦi, hΦe⟩ := hV.exists_timeSteps (R := |t| + 1) (by positivity)
  have hO : Prod.fst ⁻¹' Ioo (-(|t| + 1)) (|t| + 1) ∈ 𝓝 ((t, x) : ℝ × E) :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  apply hΦi.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hO] with p hp
  have h1 := hΦe p.1 ⟨hp.1.le, hp.2.le⟩ (flowInv V p.1 p.2)
  rw [hV.flow_flowInv] at h1
  rw [Homeomorph.eq_symm_apply]; exact h1

theorem LField.flow_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (flow V t) :=
  hV.flow_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem LField.flowInv_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (flowInv V t) :=
  hV.flowInv_smooth.comp (contDiff_const.prodMk contDiff_id)

open OAI.PackingSufficiencySupport.Hamiltonian in
/-- **Form preservation** (OAI `timeSteps_preserves_form`): if the time-dependent 2-form `Ω` on
`ℝ × E` satisfies the transport equation `L_{(1,V)} Ω = 0` everywhere, then
`φ_t^* Ω_t = Ω_0`. -/
theorem LField.flow_preserves_form (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1, V p.1 p.2) v w +
      Ω p (fderiv ℝ (fun q : ℝ × E => V q.1 q.2) p (0, v)) w +
      Ω p v (fderiv ℝ (fun q : ℝ × E => V q.1 q.2) p (0, w)) = 0) (t : ℝ) (x v w : E) :
    Ω (t, flow V t x) (fderiv ℝ (flow V t) x v) (fderiv ℝ (flow V t) x w) = Ω (0, x) v w := by
  obtain ⟨L, hL⟩ := hV.lipschitz
  let X : C(ℝ × E, E) := ⟨fun p => V p.1 p.2, hV.smooth.continuous⟩
  have hX : LipschitzWith L X := hL
  have hXs : ContDiff ℝ ∞ X := hV.smooth
  obtain ⟨N, hN⟩ := exists_nat_gt ((|t| + 1) * (L : ℝ))
  have hN0 : (0 : ℝ) < N :=
    lt_of_le_of_lt (mul_nonneg (by positivity) L.coe_nonneg) hN
  have hh : ‖t / (N : ℝ)‖ * L < 1 := by
    rw [norm_div, Real.norm_of_nonneg hN0.le, Real.norm_eq_abs, div_mul_eq_mul_div,
      div_lt_one hN0]
    calc |t| * L ≤ (|t| + 1) * L := by have := L.coe_nonneg; nlinarith
      _ < N := hN
  have hfl : (timeSteps X hX hXs hh 0 N : E → E) = flow V t := by
    funext y
    have hu := hV.flowFrom_isSol 0 y
    have he := timeSteps_eq_solution X hX hXs hh (flowFrom V 0 y)
      (hV.flowFrom_continuous 0 y) hu.2 0 N
    change timeSteps X hX hXs hh 0 N (flowFrom V 0 y 0) = _ at he
    rw [hu.1] at he
    rw [he]
    change flowFrom V 0 y (0 + (N : ℝ) * (t / N)) = flowFrom V 0 y t
    congr 1; field_simp; ring
  have hP := timeSteps_preserves_form X hX hXs Ω hΩ (fun p v w => hPDE p v w) hh 0 N x v w
  rw [hfl] at hP
  have ht : (0 : ℝ) + N * (t / N) = t := by field_simp; ring
  rw [ht] at hP
  exact hP

end smooth

end SymplecticPacking.Handle
