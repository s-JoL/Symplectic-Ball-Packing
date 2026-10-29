import Mathlib
import SymplecticPacking.Explicit
import SymplecticPacking.Return.Algebra
import OAI.Geometry.BallPacking.Moser.SymplecticFamily

/-!
# Flows of compactly supported fields

`sec:rtc`, flows of compactly supported smooth time-dependent fields (used for the transport `τ_T`
and the return flow `ψ_s`), and some smooth cutoff gadgets.

Explicitness: `flowFrom V t₀ y t` is the value at `t` of the *unique* global integral curve of
`V` with value `y` at time `t₀` (definite description `Explicit.the`); `flow V t = flowFrom V 0 · t`
and its inverse `flowInv V t = flowFrom V t · 0` (the backward flow). Joint smoothness is proved by
comparison with OAI's explicit Picard steps `timeSteps` (which only enter proofs).

Also here: the gauge-projected gradient `nperp` (equal to `n` on the unit sphere, and
Hermitian-orthogonal to `Z` everywhere on `Z ≠ 0`), the plateau functions `plateau`, and a
gluing criterion for smoothness of a cut-off field.
-/

noncomputable section

namespace SymplecticPacking.Return

open Filter Topology Set Metric
open scoped ContDiff NNReal

/-! ### Global flows of compactly supported fields -/

section flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A time-dependent field that is jointly `C^∞` and compactly supported in `(t, y)`. -/
structure CSField (V : ℝ → E → E) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => V p.1 p.2)
  compact : HasCompactSupport (fun p : ℝ × E => V p.1 p.2)

/-- `u` is a global integral curve of `V` with `u t₀ = y`. -/
def IsSolFrom (V : ℝ → E → E) (t₀ : ℝ) (y : E) (u : ℝ → E) : Prop :=
  u t₀ = y ∧ ∀ s, HasDerivAt u (V s (u s)) s

open Classical in
/-- The value at `t` of the unique global integral curve through `y` at time `t₀`
(definite description); `y` if there is none. -/
def flowFrom (V : ℝ → E → E) (t₀ : ℝ) (y : E) (t : ℝ) : E :=
  if hu : ∃! u : ℝ → E, IsSolFrom V t₀ y u then Explicit.the hu t else y

/-- The flow `φ_t` (from time `0`). -/
def flow (V : ℝ → E → E) (t : ℝ) (x : E) : E := flowFrom V 0 x t

/-- The backward flow `φ_t⁻¹` (from time `t` back to `0`). -/
def flowInv (V : ℝ → E → E) (t : ℝ) (y : E) : E := flowFrom V t y 0

variable {V : ℝ → E → E} (hV : CSField V)
include hV

theorem CSField.lipschitz : ∃ K : ℝ≥0, LipschitzWith K (fun p : ℝ × E => V p.1 p.2) :=
  hV.smooth.lipschitzWith_of_hasCompactSupport hV.compact (by simp)

theorem CSField.lipschitz_slice : ∃ K : ℝ≥0, ∀ t, LipschitzWith K (V t) := by
  obtain ⟨K, hK⟩ := hV.lipschitz
  refine ⟨K, fun t => LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  have := hK.dist_le_mul (t, y) (t, z)
  simpa [Prod.dist_eq] using this

theorem CSField.bound : ∃ C : ℝ≥0, ∀ t y, ‖V t y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hV.compact.exists_bound_of_continuous hV.smooth.continuous
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun t y => (hC (t, y)).trans (le_max_left _ _)⟩

/-- The field vanishes for `|t| ≥ R`. -/
theorem CSField.time_bound : ∃ R : ℝ, 0 < R ∧ ∀ t y, R ≤ |t| → V t y = 0 := by
  obtain ⟨R, hR⟩ := hV.compact.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0 + 1, by positivity, fun t y ht => ?_⟩
  apply image_eq_zero_of_notMem_tsupport (f := fun p : ℝ × E => V p.1 p.2) (x := (t, y))
  intro hmem
  have h1 := hR hmem
  rw [mem_closedBall_zero_iff] at h1
  have h2 : |t| ≤ ‖(t, y)‖ := by
    rw [Prod.norm_def]; exact (Real.norm_eq_abs t).symm.le.trans (le_max_left _ _)
  have := le_max_left R 0
  linarith

/-- Existence of global integral curves (Picard–Lindelöf on `[-R', R']`, constant outside). -/
theorem CSField.exists_sol (t₀ : ℝ) (x : E) [CompleteSpace E] :
    ∃ u : ℝ → E, IsSolFrom V t₀ x u := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  obtain ⟨C, hC⟩ := hV.bound
  obtain ⟨R, hR0, hRt⟩ := hV.time_bound
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
theorem CSField.sol_unique {t₀ : ℝ} {x : E} {u v : ℝ → E} (hu : IsSolFrom V t₀ x u)
    (hv : IsSolFrom V t₀ x v) : u = v := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  exact ODE_solution_unique_univ (s := fun _ => univ) (t₀ := t₀)
    (fun t => (hlip t).lipschitzOnWith) (fun t => ⟨hu.2 t, mem_univ _⟩)
    (fun t => ⟨hv.2 t, mem_univ _⟩) (hu.1.trans hv.1.symm)

variable [CompleteSpace E]

theorem CSField.existsUnique (t₀ : ℝ) (x : E) : ∃! u : ℝ → E, IsSolFrom V t₀ x u := by
  obtain ⟨u, hu⟩ := hV.exists_sol t₀ x
  exact ⟨u, hu, fun v hv => hV.sol_unique hv hu⟩

theorem CSField.flowFrom_eq {t₀ : ℝ} {x : E} {u : ℝ → E} (hu : IsSolFrom V t₀ x u) (t : ℝ) :
    flowFrom V t₀ x t = u t := by
  unfold flowFrom
  rw [dif_pos (hV.existsUnique t₀ x), Explicit.the_eq (hV.existsUnique t₀ x) hu]

theorem CSField.flowFrom_isSol (t₀ : ℝ) (x : E) : IsSolFrom V t₀ x (flowFrom V t₀ x) := by
  obtain ⟨u, hu⟩ := hV.exists_sol t₀ x
  have : flowFrom V t₀ x = u := funext fun t => hV.flowFrom_eq hu t
  rw [this]; exact hu

theorem CSField.flowFrom_self (t₀ : ℝ) (x : E) : flowFrom V t₀ x t₀ = x :=
  (hV.flowFrom_isSol t₀ x).1

theorem CSField.flowFrom_hasDerivAt (t₀ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun s => flowFrom V t₀ x s) (V t (flowFrom V t₀ x t)) t :=
  (hV.flowFrom_isSol t₀ x).2 t

theorem CSField.flowFrom_continuous (t₀ : ℝ) (x : E) : Continuous (flowFrom V t₀ x) :=
  continuous_iff_continuousAt.mpr fun t => (hV.flowFrom_hasDerivAt t₀ x t).continuousAt

/-- Cocycle property. -/
theorem CSField.flowFrom_flowFrom (t₀ t₁ : ℝ) (x : E) (t : ℝ) :
    flowFrom V t₁ (flowFrom V t₀ x t₁) t = flowFrom V t₀ x t :=
  hV.flowFrom_eq ⟨rfl, (hV.flowFrom_isSol t₀ x).2⟩ t

theorem CSField.flow_zero (x : E) : flow V 0 x = x := hV.flowFrom_self 0 x

theorem CSField.flow_hasDerivAt (x : E) (t : ℝ) :
    HasDerivAt (fun s => flow V s x) (V t (flow V t x)) t := hV.flowFrom_hasDerivAt 0 x t

theorem CSField.flowInv_flow (t : ℝ) (x : E) : flowInv V t (flow V t x) = x := by
  unfold flowInv flow
  rw [hV.flowFrom_flowFrom, hV.flowFrom_self]

theorem CSField.flow_flowInv (t : ℝ) (y : E) : flow V t (flowInv V t y) = y := by
  unfold flowInv flow
  rw [hV.flowFrom_flowFrom, hV.flowFrom_self]

theorem CSField.flow_injective (t : ℝ) : Function.Injective (flow V t) :=
  Function.LeftInverse.injective (hV.flowInv_flow t)

theorem CSField.flowInv_injective (t : ℝ) : Function.Injective (flowInv V t) :=
  Function.LeftInverse.injective (hV.flow_flowInv t)

/-- Equivariance: a continuous linear map commuting with the field commutes with the flow. -/
theorem CSField.flowFrom_map {L : E →L[ℝ] E} (hL : ∀ t y, V t (L y) = L (V t y)) (t₀ : ℝ)
    (x : E) (t : ℝ) : flowFrom V t₀ (L x) t = L (flowFrom V t₀ x t) := by
  have hs := hV.flowFrom_isSol t₀ x
  refine hV.flowFrom_eq (u := fun s => L (flowFrom V t₀ x s)) ⟨by simp [hs.1], fun s => ?_⟩ t
  rw [hL]
  exact L.hasFDerivAt.comp_hasDerivAt s (hs.2 s)

theorem CSField.flow_map {L : E →L[ℝ] E} (hL : ∀ t y, V t (L y) = L (V t y)) (t : ℝ) (x : E) :
    flow V t (L x) = L (flow V t x) := hV.flowFrom_map hL 0 x t

theorem CSField.flowInv_map {L : E →L[ℝ] E} (hL : ∀ t y, V t (L y) = L (V t y)) (t : ℝ)
    (y : E) : flowInv V t (L y) = L (flowInv V t y) := hV.flowFrom_map hL t y 0

/-- A first integral of the field is constant along the flow. -/
theorem CSField.flowFrom_firstIntegral {Q : E → ℝ} {Q' : E → E →L[ℝ] ℝ}
    (hQ : ∀ y, HasFDerivAt Q (Q' y) y) (hQV : ∀ t y, Q' y (V t y) = 0) (t₀ : ℝ) (x : E)
    (t : ℝ) : Q (flowFrom V t₀ x t) = Q x := by
  have hd : ∀ s, HasDerivAt (fun s => Q (flowFrom V t₀ x s)) 0 s := fun s => by
    have := (hQ _).comp_hasDerivAt s (hV.flowFrom_hasDerivAt t₀ x s)
    rwa [hQV] at this
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv)
    t t₀
  rw [this, hV.flowFrom_self]

theorem CSField.flow_firstIntegral {Q : E → ℝ} {Q' : E → E →L[ℝ] ℝ}
    (hQ : ∀ y, HasFDerivAt Q (Q' y) y) (hQV : ∀ t y, Q' y (V t y) = 0) (t : ℝ) (x : E) :
    Q (flow V t x) = Q x := hV.flowFrom_firstIntegral hQ hQV 0 x t

theorem CSField.flowInv_firstIntegral {Q : E → ℝ} {Q' : E → E →L[ℝ] ℝ}
    (hQ : ∀ y, HasFDerivAt Q (Q' y) y) (hQV : ∀ t y, Q' y (V t y) = 0) (t : ℝ) (y : E) :
    Q (flowInv V t y) = Q y := hV.flowFrom_firstIntegral hQ hQV t y 0

end flow

/-! #### Joint smoothness, by comparison with OAI's `timeSteps` -/

/-- A bounded smooth function equal to `t` on `[-R, R]`. -/
def clampR (R t : ℝ) : ℝ :=
  t * Real.smoothTransition (t + R + 1) * Real.smoothTransition (R + 1 - t)

theorem clampR_contDiff (R : ℝ) : ContDiff ℝ ∞ (clampR R) := by
  unfold clampR
  exact (contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).add contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem clampR_eq {R t : ℝ} (h1 : -R ≤ t) (h2 : t ≤ R) : clampR R t = t := by
  unfold clampR
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem abs_clampR_le {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : |clampR R t| ≤ R + 1 := by
  unfold clampR
  have a1 := Real.smoothTransition.nonneg (t + R + 1)
  have a2 := Real.smoothTransition.le_one (t + R + 1)
  have b1 := Real.smoothTransition.nonneg (R + 1 - t)
  have b2 := Real.smoothTransition.le_one (R + 1 - t)
  rcases le_or_gt t (-R - 1) with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; simp; linarith
  rcases le_or_gt (R + 1) t with ht' | ht'
  · rw [Real.smoothTransition.zero_of_nonpos (show R + 1 - t ≤ 0 by linarith)]; simp; linarith
  rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonneg b1]
  have : |t| ≤ R + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |t| * Real.smoothTransition (t + R + 1) * Real.smoothTransition (R + 1 - t)
      ≤ (R + 1) * 1 * 1 := by gcongr
    _ = R + 1 := by ring

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {V : ℝ → E → E} (hV : CSField V)
include hV

open OAI.PackingSufficiencySupport.Hamiltonian in
/-- On `[-R, R] × E` the flow and its inverse are given by OAI's `timeSteps`. -/
theorem CSField.exists_timeSteps {R : ℝ} (hR : 0 ≤ R) : ∃ Φ : ℝ → E ≃ₜ E,
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
theorem CSField.flow_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => flow V p.1 p.2) := by
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
theorem CSField.flowInv_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => flowInv V p.1 p.2) := by
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

theorem CSField.flow_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (flow V t) :=
  hV.flow_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem CSField.flowInv_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (flowInv V t) :=
  hV.flowInv_smooth.comp (contDiff_const.prodMk contDiff_id)

end smooth

/-! ### Reparametrised families `t ↦ φ_{σ(t)} ∘ φ₀`, for the Cartan lemma -/

/-- `σ_T(t) = T · S(t)`: smooth, `σ_T(0) = 0`, `σ_T(1) = T`, values in `[0, T]`. -/
def sigT (T t : ℝ) : ℝ := T * Real.smoothTransition t

theorem sigT_contDiff (T : ℝ) : ContDiff ℝ ∞ (sigT T) :=
  contDiff_const.mul Real.smoothTransition.contDiff

@[simp] theorem sigT_zero (T : ℝ) : sigT T 0 = 0 := by simp [sigT]

@[simp] theorem sigT_one (T : ℝ) : sigT T 1 = T := by simp [sigT]

theorem sigT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : sigT T t ∈ Icc 0 T :=
  ⟨mul_nonneg hT (Real.smoothTransition.nonneg t),
    mul_le_of_le_one_right hT (Real.smoothTransition.le_one t)⟩

theorem sigT_hasDerivAt (T t : ℝ) : HasDerivAt (sigT T) (deriv (sigT T) t) t :=
  ((sigT_contDiff T).differentiable (by simp) t).hasDerivAt

section family

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  {V : ℝ → F → F} (hV : CSField V)
include hV

/-- The family `t ↦ φ_{σ_T(t)} ∘ φ₀` is jointly smooth. -/
theorem CSField.family_smooth (T : ℝ) {φ₀ : E → F} (hφ₀ : ContDiff ℝ ∞ φ₀) :
    ContDiff ℝ ∞ (fun p : ℝ × E => flow V (sigT T p.1) (φ₀ p.2)) :=
  hV.flow_smooth.comp (((sigT_contDiff T).comp contDiff_fst).prodMk (hφ₀.comp contDiff_snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ F] in
/-- Its velocity is `σ_T'(t) V_{σ_T(t)}`. -/
theorem CSField.family_hasDerivAt (T : ℝ) (φ₀ : E → F) (t : ℝ) (x : E) :
    HasDerivAt (fun s => flow V (sigT T s) (φ₀ x))
      (deriv (sigT T) t • V (sigT T t) (flow V (sigT T t) (φ₀ x))) t :=
  (hV.flow_hasDerivAt (φ₀ x) (sigT T t)).scomp t (sigT_hasDerivAt T t)

end family

/-! ### Cutoffs and gluing -/

/-- A smooth plateau: `1` on `[a, b]`, `0` outside `(a', b')` (for `a' < a`, `b < b'`). -/
def plateau (a' a b b' x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a') / (a - a')) * Real.smoothTransition ((b' - x) / (b' - b))

theorem plateau_contDiff (a' a b b' : ℝ) : ContDiff ℝ ∞ (plateau a' a b b') := by
  unfold plateau
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem plateau_eq_one {a' a b b' x : ℝ} (ha : a' < a) (hb : b < b') (h1 : a ≤ x) (h2 : x ≤ b) :
    plateau a' a b b' x = 1 := by
  unfold plateau
  rw [Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith)), one_mul]

theorem plateau_eq_zero_left {a' a b b' x : ℝ} (ha : a' < a) (h : x ≤ a') :
    plateau a' a b b' x = 0 := by
  unfold plateau
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith)), zero_mul]

theorem plateau_eq_zero_right {a' a b b' x : ℝ} (hb : b < b') (h : b' ≤ x) :
    plateau a' a b b' x = 0 := by
  unfold plateau
  rw [Real.smoothTransition.zero_of_nonpos (x := (b' - x) / (b' - b))
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)), mul_zero]

theorem plateau_ne_zero {a' a b b' x : ℝ} (ha : a' < a) (hb : b < b')
    (h : plateau a' a b b' x ≠ 0) : a' < x ∧ x < b' := by
  constructor
  · by_contra hx; exact h (plateau_eq_zero_left ha (not_lt.mp hx))
  · by_contra hx; exact h (plateau_eq_zero_right hb (not_lt.mp hx))

/-- A smooth step: `0` for `x ≤ a`, `1` for `x ≥ b` (`a < b`). -/
def step (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

theorem step_contDiff (a b : ℝ) : ContDiff ℝ ∞ (step a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem step_eq_one {a b x : ℝ} (hab : a < b) (h : b ≤ x) : step a b x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

theorem step_eq_zero {a b x : ℝ} (hab : a < b) (h : x ≤ a) : step a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith))

/-- A function that vanishes near `p` is smooth at `p`. -/
theorem contDiffAt_of_eventually_zero {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} {p : X} (h : f =ᶠ[𝓝 p] 0) :
    ContDiffAt ℝ ∞ f p :=
  contDiffAt_const.congr_of_eventuallyEq h

/-! ### The gauge-projected gradient -/

/-- `n_⊥ = n − (Z†n/‖Z‖²) Z`: equal to `n` on the unit sphere, and `Z† n_⊥ = 0` for `Z ≠ 0`. -/
def nperp (Z : C3) : C3 := nvec Z - (herm Z (nvec Z) / (nsq Z : ℂ)) • Z

theorem nperp_unit {Z : C3} (hZ : nsq Z = 1) : nperp Z = nvec Z := by
  rw [nperp, n_horizontal Z hZ, zero_div, zero_smul, sub_zero]

theorem herm_nperp {Z : C3} (hZ : nsq Z ≠ 0) : herm Z (nperp Z) = 0 := by
  rw [nperp, sub_eq_add_neg, ← neg_smul, herm_add_right, herm_smul_right, herm_self]
  have : (nsq Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ
  field_simp
  ring

open ComplexConjugate in
theorem nperp_smul (Z : C3) {c : ℂ} (hc : conj c * c = 1) :
    nperp (c • Z) = conj c ^ 2 • nperp Z := by
  rw [nperp, nperp, nvec_smul Z hc, nsq_smul_of_unit Z hc, herm_smul_left, herm_smul_right,
    smul_sub, smul_smul, smul_smul]
  congr 1
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination (herm Z (nvec Z) * (nsq Z : ℂ)⁻¹ * conj c ^ 2) * hc

open ComplexConjugate in
theorem nperp_cubeRoot (Z : C3) : nperp (cubeRoot Z) = cubeRoot (nperp Z) := by
  have h1 : herm (cubeRoot Z) (cubeRoot (nvec Z)) = herm Z (nvec Z) := by
    simp only [herm, Fin.sum_univ_three, cubeRoot_zero, cubeRoot_one, cubeRoot_two, map_mul]
    linear_combination (conj (Z 0) * nvec Z 0) * conj_zeta_mul
  rw [nperp, nperp, nvec_cubeRoot, nsq_cubeRoot, h1]
  funext j
  fin_cases j <;> simp [cubeRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

end SymplecticPacking.Return
