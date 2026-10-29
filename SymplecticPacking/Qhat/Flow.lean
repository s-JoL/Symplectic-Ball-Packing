import Mathlib
import SymplecticPacking.Explicit
import OAI.Geometry.BallPacking.Moser.SymplecticFamily
import OAI.Geometry.BallPacking.DiskMaps.SmoothInverse

/-!
# The cut-off ambient flow of an ordinary path

`sec:pln-flow`: the source cutoff, the cut-off ambient field `W_t` and its
flow `φ_t`.

The five-segment ordinary path `𝔢` of `sec:pln-five` enters only through the interface
`OrdinaryPath` (the properties of `lem:pln-five-segment`, `lem:pln-data` and
`lem:pll-source-order` that `sec:pln-flow`–`sec:pln-ham` use); the data are bundled in `PathData`.

Explicitness: the inverse `𝔢_t⁻¹` on the image is the definite description of the unique
preimage, and the flow is the value at time `t` of the unique global integral curve
(`Explicit.the`). Smoothness of the flow is proved by comparing with OAI's explicit
`timeSteps` (any Lipschitz constant will do; it only enters proofs).
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Metric
open scoped ContDiff Real NNReal

/-! ### Conventions -/

/-- The open disk of *area* `P`, `D(P) = {π|z|² < P}`. -/
def areaDisk (P : ℝ) : Set ℂ := {z | π * ‖z‖ ^ 2 < P}

/-- The closed disk of area `P`, `D̄(P) = {π|z|² ≤ P}`. -/
def closedAreaDisk (P : ℝ) : Set ℂ := {z | π * ‖z‖ ^ 2 ≤ P}

theorem continuous_area : Continuous fun z : ℂ => π * ‖z‖ ^ 2 :=
  continuous_const.mul (continuous_norm.pow 2)

theorem isOpen_areaDisk (P : ℝ) : IsOpen (areaDisk P) :=
  isOpen_lt continuous_area continuous_const

theorem closedAreaDisk_eq (P : ℝ) (hP : 0 ≤ P) :
    closedAreaDisk P = closedBall (0 : ℂ) (Real.sqrt (P / π)) := by
  ext z
  simp only [closedAreaDisk, mem_ofPred_eq, mem_closedBall_zero_iff]
  rw [Real.le_sqrt (norm_nonneg _) (div_nonneg hP Real.pi_pos.le), le_div_iff₀ Real.pi_pos,
    mul_comm]

theorem areaDisk_eq (P : ℝ) :
    areaDisk P = ball (0 : ℂ) (Real.sqrt (P / π)) := by
  ext z
  simp only [areaDisk, mem_ofPred_eq, mem_ball_zero_iff]
  rw [Real.lt_sqrt (norm_nonneg _), lt_div_iff₀ Real.pi_pos, mul_comm]

theorem isCompact_closedAreaDisk (P : ℝ) : IsCompact (closedAreaDisk P) := by
  rcases le_or_gt 0 P with hP | hP
  · rw [closedAreaDisk_eq P hP]; exact isCompact_closedBall _ _
  · convert isCompact_empty
    ext z
    simp only [closedAreaDisk, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hP.trans_le (by positivity)

/-- The data of `sec:pln-five` used by `sec:pln-flow`–`sec:pln-ham`: the ordinary path `𝔢` (`path`), its spatial Jacobian
determinant `γ_t` (`gam`), the fibre area `h`, `e = e_q`, the source area `p†` (`pdag`), the
support area `P_supp = π R_supp²` (`Psupp`) and the shrinking factor `c = c_new`. -/
structure PathData where
  path : ℝ → ℂ → ℂ
  gam : ℝ → ℝ
  h : ℝ
  e : ℝ
  pdag : ℝ
  Psupp : ℝ
  c : ℝ

/-- **Interface to `sec:pln-five`.** The properties of the five-segment path that `sec:pln-flow`–`sec:pln-ham` use:
`lem:pln-five-segment` (a)–(c) (smooth on `ℝ × D(p†)`, `𝔢_t = id` for `t ≤ 0`, `𝔢_t = 𝔢_1` for
`t ≥ 1`, injective, spatial Jacobian determinant the constant `γ_t ∈ [c², 1]`, `γ_1 = 1`,
images in `D̄(P_supp)`), `lem:pln-data` (c) (`P_supp < h`), and
`lem:pll-source-order` (`p_+ = h - 15e/4 < p†`), with `e > 0` and `4e < h`. -/
structure OrdinaryPath (D : PathData) : Prop where
  e_pos : 0 < D.e
  four_e_lt_h : 4 * D.e < D.h
  pplus_lt_pdag : D.h - 15 * D.e / 4 < D.pdag
  Psupp_lt_h : D.Psupp < D.h
  c_pos : 0 < D.c
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.path p.1 p.2) (univ ×ˢ areaDisk D.pdag)
  eq_id : ∀ t ≤ 0, ∀ z ∈ areaDisk D.pdag, D.path t z = z
  eq_one : ∀ t, 1 ≤ t → ∀ z ∈ areaDisk D.pdag, D.path t z = D.path 1 z
  injOn : ∀ t, InjOn (D.path t) (areaDisk D.pdag)
  det : ∀ t, ∀ z ∈ areaDisk D.pdag,
    LinearMap.det (fderiv ℝ (D.path t) z : ℂ →ₗ[ℝ] ℂ) = D.gam t
  gam_smooth : ContDiff ℝ ∞ D.gam
  gam_ge : ∀ t, D.c ^ 2 ≤ D.gam t
  gam_one : D.gam 1 = 1
  image : ∀ t, ∀ z ∈ areaDisk D.pdag, π * ‖D.path t z‖ ^ 2 ≤ D.Psupp

/-! ### The source cutoff (`def:pll-cutoff`, `lem:pll-cutoff`) -/

/-- `p_on = h - 31e/8`. -/
def pon (D : PathData) : ℝ := D.h - 31 * D.e / 8

/-- `p_zero = h - 61e/16`. -/
def pzero (D : PathData) : ℝ := D.h - 61 * D.e / 16

/-- `χ(I) = 1 - S((I - p_on)/(p_zero - p_on))`. -/
def chiCut (D : PathData) (I : ℝ) : ℝ :=
  1 - Real.smoothTransition ((I - pon D) / (pzero D - pon D))

section cutoff
variable {D : PathData} (hD : OrdinaryPath D)
include hD

/-- **`lem:pll-cutoff`.** `h - 4e < p_on < p_zero < p_+ < p†`. -/
theorem pon_bounds :
    D.h - 4 * D.e < pon D ∧ pon D < pzero D ∧ pzero D < D.h - 15 * D.e / 4 ∧
      D.h - 15 * D.e / 4 < D.pdag := by
  have := hD.e_pos
  simp only [pon, pzero]
  refine ⟨?_, ?_, ?_, hD.pplus_lt_pdag⟩ <;> linarith

theorem pon_pos : 0 < pon D := by
  have := hD.e_pos; have := hD.four_e_lt_h; unfold pon; linarith

theorem pzero_lt_pdag : pzero D < D.pdag := by
  obtain ⟨-, -, h3, h4⟩ := pon_bounds hD; linarith

theorem pon_lt_pdag : pon D < D.pdag := by
  obtain ⟨-, h2, -, -⟩ := pon_bounds hD; linarith [pzero_lt_pdag hD]

theorem chiCut_eq_one {I : ℝ} (hI : I ≤ pon D) : chiCut D I = 1 := by
  have h2 := (pon_bounds hD).2.1
  unfold chiCut
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith)), sub_zero]

theorem chiCut_eq_zero {I : ℝ} (hI : pzero D ≤ I) : chiCut D I = 0 := by
  have h2 := (pon_bounds hD).2.1
  unfold chiCut
  rw [Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith)),
    sub_self]

end cutoff

theorem chiCut_contDiff (D : PathData) : ContDiff ℝ ∞ (chiCut D) := by
  unfold chiCut
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

/-! ### Generic flows of compactly supported fields -/

section flow

/-- Hypotheses on a time-dependent field `V` on `ℂ`: jointly `C^∞`, compactly supported, and
zero for `t ∉ (0,1)`. -/
structure GoodField (V : ℝ → ℂ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => V p.1 p.2)
  compact : HasCompactSupport (fun p : ℝ × ℂ => V p.1 p.2)
  time : ∀ t y, (t ≤ 0 ∨ 1 ≤ t) → V t y = 0

/-- `u` is a global integral curve of `V` starting at `y`. -/
def IsSol (V : ℝ → ℂ → ℂ) (y : ℂ) (u : ℝ → ℂ) : Prop :=
  u 0 = y ∧ ∀ s, HasDerivAt u (V s (u s)) s

open Classical in
/-- The flow of `V`: the value at time `t` of the unique global integral curve through `y` at
time `0` (definite description); `y` if there is none. -/
def flowOf (V : ℝ → ℂ → ℂ) (t : ℝ) (y : ℂ) : ℂ :=
  if hu : ∃! u : ℝ → ℂ, IsSol V y u then Explicit.the hu t else y

variable {V : ℝ → ℂ → ℂ} (hV : GoodField V)
include hV

theorem GoodField.lipschitz : ∃ K : ℝ≥0, LipschitzWith K (fun p : ℝ × ℂ => V p.1 p.2) :=
  hV.smooth.lipschitzWith_of_hasCompactSupport hV.compact (by simp)

theorem GoodField.lipschitz_slice : ∃ K : ℝ≥0, ∀ t, LipschitzWith K (V t) := by
  obtain ⟨K, hK⟩ := hV.lipschitz
  refine ⟨K, fun t => LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  have := hK.dist_le_mul (t, y) (t, z)
  simpa [Prod.dist_eq] using this

theorem GoodField.bound : ∃ C : ℝ≥0, ∀ t y, ‖V t y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hV.compact.exists_bound_of_continuous hV.smooth.continuous
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun t y => (hC (t, y)).trans (le_max_left _ _)⟩

/-- Existence of global integral curves (Picard–Lindelöf on `[0,1]`, constant outside). -/
theorem GoodField.exists_sol (x : ℂ) : ∃ u : ℝ → ℂ, IsSol V x u := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  obtain ⟨C', hC'⟩ := hV.bound
  have hPL : IsPicardLindelof (fun t y => V t y) (tmin := 0) (tmax := 1)
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ x C' 0 C' K := by
    refine ⟨fun t _ => (hlip t).lipschitzOnWith, fun y _ => ?_, fun t _ y _ => hC' _ _, ?_⟩
    · exact (hV.smooth.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · simp
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  set γ : ℝ → ℂ := fun t => α (max 0 (min t 1)) with hγdef
  have hγα : ∀ t ∈ Icc (0 : ℝ) 1, γ t = α t := by
    intro t ht; simp [hγdef, min_eq_left ht.2, max_eq_right ht.1]
  have hγ0 : γ 0 = x := by rw [hγα 0 (left_mem_Icc.mpr zero_le_one)]; exact hα0
  refine ⟨γ, hγ0, fun t => ?_⟩
  have hlo : ∀ s ≤ 0, γ s = x := by
    intro s hs; simp only [hγdef]; rw [max_eq_left (by simp [hs.trans zero_le_one, hs])]
    exact hα0
  have hhi : ∀ s ≥ 1, γ s = α 1 := by
    intro s hs; simp [hγdef, min_eq_right hs]
  have hVlo : ∀ s ≤ 0, ∀ y, V s y = 0 := fun s hs y => hV.time s y (Or.inl hs)
  have hVhi : ∀ s ≥ 1, ∀ y, V s y = 0 := fun s hs y => hV.time s y (Or.inr hs)
  have hIcc : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (V s (γ s)) (Icc 0 1) s := by
    intro s hs
    rw [hγα s hs]
    exact (hα s hs).congr (fun r hr => hγα r hr) (hγα s hs)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [hVlo t ht.le]
    apply (hasDerivAt_const t x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs using hlo s hs.le
  · rw [hγ0, hVlo 0 le_rfl x]
    have hleft : HasDerivWithinAt γ 0 (Iic 0) 0 :=
      (hasDerivWithinAt_const 0 (Iic 0) x).congr (fun s hs => hlo s hs) hγ0
    have hright : HasDerivWithinAt γ 0 (Ici 0) 0 := by
      have h := hIcc 0 (left_mem_Icc.mpr zero_le_one)
      rw [hγ0, hVlo 0 le_rfl x] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one)
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · exact (hIcc t ⟨ht.le, ht1.le⟩).hasDerivAt (Icc_mem_nhds ht ht1)
    · rw [hhi 1 le_rfl, hVhi 1 le_rfl]
      have hright : HasDerivWithinAt γ 0 (Ici 1) 1 :=
        (hasDerivWithinAt_const 1 (Ici 1) (α 1)).congr (fun s hs => hhi s hs) (hhi 1 le_rfl)
      have hleft : HasDerivWithinAt γ 0 (Iic 1) 1 := by
        have h := hIcc 1 (right_mem_Icc.mpr zero_le_one)
        rw [hVhi 1 le_rfl] at h
        exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE zero_lt_one)
      have := hleft.union hright
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [hVhi t ht1.le]
      apply (hasDerivAt_const t (α 1)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht1] with s hs using hhi s hs.le

/-- Uniqueness of global integral curves. -/
theorem GoodField.sol_unique {x : ℂ} {u v : ℝ → ℂ} (hu : IsSol V x u) (hv : IsSol V x v) :
    u = v := by
  obtain ⟨K, hlip⟩ := hV.lipschitz_slice
  exact ODE_solution_unique_univ (s := fun _ => univ) (t₀ := 0)
    (fun t => (hlip t).lipschitzOnWith) (fun t => ⟨hu.2 t, mem_univ _⟩)
    (fun t => ⟨hv.2 t, mem_univ _⟩) (hu.1.trans hv.1.symm)

theorem GoodField.existsUnique (x : ℂ) : ∃! u : ℝ → ℂ, IsSol V x u := by
  obtain ⟨u, hu⟩ := hV.exists_sol x
  exact ⟨u, hu, fun v hv => hV.sol_unique hv hu⟩

theorem GoodField.flowOf_eq {x : ℂ} {u : ℝ → ℂ} (hu : IsSol V x u) (t : ℝ) :
    flowOf V t x = u t := by
  unfold flowOf
  rw [dite_eq_left_of_eq_true (eq_true (hV.existsUnique x)), Explicit.the_eq (hV.existsUnique x) hu]

theorem GoodField.flowOf_isSol (x : ℂ) : IsSol V x (fun t => flowOf V t x) := by
  obtain ⟨u, hu⟩ := hV.exists_sol x
  have : (fun t => flowOf V t x) = u := funext fun t => hV.flowOf_eq hu t
  rw [this]; exact hu

theorem GoodField.flowOf_zero (x : ℂ) : flowOf V 0 x = x := (hV.flowOf_isSol x).1

theorem GoodField.flowOf_of_nonpos (x : ℂ) {t : ℝ} (ht : t ≤ 0) : flowOf V t x = x := by
  have hu := hV.flowOf_isSol x
  have hc : ContinuousOn (fun s => flowOf V s x) (Icc t 0) :=
    fun s _ => (hu.2 s).continuousAt.continuousWithinAt
  have key := constant_of_has_deriv_right_zero hc (fun s hs => by
    have := (hu.2 s).hasDerivWithinAt (s := Ici s)
    rwa [hV.time s _ (Or.inl hs.2.le)] at this) 0 (right_mem_Icc.mpr ht)
  rw [← key]; exact hV.flowOf_zero x

theorem GoodField.flowOf_of_one_le (x : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    flowOf V t x = flowOf V 1 x := by
  have hu := hV.flowOf_isSol x
  have hc : ContinuousOn (fun s => flowOf V s x) (Icc 1 t) :=
    fun s _ => (hu.2 s).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hc (fun s hs => by
    have := (hu.2 s).hasDerivWithinAt (s := Ici s)
    rwa [hV.time s _ (Or.inr hs.1)] at this) t (right_mem_Icc.mpr ht)

/-- A point at which the field vanishes for all times is fixed by the flow. -/
theorem GoodField.flowOf_fixed {x : ℂ} (hx : ∀ t, V t x = 0) (t : ℝ) : flowOf V t x = x :=
  hV.flowOf_eq (u := fun _ => x) ⟨rfl, fun s => by rw [hx s]; exact hasDerivAt_const s x⟩ t

/-! #### Comparison with OAI's explicit `timeSteps` -/

/-- A bounded smooth function equal to `t` on `[-1, 2]`. -/
def clampT (t : ℝ) : ℝ := t * Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t)

omit hV in
theorem clampT_contDiff : ContDiff ℝ ∞ clampT := by
  unfold clampT
  exact (contDiff_id.mul (Real.smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

omit hV in
theorem clampT_eq {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 2) : clampT t = t := by
  unfold clampT
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

omit hV in
theorem abs_clampT_le (t : ℝ) : |clampT t| ≤ 3 := by
  unfold clampT
  have a1 := Real.smoothTransition.nonneg (t + 2)
  have a2 := Real.smoothTransition.le_one (t + 2)
  have b1 := Real.smoothTransition.nonneg (3 - t)
  have b2 := Real.smoothTransition.le_one (3 - t)
  rcases le_or_gt t (-2) with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  rcases le_or_gt 3 t with ht' | ht'
  · rw [Real.smoothTransition.zero_of_nonpos (show 3 - t ≤ 0 by linarith)]; simp
  rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonneg b1]
  have : |t| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |t| * Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t)
      ≤ 3 * 1 * 1 := by gcongr
    _ = 3 := by ring

open OAI.PackingSufficiencySupport.Hamiltonian in
/-- On `(-1, 2) × ℂ` the flow and its inverse are given by OAI's `timeSteps`; hence the flow is
jointly `C^∞` there, each `φ_t` (`t ∈ (-1,2)`) is a homeomorphism with jointly `C^∞` inverse. -/
theorem GoodField.exists_timeSteps : ∃ Φ : ℝ → ℂ ≃ₜ ℂ,
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => Φ p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => (Φ p.1).symm p.2) ∧
    ∀ t ∈ Icc (-1 : ℝ) 2, ∀ x, Φ t x = flowOf V t x := by
  obtain ⟨L, hL⟩ := hV.lipschitz
  let X : C(ℝ × ℂ, ℂ) := ⟨fun p => V p.1 p.2, hV.smooth.continuous⟩
  have hX : LipschitzWith L X := hL
  have hXs : ContDiff ℝ ∞ X := hV.smooth
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (L : ℝ))
  have hN0 : (0 : ℝ) < N := by have := L.coe_nonneg; linarith
  let hf : ℝ → ℝ := fun t => clampT t / N
  have hh (t : ℝ) : ‖hf t‖ * L < 1 := by
    change ‖clampT t / (N : ℝ)‖ * L < 1
    rw [norm_div, Real.norm_of_nonneg hN0.le, Real.norm_eq_abs, div_mul_eq_mul_div,
      div_lt_one hN0]
    calc |clampT t| * L ≤ 3 * L := by gcongr; exact abs_clampT_le t
      _ < N := hN
  have hhs : ContDiff ℝ ∞ hf := clampT_contDiff.div_const _
  let Φ : ℝ → ℂ ≃ₜ ℂ := fun t => timeSteps X hX hXs (hh t) 0 N
  have hsm := timeSteps_variable_smooth X hX hXs hhs (contDiff_const (c := (0 : ℝ))) hh N
  refine ⟨Φ, hsm.1, hsm.2, fun t ht x => ?_⟩
  have hu := hV.flowOf_isSol x
  have he := timeSteps_eq_solution X hX hXs (hh t) (fun s => flowOf V s x)
    (continuous_iff_continuousAt.mpr fun s => (hu.2 s).continuousAt) hu.2 0 N
  change timeSteps X hX hXs (hh t) 0 N (flowOf V 0 x) = _ at he
  rw [hV.flowOf_zero x] at he
  change timeSteps X hX hXs (hh t) 0 N x = flowOf V t x
  rw [he]
  congr 1
  change 0 + (N : ℝ) * (clampT t / N) = t
  rw [clampT_eq ht.1 ht.2]; field_simp; ring

/-- **Joint smoothness of the flow.** -/
theorem GoodField.flowOf_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => flowOf V p.1 p.2) := by
  obtain ⟨Φ, hΦ, -, hΦe⟩ := hV.exists_timeSteps
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  rcases lt_or_ge t 0 with ht | ht
  · apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds (show (t, x) ∈ Prod.fst ⁻¹'
      Iio (0 : ℝ) from ht)] with p hp
    exact hV.flowOf_of_nonpos p.2 (le_of_lt hp)
  rcases lt_or_ge t (3 / 2) with ht' | ht'
  · have hO : Prod.fst ⁻¹' Ioo (-1 : ℝ) 2 ∈ 𝓝 ((t, x) : ℝ × ℂ) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨by linarith, by linarith⟩
    apply hΦ.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hO] with p hp
    exact (hΦe p.1 ⟨hp.1.le, hp.2.le⟩ p.2).symm
  · have hO : Prod.fst ⁻¹' Ioi (1 : ℝ) ∈ 𝓝 ((t, x) : ℝ × ℂ) :=
      (isOpen_Ioi.preimage continuous_fst).mem_nhds (show (1 : ℝ) < t by linarith)
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Φ 1 p.2) :=
      hΦ.comp (contDiff_const.prodMk contDiff_snd)
    apply h1.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hO] with p hp
    rw [hΦe 1 ⟨by norm_num, by norm_num⟩, hV.flowOf_of_one_le p.2 (le_of_lt hp)]

theorem GoodField.flowOf_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (flowOf V t) :=
  hV.flowOf_smooth.comp (contDiff_const.prodMk contDiff_id)

/-- Each `φ_t` is a homeomorphism with `C^∞` inverse (as a function of `y`). -/
theorem GoodField.flowOf_homeomorph (t : ℝ) : ∃ Ψ : ℂ ≃ₜ ℂ, (Ψ : ℂ → ℂ) = flowOf V t ∧
    ContDiff ℝ ∞ Ψ.symm := by
  obtain ⟨Φ, -, hΦi, hΦe⟩ := hV.exists_timeSteps
  have hs (s : ℝ) : ContDiff ℝ ∞ (Φ s).symm := hΦi.comp (contDiff_const.prodMk contDiff_id)
  rcases lt_or_ge t 0 with ht | ht
  · exact ⟨Homeomorph.refl ℂ, funext fun x => (hV.flowOf_of_nonpos x ht.le).symm, contDiff_id⟩
  rcases le_or_gt t 1 with ht' | ht'
  · exact ⟨Φ t, funext fun x => hΦe t ⟨by linarith, by linarith⟩ x, hs t⟩
  · refine ⟨Φ 1, funext fun x => ?_, hs 1⟩
    rw [hΦe 1 ⟨by norm_num, by norm_num⟩, hV.flowOf_of_one_le x ht'.le]

theorem GoodField.flowOf_bijective (t : ℝ) : Function.Bijective (flowOf V t) := by
  obtain ⟨Ψ, hΨ, -⟩ := hV.flowOf_homeomorph t
  rw [← hΨ]; exact Ψ.bijective

theorem GoodField.flowOf_det_ne_zero (t : ℝ) (x : ℂ) :
    LinearMap.det (fderiv ℝ (flowOf V t) x : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
  obtain ⟨Ψ, hΨ, hΨs⟩ := hV.flowOf_homeomorph t
  have hf := (hV.flowOf_slice_smooth t).differentiable (by simp)
  have hg := hΨs.differentiable (by simp)
  have hid : flowOf V t ∘ Ψ.symm = id := by
    rw [← hΨ]; funext y; exact Ψ.apply_symm_apply y
  have h := fderiv_comp (Ψ x) (hf (Ψ.symm (Ψ x))) (hg (Ψ x))
  rw [hid, fderiv_id, Ψ.symm_apply_apply] at h
  intro h0
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ => LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)) h
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at h1
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, h0, zero_mul] at h1
  exact one_ne_zero h1

/-- The fderiv of the flow is jointly continuous. -/
theorem GoodField.continuous_flowOf_fderiv :
    Continuous (fun p : ℝ × ℂ => fderiv ℝ (flowOf V p.1) p.2) := by
  have h2 := ContDiff.fderiv (f := fun (q : ℝ × ℂ) (y : ℂ) => flowOf V q.1 y) (g := fun q => q.2)
    (hV.flowOf_smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (m := ∞) (n := ∞) (by simp)
  exact h2.continuous

theorem GoodField.flowOf_det_pos (t : ℝ) (x : ℂ) :
    0 < LinearMap.det (fderiv ℝ (flowOf V t) x : ℂ →ₗ[ℝ] ℂ) := by
  set d : ℝ → ℝ := fun s => LinearMap.det (fderiv ℝ (flowOf V s) x : ℂ →ₗ[ℝ] ℂ)
  have hdc : Continuous d := by
    have hdet : Continuous fun L : ℂ →L[ℝ] ℂ => LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) :=
      ContinuousLinearMap.continuous_det
    exact hdet.comp (hV.continuous_flowOf_fderiv.comp (continuous_id.prodMk continuous_const))
  have hd0 : ∀ s ≤ 0, d s = 1 := by
    intro s hs
    have : flowOf V s = id := funext fun y => hV.flowOf_of_nonpos y hs
    simp only [d, this, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rcases le_or_gt t 0 with ht | ht
  · rw [show LinearMap.det (fderiv ℝ (flowOf V t) x : ℂ →ₗ[ℝ] ℂ) = d t from rfl, hd0 t ht]
    exact one_pos
  by_contra hneg
  push Not at hneg
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc' ht.le hdc.continuousOn
    (show (0 : ℝ) ∈ Icc (d t) (d 0) from ⟨hneg, by rw [hd0 0 le_rfl]; exact zero_le_one⟩)
  exact hV.flowOf_det_ne_zero s x hs

end flow

/-! ### Generic facts -/

/-- A bijection fixing every point outside `A` maps every `S ⊇ A` onto itself. -/
theorem image_eq_of_fixed {f : ℂ → ℂ} (hf : Function.Bijective f) {A S : Set ℂ}
    (hfix : ∀ y ∉ A, f y = y) (hAS : A ⊆ S) : f '' S = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra hy
    have h1 : f (f x) = f x := hfix _ (fun h => hy (hAS h))
    rw [hf.1 h1] at hy
    exact hy hx
  · intro hy
    obtain ⟨x, rfl⟩ := hf.2 y
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    rw [hfix x (fun h => hx (hAS h))] at hy
    exact hx hy

/-- A linear endomorphism of `ℂ` with nonzero determinant is invertible. -/
theorem isInvertible_of_det_ne_zero (L : ℂ →L[ℝ] ℂ) (h : LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) ≠ 0) :
    L.IsInvertible := by
  have hu : IsUnit (L : ℂ →ₗ[ℝ] ℂ) := (LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit h)
  have hb := (Module.End.isUnit_iff _).mp hu
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2), rfl⟩

/-! ### The ambient field and flow (`sec:pln-flow`, `lem:pln-ambient-flow`) -/

/-- The velocity `∂_t 𝔢_t(z)`. -/
def ordVel (D : PathData) (t : ℝ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun p : ℝ × ℂ => D.path p.1 p.2) (t, z) (1, 0)

open Classical in
/-- `𝔢_t⁻¹(y)`: the unique preimage of `y` in `D(p†)` (definite description), `0` if none. -/
def ordInv (D : PathData) (t : ℝ) (y : ℂ) : ℂ :=
  if hu : ∃! z, z ∈ areaDisk D.pdag ∧ D.path t z = y then Explicit.the hu else 0

open Classical in
/-- **`sec:pln-flow`.** The cut-off ambient field
`W_t(y) = χ(π|𝔢_t⁻¹ y|²) (∂_t 𝔢_t)(𝔢_t⁻¹ y)` on `𝒪 = {y ∈ 𝔢_t(D(p†))}`, `0` otherwise. -/
def ambientField (D : PathData) (t : ℝ) (y : ℂ) : ℂ :=
  if y ∈ D.path t '' areaDisk D.pdag then
    chiCut D (π * ‖ordInv D t y‖ ^ 2) • ordVel D t (ordInv D t y)
  else 0

/-- **`sec:pln-flow`.** The flow `φ_t` of `W_t`, `φ_0 = id`. -/
def ambientFlow (D : PathData) : ℝ → ℂ → ℂ := flowOf (ambientField D)

section ambient
variable {D : PathData} (hD : OrdinaryPath D)
include hD

theorem ordInv_eq {t : ℝ} {z : ℂ} (hz : z ∈ areaDisk D.pdag) : ordInv D t (D.path t z) = z := by
  have hu : ∃! w, w ∈ areaDisk D.pdag ∧ D.path t w = D.path t z :=
    ⟨z, ⟨hz, rfl⟩, fun w hw => hD.injOn t hw.1 hz hw.2⟩
  unfold ordInv
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact Explicit.the_eq hu ⟨hz, rfl⟩

theorem path_contDiffAt {t : ℝ} {z : ℂ} (hz : z ∈ areaDisk D.pdag) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => D.path p.1 p.2) (t, z) :=
  hD.smooth.contDiffAt (((isOpen_univ (X := ℝ)).prod (isOpen_areaDisk _)).mem_nhds ⟨mem_univ _, hz⟩)

theorem path_hasDerivAt {t : ℝ} {z : ℂ} (hz : z ∈ areaDisk D.pdag) :
    HasDerivAt (fun s => D.path s z) (ordVel D t z) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, z) : ℝ × ℂ)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  exact ((path_contDiffAt hD hz).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t h1

theorem path_slice_hasFDerivAt {t : ℝ} {z : ℂ} (hz : z ∈ areaDisk D.pdag) :
    HasFDerivAt (D.path t) ((fderiv ℝ (fun p : ℝ × ℂ => D.path p.1 p.2) (t, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℂ)) z :=
  ((path_contDiffAt hD hz).differentiableAt (by simp)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right t z)

/-- `∂_t 𝔢_t = 0` for `t ∉ (0,1)`. -/
theorem ordVel_eq_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) {z : ℂ} (hz : z ∈ areaDisk D.pdag) :
    ordVel D t z = 0 := by
  have hd := path_hasDerivAt hD (t := t) hz
  rcases ht with ht | ht
  · have hc : HasDerivWithinAt (fun s => D.path s z) 0 (Iic t) t :=
      (hasDerivWithinAt_const t (Iic t) z).congr (fun s hs => hD.eq_id s (hs.trans ht) z hz)
        (hD.eq_id t ht z hz)
    exact (uniqueDiffWithinAt_Iic t).eq_deriv _ hd.hasDerivWithinAt hc
  · have hc : HasDerivWithinAt (fun s => D.path s z) 0 (Ici t) t :=
      (hasDerivWithinAt_const t (Ici t) (D.path 1 z)).congr
        (fun s hs => hD.eq_one s (ht.trans hs) z hz) (hD.eq_one t ht z hz)
    exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivWithinAt hc

theorem ordVel_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ordVel D p.1 p.2) (univ ×ˢ areaDisk D.pdag) := by
  have hO : IsOpen ((univ : Set ℝ) ×ˢ areaDisk D.pdag) := isOpen_univ.prod (isOpen_areaDisk _)
  have h := hD.smooth.fderiv_of_isOpen hO (m := ∞) (by simp)
  exact h.clm_apply contDiffOn_const

theorem ambientField_apply {t : ℝ} {z : ℂ} (hz : z ∈ areaDisk D.pdag) :
    ambientField D t (D.path t z) = chiCut D (π * ‖z‖ ^ 2) • ordVel D t z := by
  unfold ambientField
  rw [if_pos ⟨z, hz, rfl⟩, ordInv_eq hD hz]

omit hD in
theorem ambientField_eq_zero_of_not_mem {t : ℝ} {y : ℂ}
    (hy : y ∉ D.path t '' areaDisk D.pdag) : ambientField D t y = 0 := by
  unfold ambientField; rw [if_neg hy]

/-- `W_t(y) = 0` for `π|y|² > P_supp`. -/
theorem ambientField_eq_zero_of_Psupp_lt {t : ℝ} {y : ℂ} (hy : D.Psupp < π * ‖y‖ ^ 2) :
    ambientField D t y = 0 := by
  apply ambientField_eq_zero_of_not_mem
  rintro ⟨z, hz, rfl⟩
  exact absurd (hD.image t z hz) (not_le.mpr hy)

theorem ambientField_eq_zero_of_time {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (y : ℂ) :
    ambientField D t y = 0 := by
  by_cases hy : y ∈ D.path t '' areaDisk D.pdag
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [ambientField_apply hD hz, ordVel_eq_zero hD ht hz, smul_zero]
  · exact ambientField_eq_zero_of_not_mem hy

/-- The graph map `(t, z) ↦ (t, 𝔢_t z)`. -/
def graphMap (D : PathData) (p : ℝ × ℂ) : ℝ × ℂ := (p.1, D.path p.1 p.2)

theorem closedAreaDisk_pzero_subset : closedAreaDisk (pzero D) ⊆ areaDisk D.pdag :=
  fun z hz => lt_of_le_of_lt hz (pzero_lt_pdag hD)

/-- **`lem:pln-ambient-flow` (a).** `W` is a good field: jointly `C^∞`, compactly supported, zero for
`t ∉ (0,1)`. -/
theorem ambientField_good : GoodField (ambientField D) := by
  set Ω : Set (ℝ × ℂ) := univ ×ˢ areaDisk D.pdag with hΩdef
  have hΩ : IsOpen Ω := isOpen_univ.prod (isOpen_areaDisk _)
  have hF : ContDiffOn ℝ ∞ (graphMap D) Ω := contDiffOn_fst.prodMk hD.smooth
  have hFi : InjOn (graphMap D) Ω := by
    rintro ⟨t, x⟩ hp ⟨s, y⟩ hq he
    have ht : t = s := congrArg Prod.fst he
    subst ht
    exact Prod.ext rfl (hD.injOn t hp.2 hq.2 (congrArg Prod.snd he))
  have hFd : ∀ p ∈ Ω, (fderiv ℝ (graphMap D) p).IsInvertible := by
    rintro ⟨t, z⟩ hp
    have hd := (path_contDiffAt hD (t := t) hp.2).differentiableAt (n := ∞) (by simp)
    have hFd' : fderiv ℝ (graphMap D) (t, z) =
        (ContinuousLinearMap.fst ℝ ℝ ℂ).prod
          (fderiv ℝ (fun p : ℝ × ℂ => D.path p.1 p.2) (t, z)) :=
      (hasFDerivAt_fst.prodMk hd.hasFDerivAt).fderiv
    rw [hFd']
    apply OAI.PackingSufficiencySupport.Hamiltonian.clockGraph_linear_invertible
    rw [← (path_slice_hasFDerivAt hD hp.2).fderiv]
    apply isInvertible_of_det_ne_zero
    rw [hD.det t z hp.2]
    exact (lt_of_lt_of_le (pow_pos hD.c_pos 2) (hD.gam_ge t)).ne'
  obtain ⟨hU, hg, hleft, hright⟩ :=
    OAI.PackingSufficiencySupport.Hamiltonian.smooth_inverse_on hΩ hF hFi hFd
  set g := Function.invFunOn (graphMap D) Ω
  -- on the image, `ordInv` is the second component of `g`
  have hgΩ : ∀ p ∈ graphMap D '' Ω, g p ∈ Ω := fun p hp => Function.invFunOn_mem hp
  have hg1 : ∀ p ∈ graphMap D '' Ω, (g p).1 = p.1 := fun p hp => by
    have h := congrArg Prod.fst (hright p hp); exact h
  have hord : ∀ p ∈ graphMap D '' Ω, ordInv D p.1 p.2 = (g p).2 := by
    intro p hp
    have h2 : D.path (g p).1 (g p).2 = p.2 := by
      have h := congrArg Prod.snd (hright p hp); exact h
    rw [hg1 p hp] at h2
    rw [← h2]
    exact ordInv_eq hD (hgΩ p hp).2
  have hmem : ∀ p : ℝ × ℂ, p ∈ graphMap D '' Ω ↔ p.2 ∈ D.path p.1 '' areaDisk D.pdag := by
    rintro ⟨t, y⟩
    constructor
    · rintro ⟨⟨s, z⟩, hz, he⟩
      have : s = t := congrArg Prod.fst he
      subst this
      exact ⟨z, hz.2, congrArg Prod.snd he⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨(t, z), ⟨mem_univ _, hz⟩, by simp [graphMap, he]⟩
  -- smoothness on the open image
  have hWon : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ambientField D p.1 p.2) (graphMap D '' Ω) := by
    have hχ : ContDiff ℝ ∞ (fun z : ℂ => chiCut D (π * ‖z‖ ^ 2)) :=
      (chiCut_contDiff D).comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hcomp : ContDiffOn ℝ ∞
        (fun p : ℝ × ℂ => chiCut D (π * ‖(g p).2‖ ^ 2) • ordVel D p.1 (g p).2)
        (graphMap D '' Ω) := by
      refine (hχ.comp_contDiffOn hg.snd).smul ?_
      have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ((p.1, (g p).2) : ℝ × ℂ)) (graphMap D '' Ω) :=
        contDiffOn_fst.prodMk hg.snd
      exact (ordVel_contDiffOn hD).comp h2 fun p hp => ⟨mem_univ _, (hgΩ p hp).2⟩
    refine hcomp.congr fun p hp => ?_
    have hp' := (hmem p).mp hp
    simp only [ambientField, if_pos hp', hord p hp]
  -- the support is contained in a compact subset of the image
  set K : Set (ℝ × ℂ) := graphMap D '' (Icc 0 1 ×ˢ closedAreaDisk (pzero D)) with hKdef
  have hKsub : Icc 0 1 ×ˢ closedAreaDisk (pzero D) ⊆ Ω :=
    fun p hp => ⟨mem_univ _, closedAreaDisk_pzero_subset hD hp.2⟩
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedAreaDisk _)).image_of_continuousOn
      (hF.continuousOn.mono hKsub)
  have hKU : K ⊆ graphMap D '' Ω := image_mono hKsub
  have hzero : ∀ p ∉ K, ambientField D p.1 p.2 = 0 := by
    rintro ⟨t, y⟩ hp
    by_cases hy : y ∈ D.path t '' areaDisk D.pdag
    · obtain ⟨z, hz, rfl⟩ := hy
      change ambientField D t (D.path t z) = 0
      rw [ambientField_apply hD hz]
      by_cases hz0 : z ∈ closedAreaDisk (pzero D)
      · have ht : t ∉ Icc (0 : ℝ) 1 := fun ht => hp ⟨(t, z), ⟨ht, hz0⟩, rfl⟩
        rw [ordVel_eq_zero hD ?_ hz, smul_zero]
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with ht | ht
        · exact Or.inl ht.le
        · exact Or.inr ht.le
      · rw [chiCut_eq_zero hD (le_of_lt (not_le.mp hz0)), zero_smul]
    · exact ambientField_eq_zero_of_not_mem hy
  refine ⟨?_, HasCompactSupport.intro hK hzero, fun t y ht => ambientField_eq_zero_of_time hD ht y⟩
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hpK : p ∈ K
  · exact hWon.contDiffAt (hU.mem_nhds (hKU hpK))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hpK] with q hq using hzero q hq

/-- **`lem:pln-ambient-flow` (b).** `φ_t(z) = 𝔢_t(z)` for `π|z|² ≤ p_on`. -/
theorem ambientFlow_eq_ordPath {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pon D) (t : ℝ) :
    ambientFlow D t z = D.path t z := by
  have hz' : z ∈ areaDisk D.pdag := lt_of_le_of_lt hz (pon_lt_pdag hD)
  refine (ambientField_good hD).flowOf_eq (u := fun s => D.path s z)
    ⟨hD.eq_id 0 le_rfl z hz', fun s => ?_⟩ t
  rw [ambientField_apply hD hz', chiCut_eq_one hD hz, one_smul]
  exact path_hasDerivAt hD hz'

/-- **`lem:pln-ambient-flow` (c).** `φ_t = id` on `{π|y|² > P_supp}`. -/
theorem ambientFlow_eq_id {y : ℂ} (hy : D.Psupp < π * ‖y‖ ^ 2) (t : ℝ) :
    ambientFlow D t y = y :=
  (ambientField_good hD).flowOf_fixed (fun s => ambientField_eq_zero_of_Psupp_lt hD hy) t

theorem ambientFlow_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ambientFlow D p.1 p.2) :=
  (ambientField_good hD).flowOf_smooth

theorem ambientFlow_slice_smooth (t : ℝ) : ContDiff ℝ ∞ (ambientFlow D t) :=
  (ambientField_good hD).flowOf_slice_smooth t

theorem ambientFlow_bijective (t : ℝ) : Function.Bijective (ambientFlow D t) :=
  (ambientField_good hD).flowOf_bijective t

theorem ambientFlow_zero : ambientFlow D 0 = id :=
  funext fun y => (ambientField_good hD).flowOf_zero y

theorem ambientFlow_of_nonpos {t : ℝ} (ht : t ≤ 0) (y : ℂ) : ambientFlow D t y = y :=
  (ambientField_good hD).flowOf_of_nonpos y ht

theorem ambientFlow_of_one_le {t : ℝ} (ht : 1 ≤ t) (y : ℂ) :
    ambientFlow D t y = ambientFlow D 1 y :=
  (ambientField_good hD).flowOf_of_one_le y ht

/-- **`lem:pln-ambient-flow` (c).** `det Dφ_t > 0` everywhere. -/
theorem ambientFlow_det_pos (t : ℝ) (y : ℂ) :
    0 < LinearMap.det (fderiv ℝ (ambientFlow D t) y : ℂ →ₗ[ℝ] ℂ) :=
  (ambientField_good hD).flowOf_det_pos t y

/-- **`lem:pln-ambient-flow` (c).** `φ_t` maps `D̄(P)` onto itself for `P ≥ P_supp`. -/
theorem ambientFlow_disk {P : ℝ} (hP : D.Psupp ≤ P) (t : ℝ) :
    ambientFlow D t '' closedAreaDisk P = closedAreaDisk P :=
  image_eq_of_fixed (ambientFlow_bijective hD t)
    (A := closedAreaDisk D.Psupp) (fun y hy => ambientFlow_eq_id hD (not_le.mp hy) t)
    (fun z hz => le_trans hz hP)

/-- **`lem:pln-ambient-flow` (b).** `det Dφ_t(z) = γ_t` for `π|z|² ≤ p_on` (on the open disk because
`φ_t = 𝔢_t` there; on its boundary circle by continuity). -/
theorem ambientFlow_det {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pon D) (t : ℝ) :
    LinearMap.det (fderiv ℝ (ambientFlow D t) z : ℂ →ₗ[ℝ] ℂ) = D.gam t := by
  have hopen : ∀ w ∈ areaDisk (pon D),
      LinearMap.det (fderiv ℝ (ambientFlow D t) w : ℂ →ₗ[ℝ] ℂ) = D.gam t := by
    intro w hw
    have hev : ambientFlow D t =ᶠ[𝓝 w] D.path t := by
      filter_upwards [(isOpen_areaDisk _).mem_nhds hw] with v hv
      exact ambientFlow_eq_ordPath hD (le_of_lt hv) t
    rw [hev.fderiv_eq]
    exact hD.det t w (lt_trans hw (pon_lt_pdag hD))
  have hcl : IsClosed {w : ℂ | LinearMap.det (fderiv ℝ (ambientFlow D t) w : ℂ →ₗ[ℝ] ℂ) =
      D.gam t} := by
    apply isClosed_eq _ continuous_const
    exact ContinuousLinearMap.continuous_det.comp
      ((ambientFlow_slice_smooth hD t).continuous_fderiv (by simp))
  have hpon := pon_pos hD
  have hsub : closedAreaDisk (pon D) ⊆ {w | LinearMap.det (fderiv ℝ (ambientFlow D t) w :
      ℂ →ₗ[ℝ] ℂ) = D.gam t} := by
    rw [closedAreaDisk_eq _ hpon.le, ← closure_ball (0 : ℂ)
      (Real.sqrt_pos.mpr (div_pos hpon Real.pi_pos)).ne', ← areaDisk_eq]
    exact closure_minimal hopen hcl
  exact hsub hz

end ambient

end SymplecticPacking.Qhat
