import SymplecticPacking.BranchLarge3.HandleData

/-!
# Quantitative cubic end control

The radial curvature is treated through its variable residue on punctured end charts.
No smooth extension of the radial form across the puncture is assumed. The available
uniform residue bound is logarithmic; the exhaustion modulus may therefore be exponential.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3.CubicTail

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open Set Function Filter MeasureTheory
open scoped ContDiff Manifold Topology

/-- A fixed squared-radius on which all four cubic ends are regular. -/
def outer : ℝ := 1 / 16
def inner : ℝ := 1 / 32

theorem regular_disc : {s : ℂ | Complex.normSq s ≤ outer} ⊆ endRegularRegion := by
  intro s hs
  have hn : ‖s‖ ^ 2 ≤ 1 / 16 := by simpa [outer, Complex.sq_norm] using hs
  have hp : ∀ j : Fin 2, ‖parameters 0 j‖ ≤ 2 := by
    intro j
    fin_cases j <;> norm_num [parameters]
  have hreg : s ∈ infinityRegion (parameters 0) := by
    intro j
    have hnorm : ‖parameters 0 j * s ^ 2‖ ≤ 1 / 8 := by
      rw [norm_mul, norm_pow]
      nlinarith [hp j, norm_nonneg (parameters 0 j), sq_nonneg ‖s‖]
    have hre := Complex.re_le_norm (parameters 0 j * s ^ 2)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  refine ⟨hreg, ?_⟩
  intro j hzero
  have hroot := infinityRoot_positive (parameters 0) zeroEnd hreg j
  simp only [zeroEnd, endSign, Bool.false_eq_true, ↓reduceIte, one_mul] at hroot
  have he := congrArg Complex.re hzero
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
  linarith

/-- Explicit one-dimensional compact cutoff, equal to one on `[-inner,inner]`. -/
def cutoff (t : ℝ) : ℝ :=
  Real.smoothTransition ((t + outer) / (outer - inner)) *
    (1 - Real.smoothTransition ((t - inner) / (outer - inner)))

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop)))

theorem cutoff_range (t : ℝ) : cutoff t ∈ Icc (0 : ℝ) 1 := by
  have h1 := Real.smoothTransition.nonneg ((t + outer) / (outer - inner))
  have h2 := Real.smoothTransition.le_one ((t + outer) / (outer - inner))
  have h3 := Real.smoothTransition.nonneg ((t - inner) / (outer - inner))
  have h4 := Real.smoothTransition.le_one ((t - inner) / (outer - inner))
  constructor
  · exact mul_nonneg h1 (by linarith)
  · exact mul_le_one₀ h2 (by linarith) (by linarith)

theorem cutoff_one {t : ℝ} (ht : t ∈ Ioo (-inner) inner) : cutoff t = 1 := by
  have hl : Real.smoothTransition ((t + outer) / (outer - inner)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by norm_num [outer, inner])]
    dsimp [outer, inner] at *; linarith [ht.1]
  have hr : Real.smoothTransition ((t - inner) / (outer - inner)) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
    norm_num [outer, inner]
  simp [cutoff, hl, hr]

theorem cutoff_zero {t : ℝ} (ht : t ∉ Icc (-outer) outer) : cutoff t = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  unfold cutoff
  rcases ht with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos]
    · exact zero_mul _
    · apply div_nonpos_of_nonpos_of_nonneg (by linarith)
      norm_num [outer, inner]
  · have hr : Real.smoothTransition ((t - inner) / (outer - inner)) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (by norm_num [outer, inner])]
      linarith
    rw [hr, sub_self, mul_zero]

theorem cutoff_support : tsupport cutoff ⊆ Icc (-outer) outer := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  exact ht (cutoff_zero hn)

theorem cutoff_compact : HasCompactSupport cutoff :=
  (isCompact_Icc : IsCompact (Icc (-outer) outer)).of_isClosed_subset (isClosed_tsupport cutoff) cutoff_support

/-- Definite compact bound for the derivative of the fixed cutoff. -/
def derivBound : ℝ := 1 + max 0 (sSup (range fun t => |deriv cutoff t|))

theorem derivBound_pos : 0 < derivBound := by
  unfold derivBound
  linarith [le_max_left (0 : ℝ) (sSup (range fun t => |deriv cutoff t|))]

theorem deriv_le_bound (t : ℝ) : |deriv cutoff t| ≤ derivBound := by
  obtain ⟨K, hK⟩ := (cutoff_smooth.continuous_deriv (by simp)).bounded_above_of_compact_support
    cutoff_compact.deriv
  have hb : BddAbove (range fun t => |deriv cutoff t|) := ⟨K, by
    rintro _ ⟨x, rfl⟩
    simpa only [Real.norm_eq_abs] using hK x⟩
  have h := le_csSup hb (mem_range_self t)
  unfold derivBound
  linarith [le_max_right (0 : ℝ) (sSup (range fun t => |deriv cutoff t|))]

/-- Definite bound on logarithms of all regular coefficient norms. -/
def logBound (A B D S : ℕ) : ℝ := 1 + max 0 (sSup {v : ℝ |
  ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
    v = |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)|})

theorem logBound_pos (A B D S : ℕ) : 0 < logBound A B D S := by
  unfold logBound
  linarith [le_max_left (0 : ℝ) (sSup {v : ℝ |
    ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
      v = |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)|})]

theorem log_le_bound (A B D S : ℕ) (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane)
    (hy : y ∈ radialAnnulus 0 outer) :
    |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)| ≤ logBound A B D S := by
  obtain ⟨M, hM, h⟩ := exists_regularCoefficient_log_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) regular_disc
  have hb : BddAbove {v : ℝ |
      ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
        v = |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)|} := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, ε, y, hy, rfl⟩
    exact h i ε y hy
  have hsup := le_csSup hb (show _ ∈ {v : ℝ |
      ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
        v = |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)|}
      from ⟨i, ε, y, hy, rfl⟩)
  unfold logBound
  linarith [le_max_right (0 : ℝ) (sSup {v : ℝ |
    ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
      v = |Real.log (regularCoefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) ε y)|})]

/-- Definite bound on the finitely many regular end primitives. -/
def primitiveBound (A B D S : ℕ) (c : ℝ) : ℝ := 1 + max 0 (sSup {v : ℝ |
  ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
    v = ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖})

theorem primitiveBound_pos (A B D S : ℕ) (c : ℝ) : 0 < primitiveBound A B D S c := by
  unfold primitiveBound
  linarith [le_max_left (0 : ℝ) (sSup {v : ℝ |
    ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
      v = ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖})]

theorem primitive_le_bound (A B D S : ℕ) (c : ℝ) (i : TrapezoidWeight A B) (ε : EndIndex)
    (y : Plane) (hy : y ∈ radialAnnulus 0 outer) :
    ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖ ≤ primitiveBound A B D S c := by
  obtain ⟨M, hM, h⟩ := exists_regularPrimitive_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) c regular_disc
  have hb : BddAbove {v : ℝ |
      ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
        v = ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖} := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, ε, y, hy, rfl⟩
    exact h i ε y hy
  have hsup := le_csSup hb (show _ ∈ {v : ℝ |
      ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
        v = ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖}
      from ⟨i, ε, y, hy, rfl⟩)
  unfold primitiveBound
  linarith [le_max_right (0 : ℝ) (sSup {v : ℝ |
    ∃ (i : TrapezoidWeight A B) (ε : EndIndex) (y : Plane), y ∈ radialAnnulus 0 outer ∧
      v = ‖weightedRegularEndPrimitive (cubicDegree D i) (cubicMarkedOrder S i) ε c y‖})]

local instance cubicTailSigmaCompact : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

/-- A quantitative version of `tendsto_curveCutoff_bounded_residue` for the cubic curve. -/
theorem mass_error_bound
    (α : ManifoldOneForm RealModel BaseCurve) (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel BaseCurve) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w, Ω x v w = -Ω x w v) (hαΩ : manifoldExteriorOneForm α = Ω)
    {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hdg : ∀ t : ℝ, |deriv cutoff t| ≤ K)
    (c : EndIndex → ℝ) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (β : EndIndex → Plane → Plane →L[ℝ] ℝ) (d : EndIndex → Plane → ℝ)
    (hβc : ∀ ε (n : ℕ), ContinuousOn (β ε) (radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1))))
    (hdc : ∀ ε (n : ℕ), ContinuousOn (d ε) (radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1))))
    (hβ : ∀ ε (n : ℕ) z, z ∈ radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1)) → ‖β ε z‖ ≤ M)
    (hd : ∀ ε (n : ℕ) z, z ∈ radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1)) → |d ε z - c ε| ≤ e n)
    (hdecomp : ∀ ε (n : ℕ) z, z ∈ radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1)) →
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph (parameters 0) ε) (0, z) =
        β ε z - (d ε z / 2) • angularOneForm z) (n : ℕ) :
    |surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) (by norm_num [inner])
        (fun _ ht => cutoff_one ht) n) Ω - (∑ ε, c ε) * Real.pi| ≤
      4 * (16 * K * outer * M * Real.sqrt (outer / ((n : ℝ) + 1)) + 4 * e n * K * outer) := by
  have hRn : {s : ℂ | Complex.normSq s ≤ outer / ((n : ℝ) + 1)} ⊆ infinityRegion (parameters 0) := by
    intro s hs
    exact (regular_disc (hs.trans (div_le_self (by norm_num [outer])
      (show (1 : ℝ) ≤ (n : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) n; linarith)))).1
  have hmass := curveCutoff_variable_flux_mass (parameters 0) α hα Ω hΩ hsk hαΩ
    (shrinkingCutoff_smooth cutoff_smooth n) (shrinkingCutoff_compact cutoff_compact n)
    (div_pos (by norm_num [inner]) (by positivity)) hRn
    (shrinkingCutoff_one (fun _ ht => cutoff_one ht) n)
    (shrinkingCutoff_tsupport_scaled (fun t ht => (cutoff_support ht).2) n)
    (shrinking_curveEndCutoff_compact (parameters 0) (by norm_num [inner]) (fun _ ht => cutoff_one ht) n) d β
    (fun ε z hz => hdecomp ε n z hz)
  rw [hmass, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hle := (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun ε : EndIndex =>
    (∫ z in radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1)),
      cutoffWedge (fun y => shrinkingCutoff cutoff n (radiusSq y)) (β ε) z -
        d ε z * deriv (shrinkingCutoff cutoff n) (radiusSq z)) - c ε * Real.pi)).trans
    (Finset.sum_le_sum fun ε _ => shrinking_variable_flux_error cutoff_smooth cutoff_compact
      (by norm_num [inner]) (fun _ ht => cutoff_one ht) (fun t ht => (cutoff_support ht).2)
      (by norm_num [outer]) hK hM (he n) hdg n (hβc ε n) (hdc ε n) (hβ ε n) (hd ε n))
  simpa [EndIndex, mul_add] using hle

/-- The logarithmic coefficient controlling the variable residue, uniformly in the moment. -/
def residueConst (A B D S : ℕ) (c : ℝ) : ℝ :=
  |c| * (2 * logBound A B D S + Fintype.card (TrapezoidWeight A B))

theorem residueConst_nonneg (A B D S : ℕ) (c : ℝ) : 0 ≤ residueConst A B D S c := by
  unfold residueConst
  have := logBound_pos A B D S
  positivity

/-- Explicit common error of the cutoff mass. -/
def errorBound (A B D S : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  4 * (16 * derivBound * outer * primitiveBound A B D S c * Real.sqrt (outer / ((n : ℝ) + 1)) +
    4 * logarithmicError (residueConst A B D S c) outer n * derivBound * outer)

theorem radial_mass_error {A B D S : ℕ} (hA : 0 < A) (hS0 : 0 < S)
    (hAB : A ≤ B) (hSB : S ≤ B) (hB : 3 * B < D) (hS : 3 * S < D)
    {p : Radial.Plane} (hp : p ∈ Radial.lowerTrapezoid A B) (c : ℝ) (n : ℕ) :
    |surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) (by norm_num [inner])
        (fun _ ht => cutoff_one ht) n)
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p) -
      c * (3 * ((D : ℝ) - 3 * (p.1 + p.2)) - 2 * markedHeight S (planeVector p.1 p.2)) * Real.pi| ≤
      errorBound A B D S c n := by
  have hpoint (n : ℕ) (y : Plane)
      (hy : y ∈ radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1))) :
      y ∈ (infinityDiffeomorph (parameters 0) (fun _ => false)).source ∧
      Complex.equivRealProdCLM.symm y ∈ endRegularRegion ∧ y ∈ radialAnnulus 0 outer ∧
      0 < radiusSq y ∧ radiusSq y < 1 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hy' : y ∈ radialAnnulus 0 outer :=
      ⟨radiusSq_nonneg _, hy.2.trans (div_le_self (by norm_num [outer]) hn)⟩
    have hreg : Complex.equivRealProdCLM.symm y ∈ endRegularRegion := by
      apply regular_disc
      change Complex.normSq (Complex.equivRealProdCLM.symm y) ≤ outer
      rw [radiusSq_complex]
      exact hy'.2
    have hRI : {s : ℂ | Complex.normSq s ≤ outer / ((n : ℝ) + 1)} ⊆ infinityRegion (parameters 0) :=
      fun s hs => (regular_disc (hs.trans (div_le_self (by norm_num [outer]) hn))).1
    exact ⟨radialAnnulus_in_end (parameters 0) (div_pos (by norm_num [inner]) (by positivity)) hRI _ hy,
      hreg, hy', (div_pos (by norm_num [inner]) (by positivity)).trans_le hy.1,
      hy'.2.trans_lt (by norm_num [outer])⟩
  have hpoint' (ε : EndIndex) (n : ℕ) (y : Plane)
      (hy : y ∈ radialAnnulus (inner / ((n : ℝ) + 1)) (outer / ((n : ℝ) + 1))) :
      y ∈ (infinityDiffeomorph (parameters 0) ε).source := by
    have h0 := (hpoint n y hy).1
    simpa only [infinityDiffeomorph_source] using h0
  have he := mass_error_bound
    (radialPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialPrimitive_smooth hA hAB _ _ c hp)
    (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p) rfl
    derivBound_pos.le (primitiveBound_pos A B D S c).le deriv_le_bound
    (fun ε => c * limitingEndOrder D S (planeVector p.1 p.2) ε)
    (logarithmicError (residueConst A B D S c) outer)
    (fun n => logarithmicError_nonneg (residueConst_nonneg A B D S c)
      (by norm_num [outer]) (by norm_num [outer]) n)
    (radialEndRegularPrimitive Radial.latticeIndex (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialEndResidue Radial.latticeIndex (cubicDegree D) (cubicMarkedOrder S) c p)
    (fun ε n y hy => (radialEndRegularPrimitive_contDiffAt hA hAB _ _ c hp ε
      (hpoint' ε n y hy) (hpoint n y hy).2.1).continuousAt.continuousWithinAt)
    (fun ε n y hy => (radialEndResidue_contDiffAt hA hAB _ _ c hp ε
      (hpoint' ε n y hy)).continuousAt.continuousWithinAt)
    (fun ε n y hy => radialEndRegularPrimitive_norm_le (Radial.lattice_zero A B) _ _ c p ε y
      (fun i => primitive_le_bound A B D S c i ε y (hpoint n y hy).2.2.1))
    (fun ε n y hy => by
      have hh := radialEndResidue_error hA hS0 hAB hSB hB hS hp ε
        (hpoint' ε n y hy) (hpoint n y hy).2.1 (hpoint n y hy).2.2.2.1
        (hpoint n y hy).2.2.2.2 (logBound_pos A B D S).le
        (fun i => log_le_bound A B D S i ε y (hpoint n y hy).2.2.1) c
      apply hh.trans
      rw [← mul_div_assoc]
      exact logarithmicError_bound (residueConst_nonneg A B D S c)
        (by norm_num [outer]) (by norm_num [outer]) n (hpoint n y hy).2.2.2.1 hy.2)
    (fun ε n y hy => radialPrimitive_infinity
      (Radial.latticeIndex (A := A) (B := B)) (fun i => (cubicMarked_lt_degree hB hS i).le)
      (fun i => cubicMarked_twice_complement hB hS i) c p ε (hpoint' ε n y hy) (hpoint n y hy).2.1) n
  rw [← Finset.mul_sum, sum_limitingEndOrder] at he
  exact he

theorem cutoff_support_exhaustion {ℓ : ℕ} (hℓ : 32 ≤ ℓ) :
    tsupport (curveEndCutoff (parameters 0) (shrinkingCutoff cutoff ℓ)) ⊆
      projectionDomain (parameters 0) (exhaustionRadius (parameters 0) ℓ) := by
  set R := exhaustionRadius (parameters 0) ℓ
  have hR : (ℓ : ℝ) + 3 ≤ R := by
    unfold R exhaustionRadius
    have h1 : ‖parameters 0 0‖ ≤ ∑ j, ‖parameters 0 j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (parameters 0 j)) (Finset.mem_univ 0)
    have h2 : ‖parameters 0 0‖ = 1 := by simp [parameters]
    linarith
  have hℓr : (32 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hRp : 0 < R := by linarith
  have hsq : 32 * ((ℓ : ℝ) + 1) ≤ R ^ 2 := by
    nlinarith [sq_nonneg ((ℓ : ℝ) - 32)]
  apply closure_minimal _ (projectionDomain_closed (parameters 0) R)
  intro x hx
  by_contra hnot
  apply hx
  have hnorm : R < ‖x.val.1‖ := by
    simpa only [projectionDomain, mem_setOf_eq, not_le] using hnot
  have hx0 : x.val.1 ≠ 0 := by intro hz; rw [hz, norm_zero] at hnorm; linarith
  have hnsq : R ^ 2 < Complex.normSq x.val.1 := by
    rw [← Complex.sq_norm]
    exact pow_lt_pow_left₀ hnorm hRp.le (by norm_num)
  have hnp : 0 < Complex.normSq x.val.1 := by nlinarith [sq_nonneg R]
  have hsmall : ((ℓ : ℝ) + 1) * Complex.normSq (x.val.1)⁻¹ < inner := by
    rw [Complex.normSq_inv]
    dsimp [inner]
    rw [mul_inv_lt_iff₀ hnp]
    nlinarith
  have hnonneg : 0 ≤ ((ℓ : ℝ) + 1) * Complex.normSq (x.val.1)⁻¹ := by
    rw [Complex.normSq_inv]
    positivity
  unfold curveEndCutoff inverseComplementCutoff curveProjection
  rw [if_neg hx0]
  show 1 - cutoff (((ℓ : ℝ) + 1) * Complex.normSq (x.val.1)⁻¹) = 0
  rw [cutoff_one ⟨by dsimp [inner]; linarith, hsmall⟩, sub_self]

/-- A common constant for both terms of the uniform cutoff-mass error. -/
def rateConst (A B D S : ℕ) (c : ℝ) : ℝ :=
  1 + 64 * derivBound * outer * primitiveBound A B D S c +
    16 * residueConst A B D S c * derivBound * outer

theorem rateConst_pos (A B D S : ℕ) (c : ℝ) : 0 < rateConst A B D S c := by
  unfold rateConst
  have := derivBound_pos
  have := primitiveBound_pos A B D S c
  have := residueConst_nonneg A B D S c
  have h0 : 0 < outer := by norm_num [outer]
  positivity

/-- An explicit, possibly exponential, error modulus. -/
def modulus (A B D S : ℕ) (c e : ℝ) : ℕ :=
  max 32 (max ⌈(2 * rateConst A B D S c / e) ^ 2⌉₊
    ⌈Real.exp (2 * rateConst A B D S c / e)⌉₊)

theorem errorBound_lt {A B D S : ℕ} {c e : ℝ} (he : 0 < e) {ℓ : ℕ}
    (hℓ : modulus A B D S c e ≤ ℓ) : errorBound A B D S c ℓ < e := by
  let C := rateConst A B D S c
  let T := 2 * C / e
  have hC : 0 < C := rateConst_pos A B D S c
  have hT : 0 < T := div_pos (by positivity) he
  have hsq : T ^ 2 < (ℓ : ℝ) + 1 := by
    have h1 : ⌈T ^ 2⌉₊ ≤ ℓ :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hℓ)
    have h2 := Nat.le_ceil (T ^ 2)
    have h3 : ((⌈T ^ 2⌉₊ : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast h1
    linarith
  have hexp : Real.exp T < (ℓ : ℝ) + 1 := by
    have h1 : ⌈Real.exp T⌉₊ ≤ ℓ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hℓ)
    have h2 := Nat.le_ceil (Real.exp T)
    have h3 : ((⌈Real.exp T⌉₊ : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast h1
    linarith
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  have houter : 0 < outer := by norm_num [outer]
  have hroot : Real.sqrt (outer / ((ℓ : ℝ) + 1)) < 1 / T := by
    rw [Real.sqrt_lt' (div_pos one_pos hT)]
    have hT2 : 0 < T ^ 2 := by positivity
    have hbound : outer * T ^ 2 < (ℓ : ℝ) + 1 := by
      have ho : outer ≤ 1 := by norm_num [outer]
      nlinarith [sq_nonneg T]
    rw [one_div_pow, div_lt_div_iff₀ hℓpos hT2]
    simpa using hbound
  have hlog : T < -Real.log (outer / ((ℓ : ℝ) + 1)) := by
    have hq : 0 < outer / ((ℓ : ℝ) + 1) := div_pos houter hℓpos
    have hlt : outer / ((ℓ : ℝ) + 1) < Real.exp (-T) := by
      rw [Real.exp_neg]
      have ho : outer ≤ 1 := by norm_num [outer]
      simpa only [one_div] using (div_le_div_of_nonneg_right ho hℓpos.le).trans_lt
        (one_div_lt_one_div_of_lt (Real.exp_pos T) hexp)
    have h := (Real.log_lt_iff_lt_exp hq).mpr hlt
    linarith
  have hden : 0 < -Real.log (outer / ((ℓ : ℝ) + 1)) := hT.trans hlog
  have hhalf : C / T = e / 2 := by dsimp [T]; field_simp
  have hpart1 : C * Real.sqrt (outer / ((ℓ : ℝ) + 1)) < e / 2 := by
    have := mul_lt_mul_of_pos_left hroot hC
    simpa only [mul_one_div, hhalf] using this
  have hpart2 : C / (-Real.log (outer / ((ℓ : ℝ) + 1))) < e / 2 := by
    rw [← hhalf]
    exact div_lt_div_of_pos_left hC hT hlog
  have hK := derivBound_pos
  have hM := primitiveBound_pos A B D S c
  have hres := residueConst_nonneg A B D S c
  have hA : 0 ≤ 64 * derivBound * outer * primitiveBound A B D S c := by positivity
  have hB : 0 ≤ 16 * residueConst A B D S c * derivBound * outer := by positivity
  have hca : 64 * derivBound * outer * primitiveBound A B D S c ≤ C := by dsimp [C, rateConst]; linarith
  have hcb : 16 * residueConst A B D S c * derivBound * outer ≤ C := by dsimp [C, rateConst]; linarith
  have ha := mul_le_mul_of_nonneg_right hca (Real.sqrt_nonneg (outer / ((ℓ : ℝ) + 1)))
  have hb := div_le_div_of_nonneg_right hcb hden.le
  unfold errorBound logarithmicError
  have hrewrite :
      4 * (16 * derivBound * outer * primitiveBound A B D S c * Real.sqrt (outer / ((ℓ : ℝ) + 1)) +
        4 * (residueConst A B D S c / -Real.log (outer / ((ℓ : ℝ) + 1))) * derivBound * outer) =
      (64 * derivBound * outer * primitiveBound A B D S c) * Real.sqrt (outer / ((ℓ : ℝ) + 1)) +
        (16 * residueConst A B D S c * derivBound * outer) / -Real.log (outer / ((ℓ : ℝ) + 1)) := by ring
  rw [hrewrite]
  linarith

end SymplecticPacking.BranchLarge3.CubicTail
