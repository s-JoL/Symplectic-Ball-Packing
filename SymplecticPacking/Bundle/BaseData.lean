import SymplecticPacking.Bundle.BaseForms
import SymplecticPacking.Params

/-!
# Base data in torus coordinates

`sec:fer` (`prop:cub-handle`, `prop:fer-handle`): the base data in torus coordinates `(u, v)`:
the annuli `𝒜 ⊂ 𝒜⁺`, the step function `f = stepA`, the bump `b = bB` of `β = b(v) dv`, the
annular cutoff `ζ_𝒜`, the cutoffs `ζ_j` near the points `b_j`, and their supports.

Conventions (see `TorusCalculus.lean`): objects on the torus are functions on the cover `ℝ²`,
`1`-periodic in `u` and `v`. Functions defined on `[0, 1]` in the paper and "extended
periodically" are composed with `Int.fract`; centred coordinates about `b_j` are
`x_j = fract(u − u(b_j) + 1/2) − 1/2` (`centred`), equal to `u − u(b_j)` near `b_j`.
Sets of the paper are `u`- resp. `v`-intervals in the fundamental domain.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Set Filter Topology MeasureTheory
open scoped ContDiff Real

/-! ### Base data (`prop:cub-handle`) -/

/-- `𝒜⁺ = {1/12 < u < 1/4}`. -/
def annulusPlus : Set ℝ := Ioo (1 / 12) (1 / 4)

/-- `𝒜 = {1/8 < u < 5/24}`. -/
def annulus : Set ℝ := Ioo (1 / 8) (5 / 24)

/-- `u₀ = 7/48`. -/
def u0 : ℝ := 7 / 48

/-- `u₁ = 3/16`. -/
def u1 : ℝ := 3 / 16

/-- `f(u) = S((u − u₀)/(u₁ − u₀))`. -/
def stepA (u : ℝ) : ℝ := flatStep ((u - u0) / (u1 - u0))

/-- `ψ` on `[0, 1]`: `a_flat(v − 1/8) a_flat(5/24 − v)`. -/
def psi0 (v : ℝ) : ℝ := expNegInvGlue (v - 1 / 8) * expNegInvGlue (5 / 24 - v)

/-- `ψ`, extended `1`-periodically. -/
def psiB (v : ℝ) : ℝ := psi0 (Int.fract v)

/-- `∫₀¹ ψ`. -/
def psiInt : ℝ := ∫ v in (0 : ℝ)..1, psiB v

/-- `b(v) = ψ(v) / ∫₀¹ ψ`. -/
def bB (v : ℝ) : ℝ := psiB v / psiInt

/-- `β = b(v) dv`. -/
def betaB : BForm := ⟨fun _ _ _ => 0, fun _ v _ => bB v⟩

/-- `ℬ = {1/9 < v < 2/9}`. -/
def stripB : Set ℝ := Ioo (1 / 9) (2 / 9)

/-- `ζ_𝒜` on `[0, 1]`: `S((u − 9/96)/(2/96)) S((23/96 − u)/(2/96))`. -/
def zetaA0 (u : ℝ) : ℝ := flatStep ((u - 9 / 96) / (2 / 96)) * flatStep ((23 / 96 - u) / (2 / 96))

/-- `ζ_𝒜`, extended by zero (periodically) to the torus. -/
def zetaA (u : ℝ) : ℝ := zetaA0 (Int.fract u)

/-- The radial cutoff `χ_{1/200, 1/100}` in the plane. -/
def diskCut (x y : ℝ) : ℝ :=
  1 - flatStep ((x ^ 2 + y ^ 2 - (1 / 200) ^ 2) / ((1 / 100) ^ 2 - (1 / 200) ^ 2))

/-- Centred coordinate `x ↦ x − c` reduced to `[−1/2, 1/2)`. -/
def centred (c x : ℝ) : ℝ := Int.fract (x - c + 1 / 2) - 1 / 2

/-- `ζ_j = χ_{1/200, 1/100}(x_j, y_j)`, extended by zero. -/
def zetaJ (j : Fin 3) (u v : ℝ) : ℝ := diskCut (centred (bpoints j).1 u) (centred (bpoints j).2 v)

/-! ### Elementary facts -/

lemma contDiff_stepA : ContDiff ℝ ∞ stepA :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma stepA_eq_zero {u : ℝ} (hu : u ≤ u0) : stepA u = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [u0, u1]))

lemma stepA_eq_one {u : ℝ} (hu : u1 ≤ u) : stepA u = 1 :=
  Real.smoothTransition.one_of_one_le (by
    rw [le_div_iff₀ (by norm_num [u0, u1])]; linarith)

lemma monotone_stepA : Monotone stepA := fun a b hab =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith)
    (by norm_num [u0, u1]))

lemma deriv_stepA_nonneg (u : ℝ) : 0 ≤ deriv stepA u :=
  monotone_stepA.deriv_nonneg

lemma stepA_nonneg (u : ℝ) : 0 ≤ stepA u := Real.smoothTransition.nonneg _
lemma stepA_le_one (u : ℝ) : stepA u ≤ 1 := Real.smoothTransition.le_one _

lemma deriv_stepA_eq_zero {u : ℝ} (hu : u ∉ Ioo u0 u1) : deriv stepA u = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hu
  rcases hu with hu | hu
  · have : IsLocalMin stepA u := Filter.Eventually.of_forall fun y => by
      rw [stepA_eq_zero hu]; exact stepA_nonneg y
    exact this.deriv_eq_zero
  · have : IsLocalMax stepA u := Filter.Eventually.of_forall fun y => by
      rw [stepA_eq_one hu]; exact stepA_le_one y
    exact this.deriv_eq_zero

lemma contDiff_deriv_stepA : ContDiff ℝ ∞ (deriv stepA) :=
  (contDiff_infty_iff_deriv.mp contDiff_stepA).2

/-! #### `ψ`, `b`, `β` -/

lemma contDiff_psi0 : ContDiff ℝ ∞ psi0 :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma psi0_eq_zero {v : ℝ} (hv : v ∉ Ioo (1 / 8 : ℝ) (5 / 24)) : psi0 v = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hv
  rcases hv with hv | hv
  · rw [psi0, expNegInvGlue.zero_of_nonpos (show v - 1 / 8 ≤ 0 by linarith), zero_mul]
  · rw [psi0, expNegInvGlue.zero_of_nonpos (show 5 / 24 - v ≤ 0 by linarith), mul_zero]

lemma psi0_pos {v : ℝ} (hv : v ∈ Ioo (1 / 8 : ℝ) (5 / 24)) : 0 < psi0 v :=
  mul_pos (expNegInvGlue.pos_of_pos (by linarith [hv.1]))
    (expNegInvGlue.pos_of_pos (by linarith [hv.2]))

lemma psi0_nonneg (v : ℝ) : 0 ≤ psi0 v :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma contDiff_psiB : ContDiff ℝ ∞ psiB :=
  contDiff_comp_fract contDiff_psi0 (a := 1 / 8) (b := 5 / 24) (by norm_num) (by norm_num)
    fun s hs => psi0_eq_zero fun h => hs (Ioo_subset_Icc_self h)

lemma psiB_nonneg (v : ℝ) : 0 ≤ psiB v := psi0_nonneg _

lemma fract_of_mem_Ico {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) : Int.fract v = v :=
  Int.fract_eq_self.mpr hv

lemma psiInt_pos : 0 < psiInt := by
  have hc := contDiff_psiB.continuous
  have h1 : 0 < ∫ v in (1 / 8 : ℝ)..(5 / 24), psiB v :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
      (fun v hv => by
        rw [psiB, fract_of_mem_Ico ⟨by linarith [hv.1], by linarith [hv.2]⟩]
        exact psi0_pos hv) (by norm_num)
  have h2 : ∫ v in (1 / 8 : ℝ)..(5 / 24), psiB v ≤ ∫ v in (0 : ℝ)..1, psiB v :=
    intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (Filter.Eventually.of_forall psiB_nonneg) (hc.intervalIntegrable _ _)
  exact lt_of_lt_of_le h1 h2

lemma contDiff_bB : ContDiff ℝ ∞ bB := contDiff_psiB.div_const _

lemma bB_nonneg (v : ℝ) : 0 ≤ bB v := div_nonneg (psiB_nonneg v) psiInt_pos.le

lemma bB_add_one (v : ℝ) : bB (v + 1) = bB v := by simp [bB, psiB, Int.fract_add_one]

lemma integral_bB : ∫ v in (0 : ℝ)..1, bB v = 1 := by
  simp only [bB]
  rw [intervalIntegral.integral_div]
  exact div_self psiInt_pos.ne'

lemma bB_pos {v : ℝ} (hv : v ∈ Ioo (1 / 8 : ℝ) (5 / 24)) : 0 < bB v := by
  rw [bB, psiB, fract_of_mem_Ico ⟨by linarith [hv.1], by linarith [hv.2]⟩]
  exact div_pos (psi0_pos hv) psiInt_pos

lemma bB_eq_zero {v : ℝ} (hv : Int.fract v ∉ Ioo (1 / 8 : ℝ) (5 / 24)) : bB v = 0 := by
  rw [bB, psiB, psi0_eq_zero hv, zero_div]

/-! #### `ζ_𝒜` -/

lemma contDiff_zetaA0 : ContDiff ℝ ∞ zetaA0 :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

lemma zetaA0_eq_zero {u : ℝ} (hu : u ∉ Ioo (9 / 96 : ℝ) (23 / 96)) : zetaA0 u = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hu
  rcases hu with hu | hu
  · rw [zetaA0, flatStep, Real.smoothTransition.zero_of_nonpos (x := (u - 9 / 96) / (2 / 96))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)), zero_mul]
  · rw [zetaA0, flatStep, Real.smoothTransition.zero_of_nonpos (x := (23 / 96 - u) / (2 / 96))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)), mul_zero]

lemma zetaA0_eq_one {u : ℝ} (hu : u ∈ Icc (11 / 96 : ℝ) (21 / 96)) : zetaA0 u = 1 := by
  rw [zetaA0, flatStep, Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le,
    mul_one]
  · rw [le_div_iff₀ (by norm_num)]; linarith [hu.2]
  · rw [le_div_iff₀ (by norm_num)]; linarith [hu.1]

lemma zetaA_eq_one {u : ℝ} (hu : u ∈ Icc (11 / 96 : ℝ) (21 / 96)) : zetaA u = 1 := by
  rw [zetaA, fract_of_mem_Ico ⟨by linarith [hu.1], by linarith [hu.2]⟩, zetaA0_eq_one hu]

lemma zetaA_eq_zero {u : ℝ} (hu : Int.fract u ∉ Ioo (9 / 96 : ℝ) (23 / 96)) : zetaA u = 0 :=
  zetaA0_eq_zero hu

/-! #### Centred coordinates and `ζ_j` -/

lemma centred_eq (c x : ℝ) : centred c x = x - c - ⌊x - c + 1 / 2⌋ := by
  rw [centred, Int.fract]; ring

lemma exists_of_abs_centred_lt {c x r : ℝ} (h : |centred c x| < r) :
    ∃ n : ℤ, |x - c - n| < r := ⟨⌊x - c + 1 / 2⌋, by rwa [centred_eq] at h⟩

/-- Near `x₀` with `|centred c x₀| < 1/2`, the centred coordinate is `x − c − n` (affine). -/
lemma centred_eventually {c x₀ : ℝ} (h : |centred c x₀| < 1 / 2) :
    ∀ᶠ x in 𝓝 x₀, centred c x = x - c - ⌊x₀ - c + 1 / 2⌋ := by
  have hfr : Int.fract (x₀ - c + 1 / 2) ≠ 0 := by
    intro h0; rw [centred, h0] at h; norm_num at h
  have := (((continuous_id.sub continuous_const).add continuous_const).tendsto x₀).eventually
    (fract_eventually_of_not_int hfr)
  filter_upwards [this] with x hx
  have hx' : Int.fract (x - c + 1 / 2) = x - c + 1 / 2 - ⌊x₀ - c + 1 / 2⌋ := hx
  rw [centred, hx']; ring

lemma diskCut_eq_zero {x y : ℝ} (h : (1 / 100 : ℝ) ^ 2 ≤ x ^ 2 + y ^ 2) : diskCut x y = 0 := by
  rw [diskCut, flatStep, Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ (by norm_num)]; linarith

lemma diskCut_eq_one {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ (1 / 200 : ℝ) ^ 2) : diskCut x y = 1 := by
  rw [diskCut, flatStep, Real.smoothTransition.zero_of_nonpos, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

lemma contDiff_diskCut : ContDiff ℝ ∞ (fun x : ℝ × ℝ => diskCut x.1 x.2) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).sub contDiff_const).div_const _))

/-- Smoothness of functions of the centred coordinates cut off by `diskCut`. -/
lemma contDiff_centred_cut {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (c d : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      diskCut (centred c x.1) (centred d x.2) * H (centred c x.1, centred d x.2)) := by
  set G : ℝ × ℝ → ℝ :=
    fun y => diskCut (y.1 - 1 / 2) (y.2 - 1 / 2) * H (y.1 - 1 / 2, y.2 - 1 / 2) with hGdef
  have hG : ContDiff ℝ ∞ G := by
    have hs : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((y.1 - 1 / 2, y.2 - 1 / 2) : ℝ × ℝ)) :=
      (contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.sub contDiff_const)
    exact (contDiff_diskCut.comp hs).mul (hH.comp hs)
  have far : ∀ s : ℝ, s ∉ Icc (1 / 2 - 1 / 100 : ℝ) (1 / 2 + 1 / 100) →
      (1 / 100 : ℝ) ^ 2 ≤ (s - 1 / 2) ^ 2 := by
    intro s hs
    have : (1 / 100 : ℝ) ≤ |s - 1 / 2| := by
      by_contra hc; push Not at hc
      exact hs ⟨by linarith [(abs_lt.mp hc).1], by linarith [(abs_lt.mp hc).2]⟩
    rw [← sq_abs (s - 1 / 2)]
    exact pow_le_pow_left₀ (by norm_num) this 2
  have h0 : ∀ s t, (s ∉ Icc (1 / 2 - 1 / 100 : ℝ) (1 / 2 + 1 / 100) ∨
      t ∉ Icc (1 / 2 - 1 / 100 : ℝ) (1 / 2 + 1 / 100)) → G (s, t) = 0 := by
    intro s t hst
    simp only [hGdef]
    rw [diskCut_eq_zero, zero_mul]
    rcases hst with hs | ht
    · nlinarith [far s hs, sq_nonneg (t - 1 / 2)]
    · nlinarith [far t ht, sq_nonneg (s - 1 / 2)]
  have := (contDiff_comp_fract₂ hG (by norm_num) (by norm_num) h0).comp
    (((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk
      ((contDiff_snd.sub contDiff_const).add contDiff_const) :
      ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1 - c + 1 / 2, x.2 - d + 1 / 2) : ℝ × ℝ)))
  exact this

/-! #### Support relations (`prop:fer-handle`) -/

lemma fract_mem_iff {u : ℝ} {a b : ℝ} : Int.fract u ∈ Icc a b → ∃ m : ℤ, u - m ∈ Icc a b :=
  fun h => ⟨⌊u⌋, by rwa [← Int.fract]⟩

lemma bpoints_fst (j : Fin 3) : (bpoints j).1 = 0 ∨ (bpoints j).1 = 1 / 3 ∨
    (bpoints j).1 = 2 / 3 := by
  fin_cases j <;> simp [bpoints]

lemma bpoints_snd (j : Fin 3) : (bpoints j).2 = 0 ∨ (bpoints j).2 = 2 / 3 ∨
    (bpoints j).2 = 1 / 3 := by
  fin_cases j <;> simp [bpoints]

/-- An integer `k` with `|k + w| < r` for `w` in an interval at distance `≥ r` from `ℤ`. -/
lemma int_far {k : ℤ} {w a b r : ℝ} (hw : w ∈ Icc a b) (ha : -1 + r ≤ a) (hb : b ≤ -r)
    (h : |(k : ℝ) + w| < r) : False := by
  rcases abs_lt.mp h with ⟨h1, h2⟩
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
    linarith [hw.1, hw.2]
  · subst hk; simp at h1 h2; linarith [hw.2]
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hw.1, hw.2]

lemma int_far_pt {k : ℤ} {w r : ℝ} (hw1 : r - 1 ≤ w) (hw2 : w ≤ -r) (h : |(k : ℝ) + w| < r) :
    False := int_far (a := w) (b := w) ⟨le_rfl, le_rfl⟩ (by linarith) hw2 h

lemma int_far_shift {k : ℤ} {w r : ℝ} (hw1 : r ≤ w) (hw2 : w ≤ 1 - r) (h : |(k : ℝ) + w| < r) :
    False :=
  int_far_pt (k := k + 1) (w := w - 1) (r := r) (by linarith) (by linarith) (by
    have e : ((k + 1 : ℤ) : ℝ) + (w - 1) = k + w := by push_cast; ring
    rw [e]; exact h)

/-- Distance from `ℤ`: if `|x − n| < r` and `x − m ∈ [a, b]` with `[a, b] + ℤ` at distance
`≥ r` from `ℤ` (encoded by `-1 + r ≤ a`, `b ≤ -r`), contradiction. -/
lemma int_far' {x a b r : ℝ} {n m : ℤ} (hn : |x - n| < r) (hm : x - m ∈ Icc a b)
    (ha : -1 + r ≤ a) (hb : b ≤ -r) : False :=
  int_far (k := m - n) (w := x - m) hm ha hb (by push_cast; convert hn using 2; ring)

lemma u_far_annulus {j : Fin 3} {u : ℝ} (h : |centred (bpoints j).1 u| < 1 / 100) :
    Int.fract u ∉ Icc (1 / 12 : ℝ) (1 / 4) := by
  intro hf
  obtain ⟨n, hn⟩ := exists_of_abs_centred_lt h
  obtain ⟨m, hm⟩ := fract_mem_iff hf
  rcases bpoints_fst j with hj | hj | hj <;> rw [hj] at hn
  · exact int_far' (x := u) (n := n) (m := m + 1) (a := 1 / 12 - 1) (b := 1 / 4 - 1)
      (by simpa using hn) ⟨by push_cast; linarith [hm.1], by push_cast; linarith [hm.2]⟩
      (by norm_num) (by norm_num)
  · exact int_far' (x := u - 1 / 3) (n := n) (m := m) (a := 1 / 12 - 1 / 3) (b := 1 / 4 - 1 / 3)
      hn ⟨by linarith [hm.1], by linarith [hm.2]⟩ (by norm_num) (by norm_num)
  · exact int_far' (x := u - 2 / 3) (n := n) (m := m) (a := 1 / 12 - 2 / 3) (b := 1 / 4 - 2 / 3)
      hn ⟨by linarith [hm.1], by linarith [hm.2]⟩ (by norm_num) (by norm_num)

lemma v_far_strip {j : Fin 3} {v : ℝ} (h : |centred (bpoints j).2 v| < 1 / 100) :
    Int.fract v ∉ Icc (1 / 9 : ℝ) (2 / 9) := by
  intro hf
  obtain ⟨n, hn⟩ := exists_of_abs_centred_lt h
  obtain ⟨m, hm⟩ := fract_mem_iff hf
  rcases bpoints_snd j with hj | hj | hj <;> rw [hj] at hn
  · exact int_far' (x := v) (n := n) (m := m + 1) (a := 1 / 9 - 1) (b := 2 / 9 - 1)
      (by simpa using hn) ⟨by push_cast; linarith [hm.1], by push_cast; linarith [hm.2]⟩
      (by norm_num) (by norm_num)
  · exact int_far' (x := v - 2 / 3) (n := n) (m := m) (a := 1 / 9 - 2 / 3) (b := 2 / 9 - 2 / 3)
      hn ⟨by linarith [hm.1], by linarith [hm.2]⟩ (by norm_num) (by norm_num)
  · exact int_far' (x := v - 1 / 3) (n := n) (m := m) (a := 1 / 9 - 1 / 3) (b := 2 / 9 - 1 / 3)
      hn ⟨by linarith [hm.1], by linarith [hm.2]⟩ (by norm_num) (by norm_num)

lemma u_far_other {j k : Fin 3} (hjk : j ≠ k) {u : ℝ} (h : |centred (bpoints j).1 u| < 1 / 100) :
    1 / 100 ≤ |centred (bpoints k).1 u| := by
  by_contra hc; push Not at hc
  obtain ⟨n, hn⟩ := exists_of_abs_centred_lt h
  obtain ⟨m, hm⟩ := exists_of_abs_centred_lt hc
  -- `x := u - c_j` is within `1/100` of `n` and `x - (c_k - c_j)` within `1/100` of `m`
  have key : ∀ w : ℝ, w ∈ ({-2/3, -1/3, 1/3, 2/3} : Set ℝ) →
      |u - (bpoints j).1 - n| < 1 / 100 → |u - (bpoints j).1 - w - m| < 1 / 100 → False := by
    intro w hw h1 h2
    have h3 : |((n - m : ℤ) : ℝ) + -w| < 2 / 100 := by
      have : ((n - m : ℤ) : ℝ) + -w = (u - (bpoints j).1 - w - m) - (u - (bpoints j).1 - n) := by
        push_cast; ring
      rw [this]
      calc _ ≤ |u - (bpoints j).1 - w - m| + |u - (bpoints j).1 - n| := abs_sub _ _
        _ < 2 / 100 := by linarith
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact int_far_shift (w := 2 / 3) (r := 2 / 100) (by norm_num) (by norm_num)
        (by convert h3 using 3; try norm_num)
    · exact int_far_shift (w := 1 / 3) (r := 2 / 100) (by norm_num) (by norm_num)
        (by convert h3 using 3; try norm_num)
    · exact int_far_pt (w := -(1 / 3)) (r := 2 / 100) (by norm_num) (by norm_num)
        (by convert h3 using 3; try norm_num)
    · exact int_far_pt (w := -(2 / 3)) (r := 2 / 100) (by norm_num) (by norm_num)
        (by convert h3 using 3; try norm_num)
  refine key ((bpoints k).1 - (bpoints j).1) ?_ hn (by convert hm using 2; ring)
  fin_cases j <;> fin_cases k <;> simp [bpoints] at hjk ⊢ <;> norm_num

lemma zetaJ_ne_zero {j : Fin 3} {u v : ℝ} (h : zetaJ j u v ≠ 0) :
    |centred (bpoints j).1 u| < 1 / 100 ∧ |centred (bpoints j).2 v| < 1 / 100 := by
  by_contra hc
  apply h
  apply diskCut_eq_zero
  rcases not_and_or.mp hc with h1 | h1 <;> push Not at h1
  · have := pow_le_pow_left₀ (by norm_num) h1 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (centred (bpoints j).2 v)]
  · have := pow_le_pow_left₀ (by norm_num) h1 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (centred (bpoints j).1 u)]

/-- **Support relations** (`prop:fer-handle`). -/
theorem supports :
    -- (i) `f`
    ((∀ u, u ≤ u0 → stepA u = 0) ∧ (∀ u, u1 ≤ u → stepA u = 1) ∧
      (annulus ∩ Iic u0).Nonempty ∧ (annulus ∩ Ici u1).Nonempty ∧ ∀ u, 0 ≤ deriv stepA u) ∧
    -- (ii) `β`
    ((∀ u v p, betaB.dC u v p = 0) ∧ (∫ v in (0 : ℝ)..1, bB v = 1) ∧
      (∀ v ∈ Ioo (1 / 8 : ℝ) (5 / 24), 0 < bB v) ∧
      (∀ v, Int.fract v ∉ Ioo (1 / 8 : ℝ) (5 / 24) → bB v = 0) ∧
      Icc (1 / 8 : ℝ) (5 / 24) ⊆ stripB) ∧
    -- (iii) `ζ_𝒜`
    ((∀ u ∈ Icc (11 / 96 : ℝ) (21 / 96), zetaA u = 1) ∧
      (∀ u, Int.fract u ∉ Ioo (9 / 96 : ℝ) (23 / 96) → zetaA u = 0) ∧
      Icc (9 / 96 : ℝ) (23 / 96) ⊆ annulusPlus ∧ closure annulus ⊆ Icc (11 / 96) (21 / 96)) ∧
    -- (iv) the disks `U_j`
    ((∀ j u v, zetaJ j u v ≠ 0 →
        |centred (bpoints j).1 u| < 1 / 100 ∧ |centred (bpoints j).2 v| < 1 / 100) ∧
      (∀ j u v, centred (bpoints j).1 u ^ 2 + centred (bpoints j).2 v ^ 2 ≤ (1 / 200) ^ 2 →
        zetaJ j u v = 1) ∧
      (∀ j u, |centred (bpoints j).1 u| < 1 / 100 → Int.fract u ∉ Icc (1 / 12 : ℝ) (1 / 4)) ∧
      (∀ j v, |centred (bpoints j).2 v| < 1 / 100 → Int.fract v ∉ Icc (1 / 9 : ℝ) (2 / 9)) ∧
      (∀ j k u, j ≠ k → |centred (bpoints j).1 u| < 1 / 100 →
        1 / 100 ≤ |centred (bpoints k).1 u|)) := by
  refine ⟨⟨fun u => stepA_eq_zero, fun u => stepA_eq_one, ?_, ?_, deriv_stepA_nonneg⟩,
    ⟨?_, integral_bB, fun v => bB_pos, fun v => bB_eq_zero, ?_⟩,
    ⟨fun u => zetaA_eq_one, fun u => zetaA_eq_zero, ?_, ?_⟩,
    ⟨fun j u v => zetaJ_ne_zero, fun j u v h => diskCut_eq_one h, fun j u => u_far_annulus,
      fun j v => v_far_strip, fun j k u h => u_far_other h⟩⟩
  · exact ⟨u0, ⟨by norm_num [u0], by norm_num [u0]⟩, mem_Iic.mpr le_rfl⟩
  · exact ⟨u1, ⟨by norm_num [u1], by norm_num [u1]⟩, mem_Ici.mpr le_rfl⟩
  · intro u v p
    simp [BForm.dC, betaB, pu, pv]
  · intro v hv; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [annulus, closure_Ioo (by norm_num)]
    intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

end SymplecticPacking.Bundle
