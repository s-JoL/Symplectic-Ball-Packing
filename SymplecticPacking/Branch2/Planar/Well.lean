import SymplecticPacking.Branch2.Planar.MorsePair

/-!
# Exactly quadratic modification and signed Morse inverse of a one-dimensional well

Generic form of `Inner/Rtilde.lean` and `Inner/Xtilde.lean`. A *well* is a function `f` smooth
on an open interval `(A, B)`, proper at both ends, with a nondegenerate unique critical point
`c` (`(x - c) f'(x) > 0` for `x ≠ c`, `f''(c) = α > 0`). With `g(x) = f(c + x) - f(c)` on
`(A - c, B - c)`:

* `f̃(x) = g(x) + ψ(x/ε)(αx²/2 - g(x))` is exactly quadratic on `|x| ≤ ε`, equal to `g` on
  `|x| ≥ 2ε`, `|f̃ - g| ≤ δ`, and `x f̃'(x) > 0` for `x ≠ 0` (Taylor estimate with the third
  derivative bound `K₃` of a compactly supported copy of `g`);
* `Σ(x) = sign(x) √f̃(x)` is a smooth increasing bijection `(A - c, B - c) → ℝ`, linear on
  `|x| ≤ ε`;
* its inverse `X = θ ∘ (Σ ∘ θ)⁻¹` (`θ : ℝ → (A - c, B - c)` an explicit diffeomorphism, only
  used to reach the generic inverse `Inner.invR`) is smooth with `X' > 0`, `f̃(X(u)) = u²`,
  `X(u) = u/√(α/2)` for `|u| ≤ √(α/2) ε`.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Filter Topology Set
open scoped ContDiff Real

open Inner (invR psiR Cpsi)

/-- A one-dimensional well. -/
structure Well where
  f : ℝ → ℝ
  A : ℝ
  B : ℝ
  c : ℝ
  δ : ℝ

namespace Well

variable (W : Well)

/-- Hypotheses on a well. -/
structure Hyp : Prop where
  A_lt : W.A < W.c
  lt_B : W.c < W.B
  δ_pos : 0 < W.δ
  smooth : ContDiffOn ℝ ∞ W.f (Ioo W.A W.B)
  crit : deriv W.f W.c = 0
  sign : ∀ x ∈ Ioo W.A W.B, x ≠ W.c → 0 < (x - W.c) * deriv W.f x
  second : 0 < deriv (deriv W.f) W.c
  top : Tendsto W.f (𝓝[<] W.B) atTop
  bot : Tendsto W.f (𝓝[>] W.A) atTop

/-- `A - c`. -/
def lo : ℝ := W.A - W.c
/-- `B - c`. -/
def hi : ℝ := W.B - W.c
/-- `g(x) = f(c + x) - f(c)`. -/
def g (x : ℝ) : ℝ := W.f (W.c + x) - W.f W.c
/-- `r₀ = min(c - A, B - c)/4`. -/
def r0 : ℝ := min (W.c - W.A) (W.B - W.c) / 4
/-- Cutoff `χ(x) = ψ(x/r₀)`. -/
def chi (x : ℝ) : ℝ := psiR (x / W.r0)
/-- The compactly supported copy `χ g` of `g`. -/
def gg (x : ℝ) : ℝ := W.chi x * W.g x
/-- `α = f''(c)`. -/
def alpha : ℝ := deriv (deriv W.f) W.c
/-- `K₃ = 1 + sup |(χ g)'''|`. -/
def K3 : ℝ := 1 + ⨆ x, |deriv (deriv (deriv W.gg)) x|
/-- `ε = min(r₀/4, α/(32 K₃ (1 + C_ψ)), √(δ/α))`. -/
def eps : ℝ := min (min (W.r0 / 4) (W.alpha / (32 * W.K3 * (1 + Cpsi)))) √(W.δ / W.alpha)
/-- `g_c(x) = αx²/2 - (χ g)(x)`. -/
def gc (x : ℝ) : ℝ := W.alpha * x ^ 2 / 2 - W.gg x
/-- The exactly quadratic modification `f̃ = g + ψ(x/ε) g_c`. -/
def ft (x : ℝ) : ℝ := W.g x + psiR (x / W.eps) * W.gc x
/-- `Σ(x) = sign(x) √f̃(x)`. -/
def Sig (x : ℝ) : ℝ := Real.sign x * √(W.ft x)
/-- `θ(t) = (lo + hi)/2 + (hi - lo)/2 · t/√(1+t²)`, a diffeomorphism `ℝ → (lo, hi)`. -/
def theta (t : ℝ) : ℝ := (W.lo + W.hi) / 2 + (W.hi - W.lo) / 2 * (t / √(1 + t ^ 2))
/-- `G = Σ ∘ θ`. -/
def G (t : ℝ) : ℝ := W.Sig (W.theta t)
/-- The Morse inverse `X = θ ∘ G⁻¹ = Σ⁻¹`. -/
def X (u : ℝ) : ℝ := W.theta (invR W.G u)
/-- `√(α/2)`. -/
def lin : ℝ := √(W.alpha / 2)

variable {W}

/-! ### The cutoff function `t/√(1+t²)` -/

lemma one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma sqrt_one_add_sq_pos (t : ℝ) : 0 < √(1 + t ^ 2) := Real.sqrt_pos.2 (one_add_sq_pos t)

lemma abs_lt_sqrt (t : ℝ) : |t| < √(1 + t ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

lemma sfun_mem (t : ℝ) : t / √(1 + t ^ 2) ∈ Ioo (-1 : ℝ) 1 := by
  have h := abs_lt_sqrt t
  have hp := sqrt_one_add_sq_pos t
  rw [abs_lt] at h
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

lemma sfun_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => t / √(1 + t ^ 2)) (1 / ((1 + t ^ 2) * √(1 + t ^ 2))) t := by
  have hq : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have hs := hq.sqrt (one_add_sq_pos t).ne'
  have hd := (hasDerivAt_id t).div hs (sqrt_one_add_sq_pos t).ne'
  refine hd.congr_deriv ?_
  have h1 := sqrt_one_add_sq_pos t
  have h2 : √(1 + t ^ 2) * √(1 + t ^ 2) = 1 + t ^ 2 := Real.mul_self_sqrt (one_add_sq_pos t).le
  set s := √(1 + t ^ 2)
  simp only [id]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  have h3 : s ^ 2 = 1 + t ^ 2 := by rw [sq]; exact h2
  rw [h3]
  ring

lemma sfun_contDiff : ContDiff ℝ ∞ (fun t : ℝ => t / √(1 + t ^ 2)) :=
  contDiff_id.div ((contDiff_const.add (contDiff_id.pow 2)).sqrt fun t =>
    (one_add_sq_pos t).ne') fun t => (sqrt_one_add_sq_pos t).ne'

lemma sfun_tendsto_atTop : Tendsto (fun t : ℝ => t / √(1 + t ^ 2)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => (√(t⁻¹ ^ 2 + 1))⁻¹) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ => t⁻¹ ^ 2 + 1) atTop (𝓝 (0 ^ 2 + 1)) :=
      (tendsto_inv_atTop_zero.pow 2).add_const 1
    have h2 := (Real.continuous_sqrt.tendsto _).comp this
    simp only [zero_pow two_ne_zero, zero_add, Real.sqrt_one] at h2
    simpa using h2.inv₀ one_ne_zero
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hs : √(1 + t ^ 2) = t * √(t⁻¹ ^ 2 + 1) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ t⁻¹ ^ 2 + 1 by positivity)
    calc t * √(t⁻¹ ^ 2 + 1) * (t * √(t⁻¹ ^ 2 + 1))
        = t ^ 2 * (√(t⁻¹ ^ 2 + 1) * √(t⁻¹ ^ 2 + 1)) := by ring
      _ = t ^ 2 * (t⁻¹ ^ 2 + 1) := by rw [h]
      _ = 1 + t ^ 2 := by field_simp
  rw [hs]; field_simp

lemma sfun_tendsto_atBot : Tendsto (fun t : ℝ => t / √(1 + t ^ 2)) atBot (𝓝 (-1)) := by
  have h := sfun_tendsto_atTop.comp tendsto_neg_atBot_atTop
  have h2 := h.neg
  refine h2.congr' (Eventually.of_forall fun t => ?_)
  simp [Function.comp_def, neg_div]

lemma deriv_g (x : ℝ) : deriv W.g x = deriv W.f (W.c + x) := by
  unfold g
  rw [deriv_sub_const, deriv_comp_const_add]

lemma g_zero : W.g 0 = 0 := by simp [g]

lemma Sig_zero : W.Sig 0 = 0 := by unfold Sig; rw [Real.sign_zero, zero_mul]

lemma Sig_of_pos {x : ℝ} (hx : 0 < x) : W.Sig x = √(W.ft x) := by
  unfold Sig; rw [Real.sign_of_pos hx, one_mul]

lemma Sig_of_neg {x : ℝ} (hx : x < 0) : W.Sig x = -√(W.ft x) := by
  unfold Sig; rw [Real.sign_of_neg hx, neg_one_mul]

section hyp
variable (hW : W.Hyp)
include hW

/-! ### Elementary facts -/

lemma lo_neg : W.lo < 0 := by unfold lo; linarith [hW.A_lt]
lemma hi_pos : 0 < W.hi := by unfold hi; linarith [hW.lt_B]

lemma r0_pos : 0 < W.r0 := by
  unfold r0; have := hW.A_lt; have := hW.lt_B
  exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)

lemma four_r0_le_lo : 4 * W.r0 ≤ -W.lo := by
  unfold r0 lo; have := min_le_left (W.c - W.A) (W.B - W.c); linarith

lemma four_r0_le_hi : 4 * W.r0 ≤ W.hi := by
  unfold r0 hi; have := min_le_right (W.c - W.A) (W.B - W.c); linarith

lemma mem_of_abs_lt {x : ℝ} (hx : |x| < 4 * W.r0) : x ∈ Ioo W.lo W.hi := by
  have := four_r0_le_lo hW; have := four_r0_le_hi hW
  rw [abs_lt] at hx
  exact ⟨by linarith, by linarith⟩

lemma add_mem {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : W.c + x ∈ Ioo W.A W.B := by
  unfold lo hi at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma g_contDiffOn : ContDiffOn ℝ ∞ W.g (Ioo W.lo W.hi) := by
  have h := hW.smooth.comp (contDiffOn_const.add contDiffOn_id) (fun x hx => add_mem hW hx)
  exact h.sub contDiffOn_const

lemma g_contDiffAt {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : ContDiffAt ℝ ∞ W.g x :=
  (g_contDiffOn hW).contDiffAt (isOpen_Ioo.mem_nhds hx)

lemma g_hasDerivAt {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : HasDerivAt W.g (deriv W.g x) x :=
  ((g_contDiffAt hW hx).differentiableAt (by simp)).hasDerivAt

/-! ### The compactly supported copy -/

lemma chi_contDiff : ContDiff ℝ ∞ W.chi :=
  Inner.psiR_contDiff.comp (contDiff_id.div_const _)

lemma chi_eq_one {x : ℝ} (hx : |x| ≤ W.r0) : W.chi x = 1 := by
  have := r0_pos hW
  exact Inner.psiR_eq_one (by rw [abs_div, abs_of_pos this, div_le_one this]; exact hx)

lemma chi_eq_zero {x : ℝ} (hx : 2 * W.r0 ≤ |x|) : W.chi x = 0 := by
  have := r0_pos hW
  exact Inner.psiR_eq_zero (by rw [abs_div, abs_of_pos this, le_div_iff₀ this]; exact hx)

lemma gg_contDiff : ContDiff ℝ ∞ W.gg := by
  have hr := r0_pos hW
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases lt_or_ge |x| (3 * W.r0) with h | h
  · exact (chi_contDiff hW).contDiffAt.mul (g_contDiffAt hW (mem_of_abs_lt hW (by linarith)))
  · have hev : W.gg =ᶠ[𝓝 x] fun _ => 0 := by
      have : {y : ℝ | 2 * W.r0 < |y|} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds (by show 2 * W.r0 < |x|; linarith)
      filter_upwards [this] with y hy
      simp [gg, chi_eq_zero hW (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma gg_hasCompactSupport : HasCompactSupport W.gg := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * W.r0)) (b := 2 * W.r0))
    (fun x hx => ?_)
  have : 2 * W.r0 ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith [r0_pos hW])]; linarith
    · rw [abs_of_pos (by linarith [r0_pos hW])]; linarith
  simp [gg, chi_eq_zero hW this]

lemma gg_eq {x : ℝ} (hx : |x| ≤ W.r0) : W.gg x = W.g x := by
  simp [gg, chi_eq_one hW hx]

lemma gg_eventually {x : ℝ} (hx : |x| < W.r0) : W.gg =ᶠ[𝓝 x] W.g := by
  have : {y : ℝ | |y| < W.r0} ∈ 𝓝 x := (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  filter_upwards [this] with y hy using gg_eq hW hy.le

lemma d1_contDiff : ContDiff ℝ ∞ (deriv W.gg) :=
  (contDiff_infty_iff_deriv.mp (gg_contDiff hW)).2
lemma d2_contDiff : ContDiff ℝ ∞ (deriv (deriv W.gg)) :=
  (contDiff_infty_iff_deriv.mp (d1_contDiff hW)).2
lemma d3_contDiff : ContDiff ℝ ∞ (deriv (deriv (deriv W.gg))) :=
  (contDiff_infty_iff_deriv.mp (d2_contDiff hW)).2

lemma bdd_d3 : BddAbove (range fun x => |deriv (deriv (deriv W.gg)) x|) := by
  have hc := (d3_contDiff hW).continuous
  have hcs : HasCompactSupport (deriv (deriv (deriv W.gg))) :=
    (gg_hasCompactSupport hW).deriv.deriv.deriv
  have := hc.norm.bddAbove_range_of_hasCompactSupport hcs.norm
  simpa [Real.norm_eq_abs] using this

lemma abs_d3_le (x : ℝ) : |deriv (deriv (deriv W.gg)) x| ≤ W.K3 := by
  have := le_ciSup (bdd_d3 hW) x
  unfold K3; linarith

lemma K3_pos : 0 < W.K3 := by
  have := (abs_nonneg _).trans (le_ciSup (bdd_d3 hW) 0)
  unfold K3; linarith

lemma deriv_gg_eventually : deriv W.gg =ᶠ[𝓝 0] fun x => deriv W.f (W.c + x) := by
  have : {y : ℝ | |y| < W.r0} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp [r0_pos hW])
  filter_upwards [this] with y hy
  rw [(gg_eventually hW hy).deriv_eq, deriv_g]

lemma gg_zero : W.gg 0 = 0 := by rw [gg_eq hW (by simp [(r0_pos hW).le]), g_zero]

lemma d1_zero : deriv W.gg 0 = 0 := by
  rw [(deriv_gg_eventually hW).eq_of_nhds, add_zero, hW.crit]

lemma d2_zero : deriv (deriv W.gg) 0 = W.alpha := by
  rw [(deriv_gg_eventually hW).deriv_eq, deriv_comp_const_add, add_zero]; rfl

lemma alpha_pos : 0 < W.alpha := hW.second

/-! ### Taylor estimates -/

lemma hasDerivAt_gg (x : ℝ) : HasDerivAt W.gg (deriv W.gg x) x :=
  ((gg_contDiff hW).differentiable (by simp) x).hasDerivAt
lemma hasDerivAt_d1 (x : ℝ) : HasDerivAt (deriv W.gg) (deriv (deriv W.gg) x) x :=
  ((d1_contDiff hW).differentiable (by simp) x).hasDerivAt
lemma hasDerivAt_d2 (x : ℝ) :
    HasDerivAt (deriv (deriv W.gg)) (deriv (deriv (deriv W.gg)) x) x :=
  ((d2_contDiff hW).differentiable (by simp) x).hasDerivAt

lemma hasDerivAt_gc (x : ℝ) : HasDerivAt W.gc (W.alpha * x - deriv W.gg x) x := by
  have := (((hasDerivAt_pow 2 x).const_mul W.alpha).div_const 2).sub (hasDerivAt_gg hW x)
  refine this.congr_deriv ?_
  push_cast; ring

lemma hasDerivAt_gc1 (x : ℝ) :
    HasDerivAt (fun x => W.alpha * x - deriv W.gg x) (W.alpha - deriv (deriv W.gg) x) x := by
  have := ((hasDerivAt_id' x).const_mul W.alpha).sub (hasDerivAt_d1 hW x)
  refine this.congr_deriv ?_; ring

lemma hasDerivAt_gc2 (x : ℝ) :
    HasDerivAt (fun x => W.alpha - deriv (deriv W.gg) x)
      (-deriv (deriv (deriv W.gg)) x) x := by
  have := (hasDerivAt_d2 hW x).const_sub W.alpha
  exact this

lemma gc2_abs_le (x : ℝ) : |W.alpha - deriv (deriv W.gg) x| ≤ W.K3 * |x| := by
  have := Inner.abs_le_of_hasDerivAt_abs_le (c := W.K3) 0 (hasDerivAt_gc2 hW)
    (by simp [d2_zero hW]) (fun t => by simpa using abs_d3_le hW t) x
  simpa using this

lemma gc1_abs_le (x : ℝ) : |W.alpha * x - deriv W.gg x| ≤ W.K3 * x ^ 2 / 2 := by
  have := Inner.abs_le_of_hasDerivAt_abs_le (c := W.K3) 1 (hasDerivAt_gc1 hW)
    (by simp [d1_zero hW]) (fun t => by simpa using gc2_abs_le hW t) x
  calc |W.alpha * x - deriv W.gg x| ≤ _ := this
    _ = W.K3 * x ^ 2 / 2 := by norm_num [sq_abs]

lemma gc_abs_le (x : ℝ) : |W.gc x| ≤ W.K3 * |x| ^ 3 / 6 := by
  have := Inner.abs_le_of_hasDerivAt_abs_le (c := W.K3 / 2) 2 (hasDerivAt_gc hW)
    (by simp [gc, gg_zero hW]) (fun t => by
      have := gc1_abs_le hW t
      rw [← sq_abs] at this
      linarith) x
  calc |W.gc x| ≤ _ := this
    _ = W.K3 * |x| ^ 3 / 6 := by norm_num; ring

/-! ### Scales -/

lemma eps_pos : 0 < W.eps := by
  have := r0_pos hW; have := K3_pos hW; have := alpha_pos hW; have := hW.δ_pos
  have := Inner.Cpsi_nonneg
  unfold eps
  exact lt_min (lt_min (by positivity) (by positivity)) (Real.sqrt_pos.2 (by positivity))

lemma eps_le_r0 : W.eps ≤ W.r0 / 4 := (min_le_left _ _).trans (min_le_left _ _)

lemma K3_mul_eps : W.K3 * W.eps ≤ W.alpha / (32 * (1 + Cpsi)) := by
  have hK := K3_pos hW
  have hC := Inner.Cpsi_nonneg
  have h : W.eps ≤ W.alpha / (32 * W.K3 * (1 + Cpsi)) := (min_le_left _ _).trans (min_le_right _ _)
  calc W.K3 * W.eps ≤ W.K3 * (W.alpha / (32 * W.K3 * (1 + Cpsi))) :=
        mul_le_mul_of_nonneg_left h hK.le
    _ = W.alpha / (32 * (1 + Cpsi)) := by field_simp

lemma eps_sq_le : W.eps ^ 2 ≤ W.δ / W.alpha := by
  have h : W.eps ≤ √(W.δ / W.alpha) := min_le_right _ _
  have h0 := (eps_pos hW).le
  calc W.eps ^ 2 ≤ √(W.δ / W.alpha) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = W.δ / W.alpha := Real.sq_sqrt (div_nonneg hW.δ_pos.le (alpha_pos hW).le)

/-! ### The modified potential `f̃` -/

lemma ft_eq_quad {x : ℝ} (hx : |x| ≤ W.eps) : W.ft x = W.alpha * x ^ 2 / 2 := by
  have he := eps_pos hW
  have h1 : psiR (x / W.eps) = 1 := Inner.psiR_eq_one
    (by rw [abs_div, abs_of_pos he, div_le_one he]; exact hx)
  have h2 : W.gg x = W.g x := gg_eq hW (by linarith [eps_le_r0 hW, r0_pos hW])
  unfold ft gc; rw [h1, h2]; ring

lemma ft_eq_far {x : ℝ} (hx : 2 * W.eps ≤ |x|) : W.ft x = W.g x := by
  have he := eps_pos hW
  have : psiR (x / W.eps) = 0 := Inner.psiR_eq_zero
    (by rw [abs_div, abs_of_pos he, le_div_iff₀ he]; exact hx)
  unfold ft; rw [this]; ring

lemma ft_zero : W.ft 0 = 0 := by
  rw [ft_eq_quad hW (by simp [(eps_pos hW).le])]; ring

/-- `|f̃ - g| ≤ δ`. -/
theorem ft_close (x : ℝ) : |W.ft x - W.g x| ≤ W.δ := by
  have he := eps_pos hW
  have hδ := hW.δ_pos
  rcases le_or_gt (2 * W.eps) |x| with hx | hx
  · rw [ft_eq_far hW hx, sub_self, abs_zero]; exact hδ.le
  have h1 : |W.ft x - W.g x| ≤ |W.gc x| := by
    unfold ft
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Inner.psiR_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Inner.psiR_le_one _)
  have hK := K3_pos hW
  have h2 : |W.gc x| ≤ W.K3 * (2 * W.eps) ^ 3 / 6 := by
    refine (gc_abs_le hW x).trans ?_
    gcongr
  have hC := Inner.Cpsi_nonneg
  have ha := alpha_pos hW
  have h3 : W.K3 * (2 * W.eps) ^ 3 / 6 = 4 / 3 * (W.K3 * W.eps) * W.eps ^ 2 := by ring
  have h4 : W.K3 * W.eps ≤ W.alpha / 32 := by
    refine (K3_mul_eps hW).trans ?_
    apply div_le_div_of_nonneg_left ha.le (by norm_num); nlinarith
  have h5 := eps_sq_le hW
  have h6 : 4 / 3 * (W.K3 * W.eps) * W.eps ^ 2 ≤ 4 / 3 * (W.alpha / 32) * (W.δ / W.alpha) := by
    gcongr
  have h7 : 4 / 3 * (W.alpha / 32) * (W.δ / W.alpha) = W.δ / 24 := by field_simp; ring
  linarith

lemma ft_contDiffOn : ContDiffOn ℝ ∞ W.ft (Ioo W.lo W.hi) := by
  have h2 : ContDiff ℝ ∞ (fun x => psiR (x / W.eps) * W.gc x) :=
    (Inner.psiR_contDiff.comp (contDiff_id.div_const _)).mul
      (((contDiff_const.mul (contDiff_id.pow 2)).div_const 2).sub (gg_contDiff hW))
  exact (g_contDiffOn hW).add h2.contDiffOn

lemma ft_contDiffAt {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : ContDiffAt ℝ ∞ W.ft x :=
  (ft_contDiffOn hW).contDiffAt (isOpen_Ioo.mem_nhds hx)

lemma hasDerivAt_ft {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) :
    HasDerivAt W.ft (deriv W.g x + deriv psiR (x / W.eps) / W.eps * W.gc x +
      psiR (x / W.eps) * (W.alpha * x - deriv W.gg x)) x := by
  have hψ := (Inner.psiR_differentiable (x / W.eps)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const W.eps)
  have := (g_hasDerivAt hW hx).add (hψ.mul (hasDerivAt_gc hW x))
  refine this.congr_deriv ?_
  simp only [id, Function.comp_apply]; ring

/-- Near estimate: for `|x| ≤ 2ε`, `x f̃'(x) ≥ (91/96) α x²`. -/
theorem ft_deriv_near {x : ℝ} (hx : |x| ≤ 2 * W.eps) :
    91 / 96 * W.alpha * x ^ 2 ≤ x * deriv W.ft x := by
  have he := eps_pos hW
  have hr := r0_pos hW
  have hxr : |x| < W.r0 := by linarith [eps_le_r0 hW]
  have hmem : x ∈ Ioo W.lo W.hi := mem_of_abs_lt hW (by linarith)
  rw [(hasDerivAt_ft hW hmem).deriv]
  have hg' : deriv W.g x = deriv W.gg x := ((gg_eventually hW hxr).deriv_eq).symm
  rw [hg']
  set ε := W.eps
  set a := W.alpha
  set K := W.K3
  set C := Cpsi
  set ψ := psiR (x / ε)
  set d := deriv psiR (x / ε)
  set Gc := W.gc x
  set G1 := a * x - deriv W.gg x
  have e : x * (deriv W.gg x + d / ε * Gc + ψ * G1) = a * x ^ 2 - (1 - ψ) * (x * G1)
      + x * (d / ε * Gc) := by simp only [G1]; ring
  set u := |x|
  have ha : 0 < a := alpha_pos hW
  have hK : 0 < K := K3_pos hW
  have hC : 0 ≤ C := Inner.Cpsi_nonneg
  have hu : 0 ≤ u := abs_nonneg x
  have hx2 : x ^ 2 = u ^ 2 := (sq_abs x).symm
  have hKe : K * ε ≤ a / (32 * (1 + C)) := K3_mul_eps hW
  have hG1 : |G1| ≤ K * x ^ 2 / 2 := gc1_abs_le hW x
  have hG : |Gc| ≤ K * u ^ 3 / 6 := gc_abs_le hW x
  have hd : |d| ≤ C := Inner.abs_deriv_psiR_le _
  have hψ0 : 0 ≤ ψ := Inner.psiR_nonneg _
  have hψ1 : ψ ≤ 1 := Inner.psiR_le_one _
  have h1 : |x * G1| ≤ (K * ε) * x ^ 2 := by
    rw [abs_mul]
    calc u * |G1| ≤ u * (K * x ^ 2 / 2) := mul_le_mul_of_nonneg_left hG1 hu
      _ = K * x ^ 2 * (u / 2) := by ring
      _ ≤ K * x ^ 2 * ε := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (K * ε) * x ^ 2 := by ring
  have h2 : |x * (d / ε * Gc)| ≤ 2 / 3 * C * (K * ε) * x ^ 2 := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos he]
    have hu2 : u ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
    have : u * (|d| * |Gc|) ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε := by
      calc u * (|d| * |Gc|) ≤ u * (C * (K * u ^ 3 / 6)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hd hG (abs_nonneg _) hC) hu
        _ = C * K * u ^ 2 * u ^ 2 / 6 := by ring
        _ ≤ C * K * u ^ 2 * (4 * ε ^ 2) / 6 := by gcongr
        _ = 2 / 3 * C * (K * ε) * x ^ 2 * ε := by rw [hx2]; ring
    calc u * (|d| / ε * |Gc|) = u * (|d| * |Gc|) / ε := by ring
      _ ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε / ε := by gcongr
      _ = 2 / 3 * C * (K * ε) * x ^ 2 := by field_simp
  have hKe1 : (K * ε) * x ^ 2 ≤ a / 32 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    refine hKe.trans ?_
    apply div_le_div_of_nonneg_left ha.le (by norm_num); nlinarith
  have hKe2 : 2 / 3 * C * (K * ε) * x ^ 2 ≤ a / 48 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    have hCK : 2 / 3 * C * (K * ε) ≤ 2 / 3 * C * (a / (32 * (1 + C))) :=
      mul_le_mul_of_nonneg_left hKe (by positivity)
    refine hCK.trans ?_
    rw [show 2 / 3 * C * (a / (32 * (1 + C))) = a / 48 * (C / (1 + C)) by
      field_simp; ring]
    have : C / (1 + C) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith
  have b1 : (1 - ψ) * (x * G1) ≤ |x * G1| :=
    calc (1 - ψ) * (x * G1) ≤ (1 - ψ) * |x * G1| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ 1 * |x * G1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |x * G1| := one_mul _
  have b2 := neg_abs_le (x * (d / ε * Gc))
  rw [e]
  nlinarith

/-- `x f̃'(x) > 0` for `x ≠ 0` in `(lo, hi)`. -/
theorem ft_mono {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) (h0 : x ≠ 0) : 0 < x * deriv W.ft x := by
  rcases le_or_gt |x| (2 * W.eps) with h | h
  · have := ft_deriv_near hW h
    have : 0 < 91 / 96 * W.alpha * x ^ 2 := by
      have := alpha_pos hW; have := pow_pos (abs_pos.2 h0) 2; rw [sq_abs] at this; positivity
    linarith
  · have hev : W.ft =ᶠ[𝓝 x] W.g := by
      have hopen : IsOpen {y : ℝ | 2 * W.eps < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds h] with y hy
      exact ft_eq_far hW (le_of_lt hy)
    rw [hev.deriv_eq, deriv_g]
    have := hW.sign (W.c + x) (add_mem hW hx) (by intro h'; apply h0; linarith)
    rwa [add_sub_cancel_left] at this

lemma ft_deriv_pos {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) (h0 : 0 < x) : 0 < deriv W.ft x :=
  (pos_iff_pos_of_mul_pos (ft_mono hW hx h0.ne')).mp h0

lemma ft_deriv_neg {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) (h0 : x < 0) : deriv W.ft x < 0 :=
  neg_of_mul_pos_right (ft_mono hW hx h0.ne) h0.le

theorem ft_strictMonoOn : StrictMonoOn W.ft (Ico 0 W.hi) := by
  have hsub : Ico 0 W.hi ⊆ Ioo W.lo W.hi := fun x hx => ⟨by linarith [lo_neg hW, hx.1], hx.2⟩
  refine strictMonoOn_of_deriv_pos (convex_Ico 0 W.hi) ((ft_contDiffOn hW).continuousOn.mono hsub)
    fun x hx => ?_
  rw [interior_Ico] at hx
  exact ft_deriv_pos hW (hsub (Ioo_subset_Ico_self hx)) hx.1

theorem ft_strictAntiOn : StrictAntiOn W.ft (Ioc W.lo 0) := by
  have hsub : Ioc W.lo 0 ⊆ Ioo W.lo W.hi := fun x hx => ⟨hx.1, by linarith [hi_pos hW, hx.2]⟩
  refine strictAntiOn_of_deriv_neg (convex_Ioc W.lo 0)
    ((ft_contDiffOn hW).continuousOn.mono hsub) fun x hx => ?_
  rw [interior_Ioc] at hx
  exact ft_deriv_neg hW (hsub (Ioo_subset_Ioc_self hx)) hx.2

theorem ft_pos {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) (h0 : x ≠ 0) : 0 < W.ft x := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have := ft_strictAntiOn hW ⟨hx.1, h.le⟩ ⟨lo_neg hW, le_rfl⟩ h
    rwa [ft_zero hW] at this
  · have := ft_strictMonoOn hW ⟨le_rfl, hi_pos hW⟩ ⟨h.le, hx.2⟩ h
    rwa [ft_zero hW] at this

lemma ft_nonneg {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : 0 ≤ W.ft x := by
  rcases eq_or_ne x 0 with rfl | h
  · rw [ft_zero hW]
  · exact (ft_pos hW hx h).le

/-! ### The signed square root `Σ` -/

lemma lin_pos : 0 < W.lin := Real.sqrt_pos.2 (by have := alpha_pos hW; positivity)

theorem Sig_linear {x : ℝ} (hx : |x| ≤ W.eps) : W.Sig x = W.lin * x := by
  unfold Sig lin
  rw [ft_eq_quad hW hx, show W.alpha * x ^ 2 / 2 = W.alpha / 2 * x ^ 2 by ring,
    Real.sqrt_mul (by have := alpha_pos hW; positivity), Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

theorem Sig_sq {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : W.Sig x ^ 2 = W.ft x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Sig_of_neg h, neg_sq, Real.sq_sqrt (ft_pos hW hx h.ne).le]
  · rw [Sig_zero, ft_zero hW]; ring
  · rw [Sig_of_pos h, Real.sq_sqrt (ft_pos hW hx h.ne').le]

lemma Sig_local {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt W.Sig d x ∧ ContDiffAt ℝ ∞ W.Sig x := by
  have he := eps_pos hW
  by_cases h0 : |x| < W.eps
  · have hev : W.Sig =ᶠ[𝓝 x] fun z => W.lin * z := by
      filter_upwards [(continuous_abs.tendsto x).eventually (gt_mem_nhds h0)] with z hz
      exact Sig_linear hW hz.le
    refine ⟨W.lin, lin_pos hW, ?_, ?_⟩
    · have := (hasDerivAt_id x).const_mul W.lin
      rw [mul_one] at this
      exact this.congr_of_eventuallyEq hev
    · exact (contDiffAt_id.const_smul W.lin).congr_of_eventuallyEq hev
  · rw [not_lt] at h0
    have hft := ft_contDiffAt hW hx
    have hdiff : DifferentiableAt ℝ W.ft x := hft.differentiableAt (by simp)
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; rw [abs_zero] at h0; linarith) with hx0 | hx0
    · have hR := ft_pos hW hx hx0.ne
      have hev : W.Sig =ᶠ[𝓝 x] fun z => -√(W.ft z) := by
        filter_upwards [gt_mem_nhds hx0] with z hz using Sig_of_neg hz
      have hd := (hdiff.hasDerivAt.sqrt hR.ne').neg
      refine ⟨-(deriv W.ft x / (2 * √(W.ft x))), ?_, hd.congr_of_eventuallyEq hev, ?_⟩
      · have := ft_deriv_neg hW hx hx0
        have : 0 < √(W.ft x) := Real.sqrt_pos.2 hR
        have : deriv W.ft x / (2 * √(W.ft x)) < 0 :=
          div_neg_of_neg_of_pos ‹_› (by linarith)
        linarith
      · exact ((hft.sqrt hR.ne').neg).congr_of_eventuallyEq hev
    · have hR := ft_pos hW hx hx0.ne'
      have hev : W.Sig =ᶠ[𝓝 x] fun z => √(W.ft z) := by
        filter_upwards [lt_mem_nhds hx0] with z hz using Sig_of_pos hz
      have hd := hdiff.hasDerivAt.sqrt hR.ne'
      refine ⟨deriv W.ft x / (2 * √(W.ft x)), ?_, hd.congr_of_eventuallyEq hev, ?_⟩
      · have := ft_deriv_pos hW hx hx0
        have : 0 < √(W.ft x) := Real.sqrt_pos.2 hR
        positivity
      · exact (hft.sqrt hR.ne').congr_of_eventuallyEq hev

lemma Sig_continuousOn : ContinuousOn W.Sig (Ioo W.lo W.hi) := fun x hx =>
  (Sig_local hW hx).choose_spec.2.2.continuousAt.continuousWithinAt

theorem Sig_strictMonoOn : StrictMonoOn W.Sig (Ioo W.lo W.hi) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (Sig_continuousOn hW) fun x hx => ?_
  rw [interior_Ioo] at hx
  obtain ⟨d, hd, hD, -⟩ := Sig_local hW hx
  rw [hD.deriv]; exact hd

theorem Sig_tendsto_hi : Tendsto W.Sig (𝓝[<] W.hi) atTop := by
  have he := eps_pos hW
  have h2e : 2 * W.eps < W.hi := by
    linarith [eps_le_r0 hW, four_r0_le_hi hW, r0_pos hW]
  have hshift : Tendsto (fun x => W.c + x) (𝓝[<] W.hi) (𝓝[<] W.B) := by
    have h1 : Tendsto (fun x => W.c + x) (𝓝 W.hi) (𝓝 W.B) := by
      have := (continuous_const.add continuous_id).tendsto (f := fun x : ℝ => W.c + x) W.hi
      simpa [hi] using this
    refine tendsto_nhdsWithin_iff.mpr ⟨h1.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Iio] at hx ⊢; unfold hi at hx; linarith
  have hg : Tendsto W.g (𝓝[<] W.hi) atTop :=
    tendsto_atTop_add_const_right _ _ (hW.top.comp hshift)
  have hs := Real.tendsto_sqrt_atTop.comp hg
  refine hs.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT h2e] with x hx
  rw [Function.comp_apply, Sig_of_pos (by linarith [hx.1]),
    ft_eq_far hW (by rw [abs_of_pos (by linarith [hx.1])]; exact hx.1.le)]

theorem Sig_tendsto_lo : Tendsto W.Sig (𝓝[>] W.lo) atBot := by
  have he := eps_pos hW
  have h2e : W.lo < -(2 * W.eps) := by
    linarith [eps_le_r0 hW, four_r0_le_lo hW, r0_pos hW]
  have hshift : Tendsto (fun x => W.c + x) (𝓝[>] W.lo) (𝓝[>] W.A) := by
    have h1 : Tendsto (fun x => W.c + x) (𝓝 W.lo) (𝓝 W.A) := by
      have := (continuous_const.add continuous_id).tendsto (f := fun x : ℝ => W.c + x) W.lo
      simpa [lo] using this
    refine tendsto_nhdsWithin_iff.mpr ⟨h1.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_Ioi] at hx ⊢; unfold lo at hx; linarith
  have hg : Tendsto W.g (𝓝[>] W.lo) atTop :=
    tendsto_atTop_add_const_right _ _ (hW.bot.comp hshift)
  have hs := tendsto_neg_atTop_atBot.comp (Real.tendsto_sqrt_atTop.comp hg)
  refine hs.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT h2e] with x hx
  have hx0 : x < 0 := by linarith [hx.2]
  rw [Function.comp_apply, Function.comp_apply, Sig_of_neg hx0,
    ft_eq_far hW (by rw [abs_of_neg hx0]; linarith [hx.2])]

/-! ### `θ` and `G = Σ ∘ θ` -/

lemma theta_mem (t : ℝ) : W.theta t ∈ Ioo W.lo W.hi := by
  have hs := sfun_mem t
  have hl := lo_neg hW; have hh := hi_pos hW
  unfold theta
  constructor <;> nlinarith [hs.1, hs.2]

lemma theta_contDiff : ContDiff ℝ ∞ W.theta :=
  contDiff_const.add (contDiff_const.mul sfun_contDiff)

lemma theta_hasDerivAt (t : ℝ) :
    HasDerivAt W.theta ((W.hi - W.lo) / 2 * (1 / ((1 + t ^ 2) * √(1 + t ^ 2)))) t :=
  ((sfun_hasDerivAt t).const_mul _).const_add _

lemma theta_deriv_pos (t : ℝ) : 0 < (W.hi - W.lo) / 2 * (1 / ((1 + t ^ 2) * √(1 + t ^ 2))) := by
  have := lo_neg hW; have := hi_pos hW
  have := sqrt_one_add_sq_pos t; have := one_add_sq_pos t
  have : 0 < (W.hi - W.lo) / 2 := by linarith
  positivity

lemma theta_tendsto_top : Tendsto W.theta atTop (𝓝[<] W.hi) := by
  have h : Tendsto W.theta atTop (𝓝 ((W.lo + W.hi) / 2 + (W.hi - W.lo) / 2 * 1)) :=
    tendsto_const_nhds.add (sfun_tendsto_atTop.const_mul _)
  rw [show (W.lo + W.hi) / 2 + (W.hi - W.lo) / 2 * 1 = W.hi by ring] at h
  exact tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall fun t => (theta_mem hW t).2⟩

lemma theta_tendsto_bot : Tendsto W.theta atBot (𝓝[>] W.lo) := by
  have h : Tendsto W.theta atBot (𝓝 ((W.lo + W.hi) / 2 + (W.hi - W.lo) / 2 * (-1))) :=
    tendsto_const_nhds.add (sfun_tendsto_atBot.const_mul _)
  rw [show (W.lo + W.hi) / 2 + (W.hi - W.lo) / 2 * (-1) = W.lo by ring] at h
  exact tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall fun t => (theta_mem hW t).1⟩

lemma G_contDiff : ContDiff ℝ ∞ W.G :=
  contDiff_iff_contDiffAt.2 fun t =>
    (Sig_local hW (theta_mem hW t)).choose_spec.2.2.comp t (theta_contDiff hW).contDiffAt

lemma G_deriv_pos (t : ℝ) : 0 < deriv W.G t := by
  obtain ⟨d, hd, hD, -⟩ := Sig_local hW (theta_mem hW t)
  have := hD.comp t (theta_hasDerivAt hW t)
  rw [show W.G = W.Sig ∘ W.theta from rfl, this.deriv]
  exact mul_pos hd (theta_deriv_pos hW t)

lemma G_top : Tendsto W.G atTop atTop := (Sig_tendsto_hi hW).comp (theta_tendsto_top hW)
lemma G_bot : Tendsto W.G atBot atBot := (Sig_tendsto_lo hW).comp (theta_tendsto_bot hW)

lemma G_strictMono : StrictMono W.G := strictMono_of_deriv_pos (G_deriv_pos hW)

lemma G_invR (u : ℝ) : W.G (invR W.G u) = u :=
  Inner.apply_invR' (G_contDiff hW).continuous (G_strictMono hW) (G_top hW) (G_bot hW) u

/-! ### The Morse inverse `X` -/

theorem X_mem (u : ℝ) : W.X u ∈ Ioo W.lo W.hi := theta_mem hW _

theorem Sig_X (u : ℝ) : W.Sig (W.X u) = u := G_invR hW u

theorem ft_X (u : ℝ) : W.ft (W.X u) = u ^ 2 := by
  rw [← Sig_sq hW (X_mem hW u), Sig_X hW]

theorem X_Sig {x : ℝ} (hx : x ∈ Ioo W.lo W.hi) : W.X (W.Sig x) = x :=
  (Sig_strictMonoOn hW).injOn (X_mem hW _) hx (Sig_X hW _)

theorem X_smooth : ContDiff ℝ ∞ W.X :=
  (theta_contDiff hW).comp
    (Inner.invR_contDiff_of_deriv (G_contDiff hW) (G_deriv_pos hW) (G_top hW) (G_bot hW)).1

theorem X_deriv_pos (u : ℝ) : 0 < deriv W.X u := by
  obtain ⟨hs, hd⟩ := Inner.invR_contDiff_of_deriv (G_contDiff hW) (G_deriv_pos hW) (G_top hW)
    (G_bot hW)
  have h1 : HasDerivAt (invR W.G) (deriv (invR W.G) u) u :=
    (hs.differentiable (by simp) u).hasDerivAt
  have := (theta_hasDerivAt hW (invR W.G u)).comp u h1
  rw [show W.X = W.theta ∘ invR W.G from rfl, this.deriv, hd u]
  exact mul_pos (theta_deriv_pos hW _) (one_div_pos.mpr (G_deriv_pos hW _))

theorem X_strictMono : StrictMono W.X := strictMono_of_deriv_pos (X_deriv_pos hW)

/-- `X(u) = u/√(α/2)` for `|u| ≤ √(α/2) ε`. -/
theorem X_linear {u : ℝ} (hu : |u| ≤ W.lin * W.eps) : W.X u = u / W.lin := by
  have hl := lin_pos hW
  have hx : |u / W.lin| ≤ W.eps := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]; linarith
  have hmem : u / W.lin ∈ Ioo W.lo W.hi :=
    mem_of_abs_lt hW (by linarith [eps_le_r0 hW, r0_pos hW])
  have hS : W.Sig (u / W.lin) = u := by
    rw [Sig_linear hW hx]; field_simp
  conv_lhs => rw [← hS]
  exact X_Sig hW hmem

end hyp

end Well

end SymplecticPacking.Branch2.Planar
