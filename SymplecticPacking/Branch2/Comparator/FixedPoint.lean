import SymplecticPacking.Branch2.Comparator.Rearrange

/-!
# The finite comparator in one fibre coordinate (`prop:cmp-fixed-point`, `prop:fcp-fixed-point`, m = 1)

Data: an interval `[0, h]`, a continuous concave `P` on `[0, h]` with mean `μ > 0`, a core fraction
`τ ∈ (0,1)` with `P ≥ β > 0` on `[τh, h]`, a gap parameter `0 < d < min(μ, β)`, a lower bound
`P_min ≤ min P`, an upper bound `P̄ ≥ ‖P‖` and a Lipschitz constant `L_P` of `P`.

Explicit constants (paper `prop:cmp-fixed-point`, with lower/upper bounds in place of the exact
`min P`, `‖P‖`, which the paper allows):
`η = (1-τ)(μ-d)`, `B_P = max(1, d - P_min + 1)`, `λ = 1 - η/(2(B_P+η))`,
`K₀ = 0`, `K_{r+1} = R(λ K_r - P)`, and the number of steps
`N = ⌊(1-λ)⁻¹ log⁺(16 P̄/(d(1-λ)))⌋ + 1` (an explicit formula; any `N` at least the paper's least
admissible `N` works, see the proof of `prop:fcp-fixed-point` (e)).

Main result `iterN_gap`: `R(K_N - P) ≤ K_N - 7d/8` on `[0, h]`.
The fixed point `K_λ` of `T_λ` is used only in proofs (Banach's theorem; the vendored
`exists_convex_fixedPoint` may be used).
-/

noncomputable section

namespace SymplecticPacking.Branch2.Cmp

open Set

/-- Input data of the one-dimensional comparator. -/
structure Input where
  h : ℝ
  P : ℝ → ℝ
  tau : ℝ
  mu : ℝ
  beta : ℝ
  d : ℝ
  Pmin : ℝ
  Pbar : ℝ
  LP : ℝ

/-- Hypotheses of `prop:cmp-fixed-point` for `m = 1`. -/
structure Input.Hyp (D : Input) : Prop where
  h_pos : 0 < D.h
  cont : Continuous D.P
  concave : ConcaveOn ℝ (Icc 0 D.h) D.P
  mean : ∫ p in (0 : ℝ)..D.h, D.P p = D.mu * D.h
  tau_pos : 0 < D.tau
  tau_lt_one : D.tau < 1
  outer : ∀ p ∈ Icc (D.tau * D.h) D.h, D.beta ≤ D.P p
  d_pos : 0 < D.d
  d_lt_mu : D.d < D.mu
  d_lt_beta : D.d < D.beta
  Pmin_le : ∀ p ∈ Icc 0 D.h, D.Pmin ≤ D.P p
  abs_le : ∀ p ∈ Icc 0 D.h, |D.P p| ≤ D.Pbar
  Pbar_pos : 0 < D.Pbar
  LP_nonneg : 0 ≤ D.LP
  lip : ∀ x ∈ Icc 0 D.h, ∀ y ∈ Icc 0 D.h, |D.P x - D.P y| ≤ D.LP * |x - y|

namespace Input

variable (D : Input)

/-- `η = (1-τ)(μ-d)`. -/
def eta : ℝ := (1 - D.tau) * (D.mu - D.d)

/-- `B_P = max(1, d - P_min + 1)`. -/
def BP : ℝ := max 1 (D.d - D.Pmin + 1)

/-- `λ = 1 - η/(2(B_P + η))`. -/
def lam : ℝ := 1 - D.eta / (2 * (D.BP + D.eta))

/-- One step `T_λ(F) = R(λF - P)`. -/
def step (F : ℝ → ℝ) : ℝ → ℝ := rearr D.h (fun p => D.lam * F p - D.P p)

/-- The iterates `K_0 = 0`, `K_{r+1} = T_λ(K_r)`. -/
def iter : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | r + 1 => D.step (iter r)

/-- The number of steps `N = ⌊(1-λ)⁻¹ log⁺(16 P̄/(d(1-λ)))⌋ + 1`. -/
def nSteps : ℕ :=
  ⌊(1 - D.lam)⁻¹ * max 0 (Real.log (16 * D.Pbar / (D.d * (1 - D.lam))))⌋₊ + 1

/-- The comparison function before smoothing, `K_N`. -/
def KN : ℝ → ℝ := D.iter D.nSteps

/-- A Lipschitz constant of every iterate on `[0, h]`: `L_P/(1-λ)`. -/
def lipK : ℝ := D.LP / (1 - D.lam)

variable {D}

lemma Hyp.eta_pos (hD : D.Hyp) : 0 < D.eta :=
  mul_pos (by linarith [hD.tau_lt_one]) (by linarith [hD.d_lt_mu])

lemma BP_ge_one : 1 ≤ D.BP := le_max_left _ _

/-- `1/2 < λ < 1`. -/
lemma Hyp.lam_bounds (hD : D.Hyp) : 1 / 2 < D.lam ∧ D.lam < 1 := by
  have he := hD.eta_pos
  have hB := D.BP_ge_one
  have hpos : 0 < 2 * (D.BP + D.eta) := by linarith
  constructor
  · unfold lam
    have : D.eta / (2 * (D.BP + D.eta)) < 1 / 2 := by
      rw [div_lt_iff₀ hpos]; linarith
    linarith
  · unfold lam
    have : 0 < D.eta / (2 * (D.BP + D.eta)) := div_pos he hpos
    linarith

/-- `λη/(1-λ) = 2B_P + η > d - P_min`. -/
lemma Hyp.lam_identity (hD : D.Hyp) :
    D.lam * D.eta / (1 - D.lam) = 2 * D.BP + D.eta ∧ D.d - D.Pmin < 2 * D.BP + D.eta := by
  have he := hD.eta_pos
  have hB := D.BP_ge_one
  have hpos : 0 < 2 * (D.BP + D.eta) := by linarith
  refine ⟨?_, ?_⟩
  · have h1 : 1 - D.lam = D.eta / (2 * (D.BP + D.eta)) := by unfold lam; ring
    rw [h1]; unfold lam; field_simp; ring
  · have : D.d - D.Pmin + 1 ≤ D.BP := le_max_right _ _
    linarith

/-! ### Properties of the iterates (`prop:fcp-fixed-point` (b), (d)) -/

lemma Hyp.lipK_nonneg' (hD : D.Hyp) : 0 ≤ D.lipK :=
  div_nonneg hD.LP_nonneg (by linarith [hD.lam_bounds.2])

/-- `λ L_K + L_P = L_K`. -/
lemma Hyp.lam_lipK (hD : D.Hyp) : D.lam * D.lipK + D.LP = D.lipK := by
  have h1 : 1 - D.lam ≠ 0 := by linarith [hD.lam_bounds.2]
  unfold lipK; field_simp; ring

/-- The three properties preserved by the iteration. -/
lemma Hyp.iter_props (hD : D.Hyp) (r : ℕ) :
    ContinuousOn (D.iter r) (Icc 0 D.h) ∧
    (∀ x ∈ Icc 0 D.h, ∀ y ∈ Icc 0 D.h, |D.iter r x - D.iter r y| ≤ D.lipK * |x - y|) ∧
    ConvexOn ℝ (Icc 0 D.h) (D.iter r) := by
  have hlam := hD.lam_bounds
  have hK := hD.lipK_nonneg'
  induction r with
  | zero =>
    refine ⟨continuousOn_const, fun x _ y _ => ?_, convexOn_const 0 (convex_Icc 0 D.h)⟩
    simp only [iter, sub_self, abs_zero]
    exact mul_nonneg hK (abs_nonneg _)
  | succ r ih =>
    obtain ⟨hc, hl, hv⟩ := ih
    have hGc : ContinuousOn (fun p => D.lam * D.iter r p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul hc).sub hD.cont.continuousOn
    have hGl : ∀ x ∈ Icc 0 D.h, ∀ y ∈ Icc 0 D.h,
        |(D.lam * D.iter r x - D.P x) - (D.lam * D.iter r y - D.P y)| ≤ D.lipK * |x - y| := by
      intro x hx y hy
      have h1 := hl x hx y hy
      have h2 := hD.lip x hx y hy
      have e : (D.lam * D.iter r x - D.P x) - (D.lam * D.iter r y - D.P y) =
          D.lam * (D.iter r x - D.iter r y) - (D.P x - D.P y) := by ring
      rw [e]
      calc |D.lam * (D.iter r x - D.iter r y) - (D.P x - D.P y)|
          ≤ |D.lam * (D.iter r x - D.iter r y)| + |D.P x - D.P y| := abs_sub _ _
        _ = D.lam * |D.iter r x - D.iter r y| + |D.P x - D.P y| := by
            rw [abs_mul, abs_of_pos (by linarith)]
        _ ≤ D.lam * (D.lipK * |x - y|) + D.LP * |x - y| := by
            have hl0 : 0 ≤ D.lam := by linarith
            gcongr
        _ = (D.lam * D.lipK + D.LP) * |x - y| := by ring
        _ = D.lipK * |x - y| := by rw [hD.lam_lipK]
    have hGv : ConvexOn ℝ (Icc 0 D.h) (fun p => D.lam * D.iter r p - D.P p) :=
      (hv.smul (by linarith : (0 : ℝ) ≤ D.lam)).add hD.concave.neg
    exact ⟨rearr_continuousOn hGc hK hGl, rearr_lipschitz hGc hK hGl, rearr_convexOn hGc hGv⟩

lemma Hyp.iter_continuousOn (hD : D.Hyp) (r : ℕ) : ContinuousOn (D.iter r) (Icc 0 D.h) :=
  (hD.iter_props r).1

lemma Hyp.iter_convexOn (hD : D.Hyp) (r : ℕ) : ConvexOn ℝ (Icc 0 D.h) (D.iter r) :=
  (hD.iter_props r).2.2

/-- Every iterate is `L_P/(1-λ)`-Lipschitz on `[0, h]`. -/
lemma Hyp.iter_lipschitz (hD : D.Hyp) (r : ℕ) :
    ∀ x ∈ Icc 0 D.h, ∀ y ∈ Icc 0 D.h, |D.iter r x - D.iter r y| ≤ D.lipK * |x - y| :=
  (hD.iter_props r).2.1

lemma Hyp.iter_monotoneOn (hD : D.Hyp) (r : ℕ) : MonotoneOn (D.iter r) (Icc 0 D.h) := by
  cases r with
  | zero => exact fun _ _ _ _ _ => le_rfl
  | succ r =>
    obtain ⟨hc, -, hv⟩ := hD.iter_props r
    have hlam := hD.lam_bounds
    exact rearr_monotoneOn ((continuousOn_const.mul hc).sub hD.cont.continuousOn)
      ((hv.smul (by linarith : (0 : ℝ) ≤ D.lam)).add hD.concave.neg)

/-! ### The finite contraction estimate

The proof below works directly with the iterates (no fixed point is needed):
* consecutive iterates differ by at most `λ^r P̄` (`R` is sup-norm nonexpansive);
* `∫₀ʰ K_r = -μh(1-λ^r)/(1-λ)` (equimeasurability of `R`), hence `K_r(0) ≤ -μ(1-λ^r)/(1-λ)`;
* the maximum `K_r(h)` satisfies `(1-λ) K_r(h) ≤ λ^r P̄ - d` (the negative-maximum argument,
  using only the two endpoints of `[0, h]` and `(1-λ)(d - P_min) ≤ λ(μ - d)`);
* `λ^N P̄ ≤ d/16` by the choice of `N`. -/

/-- `R` of a constant function is that constant. -/
lemma rearr_const' {h c I : ℝ} (hI : I ∈ Icc 0 h) : rearr h (fun _ => c) I = c := by
  obtain ⟨a, -, he⟩ := rearr_attained (h := h) (f := fun _ => c) continuousOn_const hI
  simpa using he

/-- Sup-norm nonexpansiveness of `R`, two-sided form. -/
lemma rearr_abs_sub_le {h I ε : ℝ} {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 h))
    (hg : ContinuousOn g (Icc 0 h)) (hI : I ∈ Icc 0 h)
    (hfg : ∀ x ∈ Icc 0 h, |f x - g x| ≤ ε) :
    |rearr h f I - rearr h g I| ≤ ε := by
  have h1 := rearr_le_add hf hg hI (ε := ε) (fun x hx => by linarith [(abs_le.1 (hfg x hx)).2])
  have h2 := rearr_le_add hg hf hI (ε := ε) (fun x hx => by linarith [(abs_le.1 (hfg x hx)).1])
  rw [abs_le]; constructor <;> linarith

/-- Consecutive iterates: `|K_{r+1} - K_r| ≤ λ^r P̄` on `[0, h]`. -/
lemma Hyp.iter_succ_sub (hD : D.Hyp) (r : ℕ) :
    ∀ x ∈ Icc 0 D.h, |D.iter (r + 1) x - D.iter r x| ≤ D.lam ^ r * D.Pbar := by
  obtain ⟨hl1, hl2⟩ := hD.lam_bounds
  have hl0 : 0 < D.lam := by linarith
  induction r with
  | zero =>
    intro x hx
    have hf : ContinuousOn (fun p => D.lam * D.iter 0 p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul (hD.iter_continuousOn 0)).sub hD.cont.continuousOn
    have h1 := rearr_abs_sub_le hf (continuousOn_const (c := (0 : ℝ))) hx (ε := D.Pbar)
      (fun y hy => by
        show |D.lam * 0 - D.P y - 0| ≤ D.Pbar
        simpa using hD.abs_le y hy)
    rw [rearr_const' hx] at h1
    show |rearr D.h (fun p => D.lam * D.iter 0 p - D.P p) x - 0| ≤ D.lam ^ 0 * D.Pbar
    simpa using h1
  | succ r ih =>
    intro x hx
    have hf : ContinuousOn (fun p => D.lam * D.iter (r + 1) p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul (hD.iter_continuousOn (r + 1))).sub hD.cont.continuousOn
    have hg : ContinuousOn (fun p => D.lam * D.iter r p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul (hD.iter_continuousOn r)).sub hD.cont.continuousOn
    show |rearr D.h (fun p => D.lam * D.iter (r + 1) p - D.P p) x
        - rearr D.h (fun p => D.lam * D.iter r p - D.P p) x| ≤ D.lam ^ (r + 1) * D.Pbar
    apply rearr_abs_sub_le hf hg hx
    intro y hy
    have hy' := ih y hy
    have e : (D.lam * D.iter (r + 1) y - D.P y) - (D.lam * D.iter r y - D.P y) =
        D.lam * (D.iter (r + 1) y - D.iter r y) := by ring
    rw [e, abs_mul, abs_of_pos hl0]
    calc D.lam * |D.iter (r + 1) y - D.iter r y| ≤ D.lam * (D.lam ^ r * D.Pbar) :=
          mul_le_mul_of_nonneg_left hy' hl0.le
      _ = D.lam ^ (r + 1) * D.Pbar := by ring

/-- `∫₀ʰ K_r = -μh(1-λ^r)/(1-λ)`. -/
lemma Hyp.iter_integral (hD : D.Hyp) (r : ℕ) :
    ∫ x in (0 : ℝ)..D.h, D.iter r x = -(D.mu * D.h) * (1 - D.lam ^ r) / (1 - D.lam) := by
  obtain ⟨hl1, hl2⟩ := hD.lam_bounds
  have hs : (1 - D.lam) ≠ 0 := (by linarith : (0 : ℝ) < 1 - D.lam).ne'
  induction r with
  | zero =>
    show ∫ x in (0 : ℝ)..D.h, (0 : ℝ) = _
    simp
  | succ r ih =>
    have hc := hD.iter_continuousOn r
    have hGc : ContinuousOn (fun p => D.lam * D.iter r p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul hc).sub hD.cont.continuousOn
    have hGv : ConvexOn ℝ (Icc 0 D.h) (fun p => D.lam * D.iter r p - D.P p) :=
      ((hD.iter_convexOn r).smul (by linarith : (0 : ℝ) ≤ D.lam)).add hD.concave.neg
    have hi : IntervalIntegrable (D.iter r) MeasureTheory.volume 0 D.h := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hD.h_pos.le]; exact hc
    show ∫ x in (0 : ℝ)..D.h, rearr D.h (fun p => D.lam * D.iter r p - D.P p) x = _
    rw [rearr_integral hGc hGv hD.h_pos.le,
      intervalIntegral.integral_sub (hi.const_mul D.lam) (hD.cont.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, ih, hD.mean]
    field_simp
    ring

/-- The minimum: `(1-λ) K_r(0) ≤ -μ(1-λ^r)`. -/
lemma Hyp.iter_zero_le (hD : D.Hyp) (r : ℕ) :
    D.iter r 0 * (1 - D.lam) ≤ -D.mu * (1 - D.lam ^ r) := by
  have hh := hD.h_pos
  have hs : 0 < 1 - D.lam := by linarith [hD.lam_bounds.2]
  have hc := hD.iter_continuousOn r
  have hmono : ∫ _ in (0 : ℝ)..D.h, D.iter r 0 ≤ ∫ x in (0 : ℝ)..D.h, D.iter r x := by
    apply intervalIntegral.integral_mono_on hh.le intervalIntegrable_const
    · apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hh.le]; exact hc
    · intro x hx; exact hD.iter_monotoneOn r ⟨le_rfl, hh.le⟩ hx hx.1
  rw [hD.iter_integral r, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    le_div_iff₀ hs] at hmono
  exact le_of_mul_le_mul_left
    (by linarith : D.h * (D.iter r 0 * (1 - D.lam)) ≤ D.h * (-D.mu * (1 - D.lam ^ r))) hh

/-- `μ ≤ P̄`. -/
lemma Hyp.mu_le (hD : D.Hyp) : D.mu ≤ D.Pbar := by
  have hh := hD.h_pos
  have h1 : ∫ x in (0 : ℝ)..D.h, D.P x ≤ ∫ _ in (0 : ℝ)..D.h, D.Pbar :=
    intervalIntegral.integral_mono_on hh.le (hD.cont.intervalIntegrable _ _)
      intervalIntegrable_const (fun x hx => (le_abs_self _).trans (hD.abs_le x hx))
  rw [hD.mean, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  exact le_of_mul_le_mul_right (by linarith : D.mu * D.h ≤ D.Pbar * D.h) hh

/-- The maximum (negative-maximum argument): `(1-λ) K_r(h) ≤ λ^r P̄ - d`. -/
lemma Hyp.iter_top (hD : D.Hyp) (r : ℕ) :
    D.iter r D.h * (1 - D.lam) ≤ D.lam ^ r * D.Pbar - D.d := by
  obtain ⟨hl1, hl2⟩ := hD.lam_bounds
  have hh := hD.h_pos
  have hs : 0 < 1 - D.lam := by linarith
  have hl0 : 0 ≤ D.lam := by linarith
  have hhmem : D.h ∈ Icc 0 D.h := ⟨hh.le, le_rfl⟩
  have h0mem : (0 : ℝ) ∈ Icc 0 D.h := ⟨le_rfl, hh.le⟩
  have hPh : D.beta ≤ D.P D.h :=
    hD.outer _ ⟨by nlinarith [hD.tau_lt_one], le_rfl⟩
  have hdb := hD.d_lt_beta
  have hPbar_h : D.P D.h ≤ D.Pbar := (le_abs_self _).trans (hD.abs_le _ hhmem)
  have hmu := hD.mu_le
  have hkey : (1 - D.lam) * (D.d - D.Pmin) ≤ D.lam * (D.mu - D.d) := by
    obtain ⟨e1, e2⟩ := hD.lam_identity
    have he : D.lam * D.eta = (2 * D.BP + D.eta) * (1 - D.lam) := by
      rw [← e1]; field_simp
    have heta : D.eta ≤ D.mu - D.d := by
      unfold eta; nlinarith [hD.tau_pos, hD.d_lt_mu]
    have h3 : D.lam * D.eta ≤ D.lam * (D.mu - D.d) := mul_le_mul_of_nonneg_left heta hl0
    have h4 : (1 - D.lam) * (D.d - D.Pmin) ≤ (1 - D.lam) * (2 * D.BP + D.eta) :=
      mul_le_mul_of_nonneg_left e2.le hs.le
    linarith
  induction r with
  | zero =>
    show (0 : ℝ) * (1 - D.lam) ≤ D.lam ^ 0 * D.Pbar - D.d
    rw [pow_zero]; linarith
  | succ r ih =>
    have hc := hD.iter_continuousOn r
    have hGc : ContinuousOn (fun p => D.lam * D.iter r p - D.P p) (Icc 0 D.h) :=
      (continuousOn_const.mul hc).sub hD.cont.continuousOn
    have hle := rearr_le hGc hh.le (a := 0) ⟨le_rfl, by simp⟩
    simp only [zero_add] at hle
    have hA := hD.iter_zero_le r
    have hP0 := hD.Pmin_le 0 h0mem
    have hb : max (D.lam * D.iter r 0 - D.P 0) (D.lam * D.iter r D.h - D.P D.h) * (1 - D.lam)
        ≤ D.lam ^ (r + 1) * D.Pbar - D.d := by
      rw [max_mul_of_nonneg _ _ hs.le, pow_succ]
      have hpr : 0 ≤ D.lam ^ r * D.lam := mul_nonneg (pow_nonneg hl0 r) hl0
      apply max_le
      · have t1 := mul_le_mul_of_nonneg_left hA hl0
        have t2 := mul_le_mul_of_nonneg_left hP0 hs.le
        have t3 := mul_le_mul_of_nonneg_left hmu hpr
        nlinarith
      · have t1 := mul_le_mul_of_nonneg_left ih hl0
        have t2 := mul_le_mul_of_nonneg_left (by linarith : D.d ≤ D.P D.h) hs.le
        nlinarith
    show rearr D.h (fun p => D.lam * D.iter r p - D.P p) D.h * (1 - D.lam) ≤ _
    exact (mul_le_mul_of_nonneg_right hle hs.le).trans hb

/-- The choice of `N`: `λ^N P̄ ≤ d/16`. -/
lemma Hyp.pow_nSteps (hD : D.Hyp) : D.lam ^ D.nSteps * D.Pbar ≤ D.d / 16 := by
  obtain ⟨hl1, hl2⟩ := hD.lam_bounds
  have hs : 0 < 1 - D.lam := by linarith
  have hd := hD.d_pos
  have hP := hD.Pbar_pos
  have hN : (1 - D.lam)⁻¹ * max 0 (Real.log (16 * D.Pbar / (D.d * (1 - D.lam))))
      < (D.nSteps : ℝ) := by
    unfold nSteps; push_cast; exact Nat.lt_floor_add_one _
  have hNs : Real.log (16 * D.Pbar / (D.d * (1 - D.lam))) ≤ (D.nSteps : ℝ) * (1 - D.lam) := by
    have h1 := mul_lt_mul_of_pos_right hN hs
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hs.ne'] at h1
    linarith [le_max_right 0 (Real.log (16 * D.Pbar / (D.d * (1 - D.lam))))]
  have hexp : D.lam ≤ Real.exp (D.lam - 1) := by linarith [Real.add_one_le_exp (D.lam - 1)]
  have hpow : D.lam ^ D.nSteps ≤ Real.exp (-(Real.log (16 * D.Pbar / (D.d * (1 - D.lam))))) := by
    calc D.lam ^ D.nSteps ≤ Real.exp (D.lam - 1) ^ D.nSteps :=
          pow_le_pow_left₀ (by linarith) hexp _
      _ = Real.exp (D.nSteps * (D.lam - 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have harg : 0 < 16 * D.Pbar / (D.d * (1 - D.lam)) := by positivity
  rw [Real.exp_neg, Real.exp_log harg, inv_div] at hpow
  calc D.lam ^ D.nSteps * D.Pbar ≤ D.d * (1 - D.lam) / (16 * D.Pbar) * D.Pbar :=
        mul_le_mul_of_nonneg_right hpow hP.le
    _ = D.d * (1 - D.lam) / 16 := by field_simp
    _ ≤ D.d / 16 := by
        have : D.d * (1 - D.lam) ≤ D.d := by nlinarith
        linarith

/-- **`prop:cmp-fixed-point`.** `R(K_N - P) ≤ K_N - 7d/8` on `[0, h]`. -/
theorem Hyp.KN_gap (hD : D.Hyp) {I : ℝ} (hI : I ∈ Icc 0 D.h) :
    rearr D.h (fun p => D.KN p - D.P p) I ≤ D.KN I - 7 * D.d / 8 := by
  obtain ⟨hl1, hl2⟩ := hD.lam_bounds
  have hh := hD.h_pos
  have hs : 0 < 1 - D.lam := by linarith
  have hc := hD.iter_continuousOn D.nSteps
  have hf : ContinuousOn (fun p => D.iter D.nSteps p - D.P p) (Icc 0 D.h) :=
    hc.sub hD.cont.continuousOn
  have hg : ContinuousOn (fun p => D.lam * D.iter D.nSteps p - D.P p) (Icc 0 D.h) :=
    (continuousOn_const.mul hc).sub hD.cont.continuousOn
  have hhmem : D.h ∈ Icc 0 D.h := ⟨hh.le, le_rfl⟩
  have h1 := rearr_le_add hf hg hI (ε := (1 - D.lam) * D.iter D.nSteps D.h) (fun x hx => by
    have t := mul_le_mul_of_nonneg_left (hD.iter_monotoneOn D.nSteps hx hhmem hx.2) hs.le
    nlinarith)
  have h2 : rearr D.h (fun p => D.lam * D.iter D.nSteps p - D.P p) I
      ≤ D.iter D.nSteps I + D.lam ^ D.nSteps * D.Pbar := by
    have t := hD.iter_succ_sub D.nSteps I hI
    rw [_root_.abs_le] at t
    have t := t.2
    change D.iter (D.nSteps + 1) I ≤ _
    linarith
  have h3 := hD.iter_top D.nSteps
  have h4 := hD.pow_nSteps
  show rearr D.h (fun p => D.iter D.nSteps p - D.P p) I ≤ D.iter D.nSteps I - 7 * D.d / 8
  nlinarith

end Input

end SymplecticPacking.Branch2.Cmp
