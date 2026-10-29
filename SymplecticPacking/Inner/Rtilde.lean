import SymplecticPacking.InnerConstants

/-!
# The quadratic modification `R̃` of the hyperbola

`sec:pll`, subsection `sec:pll-morse`, x-side: the cutoff `ψ_R`, the scales
`ε_R, κ_R, δ'`, the exactly quadratic modification `Rtilde` of the hyperbola `R = Rmorse`,
and Lemmas `lem:pll-taylor`, `lem:pll-Rtilde-close`, `lem:pll-Rtilde-mono` of the supplement.
-/

noncomputable section

open Real Filter Topology Set
open scoped ContDiff

namespace SymplecticPacking

namespace Params

variable (P : Params)

/-- The curvature `α₀ = r³/(η n²) = R''(0)` (Def. `def:pll-curvatures`). -/
def alpha0 : ℝ := P.r ^ 3 / (P.eta * P.n ^ 2)

lemma alpha0_pos : 0 < P.alpha0 := by
  have := P.r_pos; have := P.eta_pos; have := P.n_pos
  unfold alpha0; positivity

end Params

namespace Inner

/-! ### A generic integration lemma -/

private lemma abs_le_of_hasDerivAt_abs_le_aux {f f' : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t, |f' t| ≤ c * |t| ^ k) {x : ℝ} (hx : 0 ≤ x) :
    |f x| ≤ c * x ^ (k + 1) / (k + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hpow : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c * t ^ (k + 1) / (k + 1)) (c * t ^ k) t := by
    intro t
    have := ((hasDerivAt_pow (k + 1) t).const_mul c).div_const ((k : ℝ) + 1)
    convert this using 1
    rw [Nat.add_sub_cancel]; push_cast; field_simp
  have mono : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      MonotoneOn (fun t => c * t ^ (k + 1) / (k + 1) - s * f t) (Ici 0) := by
    intro s hs
    have hd : ∀ t, HasDerivAt (fun t => c * t ^ (k + 1) / (k + 1) - s * f t)
        (c * t ^ k - s * f' t) t := fun t => (hpow t).sub ((hf t).const_mul s)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      have h1 := hb t
      rw [abs_of_pos (show (0 : ℝ) < t from ht)] at h1
      have : |s * f' t| = |f' t| := by rcases hs with rfl | rfl <;> simp
      have h2 := le_abs_self (s * f' t)
      linarith
  have e0 : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
  have h1 := mono 1 (Or.inl rfl) Set.self_mem_Ici hx hx
  have h2 := mono (-1) (Or.inr rfl) Set.self_mem_Ici hx hx
  simp only [e0, h0, mul_zero, zero_div, sub_zero] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- If `f 0 = 0` and `|f'(t)| ≤ c |t|^k` then `|f x| ≤ c |x|^(k+1)/(k+1)`. -/
lemma abs_le_of_hasDerivAt_abs_le {f f' : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t, |f' t| ≤ c * |t| ^ k) (x : ℝ) :
    |f x| ≤ c * |x| ^ (k + 1) / (k + 1) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact abs_le_of_hasDerivAt_abs_le_aux k hf h0 hb hx
  · have := abs_le_of_hasDerivAt_abs_le_aux (f := fun t => f (-t)) (f' := fun t => -f' (-t)) k
      (fun t => by
        have h := (hf (-t)).comp t (hasDerivAt_neg t)
        simpa [Function.comp_def] using h)
      (by simp [h0]) (fun t => by simpa using hb (-t)) (x := -x) (by linarith)
    have e : |x| = -x := abs_of_nonpos hx
    rw [e]; simpa only [neg_neg] using this

/-! ### Derivatives of the hyperbola `R` -/

variable (P : Params)

/-- `s(x) = √((x*+x)² + η²)`. -/
def sR (x : ℝ) : ℝ := Real.sqrt ((P.xstar + x) ^ 2 + P.eta ^ 2)

lemma sR_pos (x : ℝ) : 0 < sR P x :=
  Real.sqrt_pos.2 (by have := P.eta_pos; positivity)

lemma sR_sq (x : ℝ) : sR P x ^ 2 = (P.xstar + x) ^ 2 + P.eta ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma sR_zero : sR P 0 = P.eta * P.n / P.r := by
  have hr := P.r_pos
  have hn := P.n_pos
  have he := P.eta_pos
  have hsq : P.xstar ^ 2 + P.eta ^ 2 = (P.eta * P.n / P.r) ^ 2 := by
    unfold Params.xstar
    have := P.n_sq_sub_m_sq
    field_simp
    nlinarith
  unfold sR; rw [add_zero, hsq, Real.sqrt_sq (by positivity)]

lemma hasDerivAt_sR (x : ℝ) : HasDerivAt (sR P) ((P.xstar + x) / sR P x) x := by
  have h1 : HasDerivAt (fun x => P.xstar + x) 1 x := (hasDerivAt_id' x).const_add _
  have h2 := (h1.pow 2).add_const (P.eta ^ 2)
  have := h2.sqrt (by have := P.eta_pos; simp only [Pi.pow_apply]; positivity)
  refine this.congr_deriv ?_
  rw [show (((2 : ℕ) : ℝ) * (P.xstar + x) ^ (2 - 1) * 1) = 2 * (P.xstar + x) by norm_num]
  rw [mul_div_mul_left _ _ two_ne_zero]; rfl

/-- `R'(x) = m + n w / s`. -/
def Rmorse1 (x : ℝ) : ℝ := P.m + P.n * (P.xstar + x) / sR P x
/-- `R''(x) = n η² / s³`. -/
def Rmorse2 (x : ℝ) : ℝ := P.n * P.eta ^ 2 / sR P x ^ 3
/-- `R'''(x) = -3 n η² w / s⁵`. -/
def Rmorse3 (x : ℝ) : ℝ := -3 * P.n * P.eta ^ 2 * (P.xstar + x) / sR P x ^ 5

lemma hasDerivAt_Rmorse (x : ℝ) : HasDerivAt P.Rmorse (Rmorse1 P x) x := by
  have h1 : HasDerivAt (fun x => P.xstar + x) 1 x := (hasDerivAt_id' x).const_add _
  have := ((h1.const_mul P.m).add ((hasDerivAt_sR P x).const_mul P.n)).sub_const (P.eta * P.r)
  refine this.congr_deriv ?_
  unfold Rmorse1; ring

lemma hasDerivAt_Rmorse1 (x : ℝ) : HasDerivAt (Rmorse1 P) (Rmorse2 P x) x := by
  have h1 : HasDerivAt (fun x => P.xstar + x) 1 x := (hasDerivAt_id' x).const_add _
  have hs := (sR_pos P x).ne'
  have := ((h1.div (hasDerivAt_sR P x) hs).const_mul P.n).const_add P.m
  have e : Rmorse1 P = fun y => P.m + P.n * ((fun x => P.xstar + x) / sR P) y := by
    funext y; simp only [Pi.div_apply]; unfold Rmorse1; ring
  rw [e]
  refine this.congr_deriv ?_
  rw [show (1 * sR P x - (P.xstar + x) * ((P.xstar + x) / sR P x)) / sR P x ^ 2
      = (sR P x ^ 2 - (P.xstar + x) ^ 2) / sR P x ^ 3 by field_simp]
  rw [sR_sq]; unfold Rmorse2; ring

lemma hasDerivAt_Rmorse2 (x : ℝ) : HasDerivAt (Rmorse2 P) (Rmorse3 P x) x := by
  have hs := (sR_pos P x).ne'
  have := (hasDerivAt_const x (P.n * P.eta ^ 2)).div ((hasDerivAt_sR P x).pow 3)
    (pow_ne_zero 3 hs)
  refine this.congr_deriv ?_
  unfold Rmorse3
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma Rmorse2_pos (x : ℝ) : 0 < Rmorse2 P x := by
  have := sR_pos P x; have := P.n_pos; have := P.eta_pos
  unfold Rmorse2; positivity

lemma Rmorse1_zero : Rmorse1 P 0 = 0 := by
  have := P.r_pos.ne'; have := P.n_pos.ne'; have := P.eta_pos.ne'
  unfold Rmorse1; rw [sR_zero]; unfold Params.xstar
  field_simp; ring

lemma Rmorse2_zero : Rmorse2 P 0 = P.alpha0 := by
  have := P.r_pos.ne'; have := P.n_pos.ne'; have := P.eta_pos.ne'
  unfold Rmorse2; rw [sR_zero]; unfold Params.alpha0
  field_simp

lemma deriv_Rmorse : deriv P.Rmorse = Rmorse1 P := funext fun x => (hasDerivAt_Rmorse P x).deriv
lemma deriv_Rmorse1 : deriv (Rmorse1 P) = Rmorse2 P :=
  funext fun x => (hasDerivAt_Rmorse1 P x).deriv
lemma deriv_Rmorse2 : deriv (Rmorse2 P) = Rmorse3 P :=
  funext fun x => (hasDerivAt_Rmorse2 P x).deriv

/-- `K₃ = n / η²`. -/
def K3 : ℝ := P.n / P.eta ^ 2

lemma K3_pos : 0 < K3 P := by
  have := P.n_pos; have := P.eta_pos; unfold K3; positivity

/-- **Lemma `lem:pll-taylor`(i)**: `R''' = -3nη² w (w²+η²)^{-5/2}` and `|R'''| ≤ n/η²`. -/
theorem Rmorse_deriv3_le (x : ℝ) :
    deriv (deriv (deriv P.Rmorse)) x = Rmorse3 P x ∧ |Rmorse3 P x| ≤ K3 P := by
  refine ⟨by rw [deriv_Rmorse, deriv_Rmorse1, deriv_Rmorse2], ?_⟩
  set w := P.xstar + x
  set s := sR P x
  have hs := sR_pos P x
  have hsq : s ^ 2 = w ^ 2 + P.eta ^ 2 := sR_sq P x
  have he := P.eta_pos
  have hn := P.n_pos
  -- key: 3 η⁴ |w| ≤ s⁵
  have hkey : 3 * P.eta ^ 4 * |w| ≤ s ^ 5 := by
    have hpoly : 9 * (P.eta ^ 2) ^ 4 * w ^ 2 ≤ (w ^ 2 + P.eta ^ 2) ^ 5 := by
      have e : (w ^ 2 + P.eta ^ 2) ^ 5 - 9 * (P.eta ^ 2) ^ 4 * w ^ 2 =
          (P.eta ^ 2) ^ 3 * ((P.eta ^ 2 - 2 * w ^ 2) ^ 2 + 6 * (w ^ 2) ^ 2) + (w ^ 2) ^ 5
            + 5 * (w ^ 2) ^ 4 * P.eta ^ 2 + 10 * (w ^ 2) ^ 3 * (P.eta ^ 2) ^ 2 := by ring
      have : 0 ≤ (P.eta ^ 2) ^ 3 * ((P.eta ^ 2 - 2 * w ^ 2) ^ 2 + 6 * (w ^ 2) ^ 2) + (w ^ 2) ^ 5
            + 5 * (w ^ 2) ^ 4 * P.eta ^ 2 + 10 * (w ^ 2) ^ 3 * (P.eta ^ 2) ^ 2 := by positivity
      linarith
    have hL : (3 * P.eta ^ 4 * |w|) ^ 2 = 9 * (P.eta ^ 2) ^ 4 * w ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    have hR : (s ^ 5) ^ 2 = (w ^ 2 + P.eta ^ 2) ^ 5 := by rw [← hsq]; ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp (by rw [hL, hR]; exact hpoly)
  have habs : |Rmorse3 P x| = 3 * P.n * P.eta ^ 2 * |w| / s ^ 5 := by
    unfold Rmorse3
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 5)]
    rw [show -3 * P.n * P.eta ^ 2 * w = -(3 * P.n * P.eta ^ 2 * w) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 3 * P.n * P.eta ^ 2)]
  rw [habs]; unfold K3
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hkey hn.le
  nlinarith

/-! ### The cutoff and the scales (Def. `cons:pll-morse`) -/

/-- The cutoff `ψ_R(t) = 1 - S((t²-1)/3)`. -/
def psiR (t : ℝ) : ℝ := 1 - Real.smoothTransition ((t ^ 2 - 1) / 3)

lemma psiR_contDiff : ContDiff ℝ ∞ psiR := by
  unfold psiR
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_id.pow 2).sub contDiff_const).div_const 3))

lemma psiR_differentiable : Differentiable ℝ psiR :=
  psiR_contDiff.differentiable (by simp)

lemma psiR_nonneg (t : ℝ) : 0 ≤ psiR t := by
  unfold psiR; linarith [Real.smoothTransition.le_one ((t ^ 2 - 1) / 3)]

lemma psiR_le_one (t : ℝ) : psiR t ≤ 1 := by
  unfold psiR; linarith [Real.smoothTransition.nonneg ((t ^ 2 - 1) / 3)]

lemma psiR_eq_one {t : ℝ} (ht : |t| ≤ 1) : psiR t = 1 := by
  unfold psiR
  rw [Real.smoothTransition.zero_of_nonpos, sub_zero]
  have : t ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  linarith

lemma psiR_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : psiR t = 0 := by
  unfold psiR
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  have : 4 ≤ t ^ 2 := by
    rw [← sq_abs]; nlinarith
  rw [le_div_iff₀ (by norm_num)]; linarith

lemma psiR_hasCompactSupport : HasCompactSupport psiR := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) (fun t ht => ?_)
  apply psiR_eq_zero
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `C_ψ = sup |ψ_R'|`. -/
def Cpsi : ℝ := ⨆ t, |deriv psiR t|

lemma bddAbove_abs_deriv_psiR : BddAbove (Set.range fun t => |deriv psiR t|) := by
  have hc : Continuous (deriv psiR) := psiR_contDiff.continuous_deriv (by simp)
  have := hc.norm.bddAbove_range_of_hasCompactSupport psiR_hasCompactSupport.deriv.norm
  simpa [Real.norm_eq_abs] using this

lemma abs_deriv_psiR_le (t : ℝ) : |deriv psiR t| ≤ Cpsi :=
  le_ciSup bddAbove_abs_deriv_psiR t

lemma Cpsi_nonneg : 0 ≤ Cpsi := le_trans (abs_nonneg _) (abs_deriv_psiR_le 0)

/-- `ε_R = e r³ / (256 n⁴ (1 + C_ψ))`. -/
def epsR : ℝ := P.eq_ * P.r ^ 3 / (256 * P.n ^ 4 * (1 + Cpsi))
/-- `κ_R = e / 196608`. -/
def kappaR : ℝ := P.eq_ / 196608
/-- `δ' = δ + κ_R`. -/
def deltaPrime : ℝ := P.delta + kappaR P

lemma epsR_pos : 0 < epsR P := by
  have := P.eq_pos; have := P.r_pos; have := P.n_pos; have := Cpsi_nonneg
  unfold epsR; positivity

lemma kappaR_pos : 0 < kappaR P := by have := P.eq_pos; unfold kappaR; positivity

/-! ### The modified Morse function (Def. `cons:pll-morse`) -/

/-- `g(x) = α₀ x²/2 - R(x)`. -/
def gcub (x : ℝ) : ℝ := P.alpha0 * x ^ 2 / 2 - P.Rmorse x
/-- `g'`. -/
def gcub1 (x : ℝ) : ℝ := P.alpha0 * x - Rmorse1 P x
/-- `g''`. -/
def gcub2 (x : ℝ) : ℝ := P.alpha0 - Rmorse2 P x

/-- `R̃(x) = R(x) + ψ_R(x/ε_R) g(x)`. -/
def Rtilde (x : ℝ) : ℝ := P.Rmorse x + psiR (x / epsR P) * gcub P x

lemma hasDerivAt_gcub (x : ℝ) : HasDerivAt (gcub P) (gcub1 P x) x := by
  have := (((hasDerivAt_pow 2 x).const_mul P.alpha0).div_const 2).sub (hasDerivAt_Rmorse P x)
  refine this.congr_deriv ?_
  unfold gcub1; push_cast; ring

lemma hasDerivAt_gcub1 (x : ℝ) : HasDerivAt (gcub1 P) (gcub2 P x) x := by
  have := ((hasDerivAt_id' x).const_mul P.alpha0).sub (hasDerivAt_Rmorse1 P x)
  refine this.congr_deriv ?_
  unfold gcub2; ring

lemma hasDerivAt_gcub2 (x : ℝ) : HasDerivAt (gcub2 P) (-Rmorse3 P x) x := by
  have := (hasDerivAt_Rmorse2 P x).const_sub P.alpha0
  exact this

lemma gcub_zero : gcub P 0 = 0 := by unfold gcub; rw [P.Rmorse_zero]; ring
lemma gcub1_zero : gcub1 P 0 = 0 := by unfold gcub1; rw [Rmorse1_zero]; ring
lemma gcub2_zero : gcub2 P 0 = 0 := by unfold gcub2; rw [Rmorse2_zero]; ring

lemma gcub2_abs_le (x : ℝ) : |gcub2 P x| ≤ K3 P * |x| := by
  have := abs_le_of_hasDerivAt_abs_le (c := K3 P) 0 (hasDerivAt_gcub2 P) (gcub2_zero P)
    (fun t => by simpa using (Rmorse_deriv3_le P t).2) x
  simpa using this

lemma gcub1_abs_le (x : ℝ) : |gcub1 P x| ≤ K3 P * x ^ 2 / 2 := by
  have := abs_le_of_hasDerivAt_abs_le (c := K3 P) 1 (hasDerivAt_gcub1 P) (gcub1_zero P)
    (fun t => by simpa using gcub2_abs_le P t) x
  calc |gcub1 P x| ≤ _ := this
    _ = K3 P * x ^ 2 / 2 := by norm_num [sq_abs]

lemma gcub_abs_le (x : ℝ) : |gcub P x| ≤ K3 P * |x| ^ 3 / 6 := by
  have := abs_le_of_hasDerivAt_abs_le (c := K3 P / 2) 2 (hasDerivAt_gcub P) (gcub_zero P)
    (fun t => by
      have := gcub1_abs_le P t
      rw [← sq_abs] at this
      linarith) x
  calc |gcub P x| ≤ _ := this
    _ = K3 P * |x| ^ 3 / 6 := by norm_num; ring

/-- **Lemma `lem:pll-taylor`(iii)**: `K₃ ε_R = α₀ / (32 (1 + C_ψ))`. -/
theorem epsR_mul_K3 : K3 P * epsR P = P.alpha0 / (32 * (1 + Cpsi)) := by
  have := P.r_pos.ne'; have := P.n_pos.ne'; have := P.eq_pos.ne'
  have : (1 + Cpsi) ≠ 0 := by linarith [Cpsi_nonneg]
  unfold K3 epsR Params.alpha0 Params.eta
  field_simp
  ring

/-- `R̃ = α₀x²/2` for `|x| ≤ ε_R`. -/
theorem Rtilde_eq_quad {x : ℝ} (hx : |x| ≤ epsR P) : Rtilde P x = P.alpha0 * x ^ 2 / 2 := by
  have he := epsR_pos P
  have : psiR (x / epsR P) = 1 := by
    apply psiR_eq_one
    rw [abs_div, abs_of_pos he, div_le_one he]; exact hx
  unfold Rtilde gcub; rw [this]; ring

/-- `R̃ = R` for `|x| ≥ 2 ε_R`. -/
theorem Rtilde_eq_far {x : ℝ} (hx : 2 * epsR P ≤ |x|) : Rtilde P x = P.Rmorse x := by
  have he := epsR_pos P
  have : psiR (x / epsR P) = 0 := by
    apply psiR_eq_zero
    rw [abs_div, abs_of_pos he, le_div_iff₀ he]; exact hx
  unfold Rtilde; rw [this]; ring

lemma Rtilde_zero : Rtilde P 0 = 0 := by
  rw [Rtilde_eq_quad P (by rw [abs_zero]; exact (epsR_pos P).le)]; ring

/-! ### Closeness (Lemma `lem:pll-Rtilde-close`) -/

/-- `|R̃ - R| ≤ κ_R`. -/
theorem Rtilde_close (x : ℝ) : |Rtilde P x - P.Rmorse x| ≤ kappaR P := by
  have he := epsR_pos P
  have hk := kappaR_pos P
  rcases le_or_gt (2 * epsR P) |x| with hx | hx
  · rw [Rtilde_eq_far P hx, sub_self, abs_zero]; exact hk.le
  have h1 : |Rtilde P x - P.Rmorse x| ≤ |gcub P x| := by
    unfold Rtilde
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (psiR_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (psiR_le_one _)
  have h2 : |gcub P x| ≤ K3 P * (2 * epsR P) ^ 3 / 6 := by
    refine (gcub_abs_le P x).trans ?_
    have := K3_pos P
    gcongr
  have hC := Cpsi_nonneg
  have hid : K3 P * (2 * epsR P) ^ 3 / 6 = kappaR P * (P.r / P.n) ^ 9 / (1 + Cpsi) ^ 3 := by
    have := P.r_pos.ne'; have := P.n_pos.ne'; have := P.eq_pos.ne'
    have : (1 + Cpsi) ≠ 0 := by linarith
    unfold K3 epsR kappaR Params.eta
    field_simp
    ring
  have hrn : (P.r / P.n) ^ 9 ≤ 1 :=
    pow_le_one₀ (div_nonneg P.r_pos.le P.n_pos.le) ((div_le_one P.n_pos).2 P.r_le_n)
  have hD : 1 ≤ (1 + Cpsi) ^ 3 := one_le_pow₀ (by linarith)
  have h3 : kappaR P * (P.r / P.n) ^ 9 / (1 + Cpsi) ^ 3 ≤ kappaR P := by
    rw [div_le_iff₀ (by positivity)]
    calc kappaR P * (P.r / P.n) ^ 9 ≤ kappaR P * 1 := mul_le_mul_of_nonneg_left hrn hk.le
      _ ≤ kappaR P * (1 + Cpsi) ^ 3 := mul_le_mul_of_nonneg_left hD hk.le
  linarith

/-- `|R̃(p - p*) - Rcal(p)| ≤ δ' = δ + κ_R`. -/
theorem Rtilde_Rcal_close (x : ℝ) :
    |Rtilde P (x - P.pstar) - P.Rcal x| ≤ deltaPrime P := by
  have h1 := Rtilde_close P (x - P.pstar)
  have h2 := P.Rmorse_close x
  have := abs_sub_le (Rtilde P (x - P.pstar)) (P.Rmorse (x - P.pstar)) (P.Rcal x)
  unfold deltaPrime; linarith

/-! ### Smoothness and monotonicity (Lemma `lem:pll-Rtilde-mono`) -/

lemma Rmorse_contDiff : ContDiff ℝ ∞ P.Rmorse := by
  have hq : ContDiff ℝ ∞ fun x : ℝ => (P.xstar + x) ^ 2 + P.eta ^ 2 :=
    ((contDiff_const.add contDiff_id).pow 2).add contDiff_const
  have hs := hq.sqrt (fun x => by have := P.eta_pos; positivity)
  exact ((contDiff_const.mul (contDiff_const.add contDiff_id)).add
    (contDiff_const.mul hs)).sub contDiff_const

lemma gcub_contDiff : ContDiff ℝ ∞ (gcub P) :=
  ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2).sub (Rmorse_contDiff P)

theorem Rtilde_smooth : ContDiff ℝ ∞ (Rtilde P) :=
  (Rmorse_contDiff P).add
    ((psiR_contDiff.comp (contDiff_id.div_const _)).mul (gcub_contDiff P))

/-- The derivative of `R̃`. -/
def Rtilde1 (x : ℝ) : ℝ :=
  Rmorse1 P x + deriv psiR (x / epsR P) / epsR P * gcub P x + psiR (x / epsR P) * gcub1 P x

lemma hasDerivAt_Rtilde (x : ℝ) : HasDerivAt (Rtilde P) (Rtilde1 P x) x := by
  have hψ := (psiR_differentiable (x / epsR P)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const (epsR P))
  have := (hasDerivAt_Rmorse P x).add (hψ.mul (hasDerivAt_gcub P x))
  refine this.congr_deriv ?_
  unfold Rtilde1; simp only [id, Function.comp_apply]; ring

lemma deriv_Rtilde (x : ℝ) : deriv (Rtilde P) x = Rtilde1 P x := (hasDerivAt_Rtilde P x).deriv

lemma Rmorse1_strictMono : StrictMono (Rmorse1 P) :=
  strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_Rmorse1 P x).deriv]; exact Rmorse2_pos P x

lemma mul_Rmorse1_pos {x : ℝ} (hx : x ≠ 0) : 0 < x * Rmorse1 P x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have := Rmorse1_strictMono P h; rw [Rmorse1_zero] at this
    exact mul_pos_of_neg_of_neg h this
  · have := Rmorse1_strictMono P h; rw [Rmorse1_zero] at this
    exact mul_pos h this

/-- Near estimate: for `|x| ≤ 2 ε_R`, `x R̃'(x) ≥ (91/96) α₀ x²`
(equivalently `sign(x) R̃'(x) ≥ (91/96) α₀ |x|`). -/
theorem Rtilde_deriv_near {x : ℝ} (hx : |x| ≤ 2 * epsR P) :
    91 / 96 * P.alpha0 * x ^ 2 ≤ x * deriv (Rtilde P) x := by
  rw [deriv_Rtilde]
  have e : x * Rtilde1 P x = P.alpha0 * x ^ 2 - (1 - psiR (x / epsR P)) * (x * gcub1 P x)
      + x * (deriv psiR (x / epsR P) / epsR P * gcub P x) := by
    unfold Rtilde1 gcub1; ring
  set ε := epsR P with hε
  set a := P.alpha0
  set K := K3 P
  set C := Cpsi
  set ψ := psiR (x / ε)
  set d := deriv psiR (x / ε)
  set G := gcub P x
  set G1 := gcub1 P x
  set u := |x|
  have he : 0 < ε := epsR_pos P
  have ha : 0 < a := P.alpha0_pos
  have hK : 0 < K := K3_pos P
  have hC : 0 ≤ C := Cpsi_nonneg
  have hu : 0 ≤ u := abs_nonneg x
  have hx2 : x ^ 2 = u ^ 2 := (sq_abs x).symm
  have hKe : K * ε = a / (32 * (1 + C)) := epsR_mul_K3 P
  have hG1 : |G1| ≤ K * x ^ 2 / 2 := gcub1_abs_le P x
  have hG : |G| ≤ K * u ^ 3 / 6 := gcub_abs_le P x
  have hd : |d| ≤ C := abs_deriv_psiR_le _
  have hψ0 : 0 ≤ ψ := psiR_nonneg _
  have hψ1 : ψ ≤ 1 := psiR_le_one _
  -- first error term
  have h1 : |x * G1| ≤ (K * ε) * x ^ 2 := by
    rw [abs_mul]
    calc u * |G1| ≤ u * (K * x ^ 2 / 2) := mul_le_mul_of_nonneg_left hG1 hu
      _ = K * x ^ 2 * (u / 2) := by ring
      _ ≤ K * x ^ 2 * ε := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (K * ε) * x ^ 2 := by ring
  -- second error term
  have h2 : |x * (d / ε * G)| ≤ 2 / 3 * C * (K * ε) * x ^ 2 := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos he]
    have hu2 : u ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
    have : u * (|d| * |G|) ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε := by
      calc u * (|d| * |G|) ≤ u * (C * (K * u ^ 3 / 6)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hd hG (abs_nonneg _) hC) hu
        _ = C * K * u ^ 2 * u ^ 2 / 6 := by ring
        _ ≤ C * K * u ^ 2 * (4 * ε ^ 2) / 6 := by gcongr
        _ = 2 / 3 * C * (K * ε) * x ^ 2 * ε := by rw [hx2]; ring
    calc u * (|d| / ε * |G|) = u * (|d| * |G|) / ε := by ring
      _ ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε / ε := by gcongr
      _ = 2 / 3 * C * (K * ε) * x ^ 2 := by field_simp
  -- size of `K ε`
  have hKe1 : (K * ε) * x ^ 2 ≤ a / 32 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    rw [hKe]; apply div_le_div_of_nonneg_left ha.le (by norm_num); nlinarith
  have hKe2 : 2 / 3 * C * (K * ε) * x ^ 2 ≤ a / 48 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    rw [hKe, show 2 / 3 * C * (a / (32 * (1 + C))) = a / 48 * (C / (1 + C)) by
      field_simp; ring]
    have : C / (1 + C) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith
  have b1 : (1 - ψ) * (x * G1) ≤ |x * G1| :=
    calc (1 - ψ) * (x * G1) ≤ (1 - ψ) * |x * G1| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ 1 * |x * G1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |x * G1| := one_mul _
  have b2 := neg_abs_le (x * (d / ε * G))
  rw [e]
  nlinarith

/-- **Lemma `lem:pll-Rtilde-mono`** (sign statement): `sign(x) R̃'(x) > 0` for `x ≠ 0`,
stated as `0 < x · R̃'(x)`. -/
theorem Rtilde_mono {x : ℝ} (hx : x ≠ 0) : 0 < x * deriv (Rtilde P) x := by
  rcases le_or_gt |x| (2 * epsR P) with h | h
  · have := Rtilde_deriv_near P h
    have : 0 < 91 / 96 * P.alpha0 * x ^ 2 := by
      have := P.alpha0_pos; have := pow_pos (abs_pos.2 hx) 2; rw [sq_abs] at this; positivity
    linarith
  · have hev : Rtilde P =ᶠ[𝓝 x] P.Rmorse := by
      have hopen : IsOpen {y : ℝ | 2 * epsR P < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds h] with y hy
      exact Rtilde_eq_far P (le_of_lt hy)
    rw [hev.deriv_eq, deriv_Rmorse]
    exact mul_Rmorse1_pos P hx

lemma Rtilde_deriv_pos {x : ℝ} (hx : 0 < x) : 0 < deriv (Rtilde P) x :=
  (pos_iff_pos_of_mul_pos (Rtilde_mono P hx.ne')).mp hx

lemma Rtilde_deriv_neg {x : ℝ} (hx : x < 0) : deriv (Rtilde P) x < 0 :=
  neg_of_mul_pos_right (Rtilde_mono P hx.ne) hx.le

lemma Rtilde_continuous : Continuous (Rtilde P) := (Rtilde_smooth P).continuous

theorem Rtilde_strictMonoOn : StrictMonoOn (Rtilde P) (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) (Rtilde_continuous P).continuousOn
    (fun x hx => by rw [interior_Ici] at hx; exact Rtilde_deriv_pos P hx)

theorem Rtilde_strictAntiOn : StrictAntiOn (Rtilde P) (Iic 0) :=
  strictAntiOn_of_deriv_neg (convex_Iic 0) (Rtilde_continuous P).continuousOn
    (fun x hx => by rw [interior_Iic] at hx; exact Rtilde_deriv_neg P hx)

/-- `R̃(x) > 0` for `x ≠ 0` (and `R̃(0) = 0`). -/
theorem Rtilde_pos {x : ℝ} (hx : x ≠ 0) : 0 < Rtilde P x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have := Rtilde_strictAntiOn P (Set.mem_Iic.2 h.le) Set.self_mem_Iic h
    rwa [Rtilde_zero] at this
  · have := Rtilde_strictMonoOn P Set.self_mem_Ici (Set.mem_Ici.2 h.le) h
    rwa [Rtilde_zero] at this

/-! ### Growth at infinity -/

lemma abs_m_lt_n : |P.m| < P.n := by
  rw [abs_lt]; unfold Params.m Params.n
  constructor <;> linarith [P.A_pos, P.B_pos]

/-- Linear lower bound for `R`: `R(x) ≥ (n - |m|) |x* + x| - η r`. -/
theorem Rmorse_ge (x : ℝ) : (P.n - |P.m|) * |P.xstar + x| - P.eta * P.r ≤ P.Rmorse x := by
  set w := P.xstar + x
  have h1 : |w| ≤ Real.sqrt (w ^ 2 + P.eta ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [P.eta_pos])
  have h2 : -(|P.m| * |w|) ≤ P.m * w := by rw [← abs_mul]; exact neg_abs_le _
  have h3 := mul_le_mul_of_nonneg_left h1 P.n_pos.le
  unfold Params.Rmorse
  nlinarith

theorem Rtilde_ge (x : ℝ) :
    (P.n - |P.m|) * |P.xstar + x| - P.eta * P.r - kappaR P ≤ Rtilde P x := by
  have := Rmorse_ge P x
  have := (abs_le.1 (Rtilde_close P x)).1
  linarith

theorem Rtilde_tendsto_atTop : Tendsto (Rtilde P) atTop atTop := by
  have hc : 0 < P.n - |P.m| := by linarith [abs_m_lt_n P]
  have hlin : Tendsto (fun x => (P.n - |P.m|) * x + ((P.n - |P.m|) * P.xstar
      - P.eta * P.r - kappaR P)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hc)
  refine tendsto_atTop_mono (fun x => ?_) hlin
  have := Rtilde_ge P x
  have := le_abs_self (P.xstar + x)
  have := mul_le_mul_of_nonneg_left this hc.le
  nlinarith

theorem Rtilde_tendsto_atBot : Tendsto (Rtilde P) atBot atTop := by
  have hc : 0 < P.n - |P.m| := by linarith [abs_m_lt_n P]
  have hlin : Tendsto (fun x => (P.n - |P.m|) * (-x) + (-(P.n - |P.m|) * P.xstar
      - P.eta * P.r - kappaR P)) atBot atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_neg_atBot_atTop.const_mul_atTop hc)
  refine tendsto_atTop_mono (fun x => ?_) hlin
  have := Rtilde_ge P x
  have := neg_abs_le (P.xstar + x)
  have := mul_le_mul_of_nonneg_left (show -(P.xstar + x) ≤ |P.xstar + x| by linarith) hc.le
  nlinarith

end Inner

end SymplecticPacking
