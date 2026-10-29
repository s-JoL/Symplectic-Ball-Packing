import Mathlib
import SymplecticPacking.Qhat.DensitySmooth

/-!
# A priori bounds for the density family

`sec:pll-data`, `lem:pll-bounds` (a priori bounds): for `z ∈ D̄(p†)`,
`s ∈ [0, 1]`, with `(u, v) = T_s⁻¹ D_s z`:
(a) `E_s(π|z|²) ≤ Ē`, `|X_s(u)| ≤ X̄`, `|Y_s(v)| ≤ Ȳ`;
(b) for `s ≥ 1 - δ_s`: `E_s < E_c`, `ΔP/2 ≤ p* + X_s(u) ≤ h - ΔP/2`, `|Y_s(v)| ≤ 1/2 - Δy/2`;
(c) for `s = 1`: `(2e - δ')/A ≤ p* + X̃(u) ≤ h - (2e - δ')/B`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-- The Morse coordinates `(u, v) = T_s⁻¹ D_s z` of `z`. -/
def uv (s : ℝ) (z : ℂ) : ℂ := Inner.TrotInv (Js P) s (Inner.Darea (Js P) s z)

lemma fs_re_uv (s : ℝ) (z : ℂ) : (fs P s z).re = Xs P s (uv P s z).re := fs_re P s z

lemma fs_im_uv (s : ℝ) (z : ℂ) : (fs P s z).im = Ys P s (uv P s z).im := fs_im P s z

/-- `u² + v² = E_s(π|z|²)`. -/
lemma uv_normSq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : ℂ) :
    ‖uv P s z‖ ^ 2 = Es P s (π * ‖z‖ ^ 2) := fs_level P hs z

lemma re_sq_le_normSq (w : ℂ) : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [mul_self_nonneg w.im]

lemma im_sq_le_normSq (w : ℂ) : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [mul_self_nonneg w.re]

lemma abs_le_sqrt_of_sq_le {x E : ℝ} (h : x ^ 2 ≤ E) : |x| ≤ √E := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h

/-! ### Growth of `X` and `X̃` -/

/-- `|X(u)| ≤ Q_X(u²)`. -/
theorem abs_Xinv_le (u : ℝ) : |Inner.Xinv P u| ≤ QX P (u ^ 2) := by
  have hr := P.r_pos; have hn := P.n_pos
  have h2 := Inner.two_eta_r_pos P
  have hs : |u| * √(u ^ 2 + 2 * P.eta * P.r) = √(u ^ 2 * (u ^ 2 + 2 * P.eta * P.r)) := by
    rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq_eq_abs]
  unfold Inner.Xinv QX
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < P.r ^ 2), ← hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq := Real.sqrt_nonneg (u ^ 2 + 2 * P.eta * P.r)
  calc |-P.m * u ^ 2 + P.n * u * √(u ^ 2 + 2 * P.eta * P.r)|
      ≤ |-P.m * u ^ 2| + |P.n * u * √(u ^ 2 + 2 * P.eta * P.r)| := abs_add_le _ _
    _ = |P.m| * u ^ 2 + P.n * (|u| * √(u ^ 2 + 2 * P.eta * P.r)) := by
        rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg u), abs_mul, abs_mul,
          abs_of_pos hn, abs_of_nonneg hsq]; ring

/-- `|X̃(u)| ≤ Q̃_X(u²)`. -/
theorem abs_Xtilde_le_QXt (u : ℝ) : |Inner.Xtilde P u| ≤ QXt P (u ^ 2) := by
  have h := Inner.Xtilde_abs_le P u
  have := abs_Xinv_le P u
  unfold QXt; linarith [h.1, h.2]

/-- `|Ỹ(v)| ≤ b₀ |v|`. -/
theorem abs_Ytilde_le_b0 (v : ℝ) : |Inner.Ytilde P v| ≤ b0 P * |v| := Inner.abs_Ytilde_le P v

/-- `|X_s(u)| ≤ max(a₀ √E, Q̃_X(E))` for `u² ≤ E`, `s ∈ [0, 1]`. -/
theorem abs_Xs_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {u E : ℝ} (hu : u ^ 2 ≤ E) :
    |Xs P s u| ≤ max (a0 P * √E) (QXt P E) := by
  have hE : 0 ≤ E := (sq_nonneg u).trans hu
  have h1 : |u| ≤ √E := abs_le_sqrt_of_sq_le hu
  have h2 : |Inner.Xtilde P u| ≤ QXt P E :=
    (abs_Xtilde_le_QXt P u).trans (QXt_mono P (sq_nonneg u) hu)
  have ha := a0_pos P
  set M := max (a0 P * √E) (QXt P E)
  have hM1 : a0 P * |u| ≤ M := (mul_le_mul_of_nonneg_left h1 ha.le).trans (le_max_left _ _)
  have hM2 : |Inner.Xtilde P u| ≤ M := h2.trans (le_max_right _ _)
  unfold Xs
  calc |(1 - s) * a0 P * u + s * Inner.Xtilde P u|
      ≤ |(1 - s) * a0 P * u| + |s * Inner.Xtilde P u| := abs_add_le _ _
    _ = (1 - s) * (a0 P * |u|) + s * |Inner.Xtilde P u| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_pos ha, abs_of_nonneg hs.1]; ring
    _ ≤ (1 - s) * M + s * M := by
        gcongr
        · linarith [hs.2]
        · exact hs.1
    _ = M := by ring

/-- `|Y_s(v)| ≤ b₀ |v|`, `s ∈ [0, 1]`. -/
theorem abs_Ys_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (v : ℝ) : |Ys P s v| ≤ b0 P * |v| := by
  have hb := b0_pos P
  have h2 := abs_Ytilde_le_b0 P v
  unfold Ys
  calc |(1 - s) * b0 P * v + s * Inner.Ytilde P v|
      ≤ |(1 - s) * b0 P * v| + |s * Inner.Ytilde P v| := abs_add_le _ _
    _ = (1 - s) * (b0 P * |v|) + s * |Inner.Ytilde P v| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_pos hb, abs_of_nonneg hs.1]; ring
    _ ≤ (1 - s) * (b0 P * |v|) + s * (b0 P * |v|) := by gcongr; exact hs.1
    _ = b0 P * |v| := by ring

/-! ### (a) The crude bounds -/

/-- **`lem:pll-bounds` (a).** `E_s(π|z|²) ≤ Ē` on `D̄(p†)`. -/
theorem Es_le_Ebar {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    Es P s (π * ‖z‖ ^ 2) ≤ Ebar P :=
  (Es_le P hs (by positivity)).trans
    (div_le_div_of_nonneg_right (by linarith) (kappa_pos P).le)

/-- **`lem:pll-bounds` (a).** `|X_s(u)| ≤ X̄` on `D̄(p†)`. -/
theorem Xs_le_Xbar {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    |(fs P s z).re| ≤ Xbar P := by
  rw [fs_re_uv]
  refine abs_Xs_le P hs ?_
  exact (re_sq_le_normSq _).trans ((uv_normSq P hs z).le.trans (Es_le_Ebar P hs hz))

/-- **`lem:pll-bounds` (a).** `|Y_s(v)| ≤ Ȳ` on `D̄(p†)`. -/
theorem Ys_le_Ybar {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    |(fs P s z).im| ≤ Ybar P := by
  rw [fs_im_uv]
  refine (abs_Ys_le P hs _).trans (mul_le_mul_of_nonneg_left ?_ (b0_pos P).le)
  exact abs_le_sqrt_of_sq_le
    ((im_sq_le_normSq _).trans ((uv_normSq P hs z).le.trans (Es_le_Ebar P hs hz)))

/-! ### (b), (c) The late margins -/

lemma h_div_A : P.h / P.A = P.a := by
  have := P.h_pos.ne'; have := P.a_pos.ne'; unfold Params.A; field_simp

lemma h_div_B : P.h / P.B = P.h - P.a := by
  have := P.h_pos.ne'; have : P.h - P.a ≠ 0 := by linarith [P.a_lt_h]
  unfold Params.B; field_simp

/-- **`lem:pll-bounds` (c), at the level of the Morse coordinate.** If `u² < E_c` then
`c_P/A ≤ p* + X̃(u) ≤ h - c_P/B`, `c_P = 2e - δ'`. -/
theorem endpoint_margin {u : ℝ} (hu : u ^ 2 < Ec P) :
    cP P / P.A ≤ P.pstar + Inner.Xtilde P u ∧ P.pstar + Inner.Xtilde P u ≤ P.h - cP P / P.B := by
  set x := P.pstar + Inner.Xtilde P u
  have hc := (abs_le.mp (Inner.Rtilde_Rcal_close P x)).1
  rw [show x - P.pstar = Inner.Xtilde P u by simp [x], Inner.Rtilde_Xtilde] at hc
  have hR : P.Rcal x ≤ P.h - cP P := by unfold cP Ec at *; linarith
  have hb : 0 ≤ P.h - cP P := by linarith [cP_lt_h P]
  have hmem := (P.Rcal_le_iff hb x).mp hR
  have e1 : P.a - (P.h - cP P) / P.A = cP P / P.A := by
    rw [sub_div, h_div_A]; ring
  have e2 : P.a + (P.h - cP P) / P.B = P.h - cP P / P.B := by
    rw [sub_div, h_div_B]; ring
  rw [e1, e2] at hmem
  exact hmem

lemma cP_div_A_ge : DeltaP P ≤ cP P / P.A :=
  div_le_div_of_nonneg_left (cP_pos P).le P.A_pos (le_max_left _ _)

lemma cP_div_B_ge : DeltaP P ≤ cP P / P.B :=
  div_le_div_of_nonneg_left (cP_pos P).le P.B_pos (le_max_right _ _)

/-- In the late range the whole source disk lies below the level `E_c`. -/
theorem Es_lt_Ec {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hlate : 1 - delta_s P ≤ s) {z : ℂ}
    (hz : π * ‖z‖ ^ 2 ≤ pdag P) : Es P s (π * ‖z‖ ^ 2) < Ec P := by
  have hJ := JsC_flat P hs
  have hδ := delta_s_pos P
  have hEc := Ec_pos P
  have hEd := Ec_sub_d0_pos P
  have h1 := (As_ge P hs hEc.le).1
  have hK := K0_pos P
  have hs2 : (1 - delta_s P) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith) hlate 2
  have h2 : (1 - delta_s P) ^ 2 * (Ec P - P.d0) ≤ As P s (Ec P) := by
    have : 0 ≤ K0 P * (1 - s) ^ 2 * Ec P := by positivity
    nlinarith
  have h3 := (pdag_bounds P).2.1
  have h4 : π * ‖z‖ ^ 2 < As P s (Ec P) := by linarith
  rw [← Inner.Acal_Einv hJ zero_mem_Ioo (π * ‖z‖ ^ 2)] at h4
  exact (Inner.Acal_strictMono hJ zero_mem_Ioo).lt_iff_lt.mp h4

/-- **`lem:pll-bounds` (b), (6).** For `s ∈ [1 - δ_s, 1]` and `z ∈ D̄(p†)`:
`E_s < E_c`, `ΔP/2 ≤ p* + X_s(u) ≤ h - ΔP/2` and `|Y_s(v)| ≤ 1/2 - Δy/2`. -/
theorem late_margin {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hlate : 1 - delta_s P ≤ s) {z : ℂ}
    (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    Es P s (π * ‖z‖ ^ 2) < Ec P ∧
      DeltaP P / 2 ≤ P.pstar + (fs P s z).re ∧ P.pstar + (fs P s z).re ≤ P.h - DeltaP P / 2 ∧
      |(fs P s z).im| ≤ 1 / 2 - Deltay P / 2 := by
  have hE := Es_lt_Ec P hs hlate hz
  refine ⟨hE, ?_⟩
  set w := uv P s z
  have hw : ‖w‖ ^ 2 < Ec P := by rw [uv_normSq P hs z]; exact hE
  have hu : w.re ^ 2 < Ec P := (re_sq_le_normSq w).trans_lt hw
  have hv : w.im ^ 2 < Ec P := (im_sq_le_normSq w).trans_lt hw
  set u := w.re
  set v := w.im
  have hu' : |u| ≤ √(Ec P) := abs_le_sqrt_of_sq_le hu.le
  have hv' : |v| ≤ √(Ec P) := abs_le_sqrt_of_sq_le hv.le
  have h1ms : 0 ≤ 1 - s := by linarith [hs.2]
  have h1ms' : 1 - s ≤ delta_s P := by linarith
  -- the x-side
  obtain ⟨hX1, hX2⟩ := endpoint_margin P hu
  have hXt : |Inner.Xtilde P u| ≤ QXt P (Ec P) :=
    (abs_Xtilde_le_QXt P u).trans (QXt_mono P (sq_nonneg u) hu.le)
  have hdx : |Xs P s u - Inner.Xtilde P u| ≤ DeltaP P / 2 := by
    have heq : Xs P s u - Inner.Xtilde P u = (1 - s) * (a0 P * u - Inner.Xtilde P u) := by
      unfold Xs; ring
    rw [heq, abs_mul, abs_of_nonneg h1ms]
    have hb : |a0 P * u - Inner.Xtilde P u| ≤ Dx P := by
      unfold Dx
      calc |a0 P * u - Inner.Xtilde P u| ≤ |a0 P * u| + |Inner.Xtilde P u| := abs_sub _ _
        _ ≤ a0 P * √(Ec P) + QXt P (Ec P) := by
            rw [abs_mul, abs_of_pos (a0_pos P)]
            exact add_le_add (mul_le_mul_of_nonneg_left hu' (a0_pos P).le) hXt
    calc (1 - s) * |a0 P * u - Inner.Xtilde P u| ≤ delta_s P * Dx P :=
          mul_le_mul h1ms' hb (abs_nonneg _) (delta_s_pos P).1.le
      _ ≤ DeltaP P / 2 := delta_s_mul_Dx P
  have hA := cP_div_A_ge P
  have hB := cP_div_B_ge P
  have hdx' := abs_le.mp hdx
  -- the y-side
  have hYt : |Inner.Ytilde P v| < Inner.yc P := by
    have : Inner.Vtilde P (Inner.Ytilde P v) ≤ P.h - 2 * P.eq_ := by
      rw [Inner.Vtilde_Ytilde]; unfold Ec at hv; linarith
    exact (Inner.Vtilde_le_lt_yc P this).2
  have hdy : |Ys P s v - Inner.Ytilde P v| ≤ Deltay P / 2 := by
    have heq : Ys P s v - Inner.Ytilde P v = (1 - s) * (b0 P * v - Inner.Ytilde P v) := by
      unfold Ys; ring
    rw [heq, abs_mul, abs_of_nonneg h1ms]
    have hb : |b0 P * v - Inner.Ytilde P v| ≤ Dy P := by
      unfold Dy
      calc |b0 P * v - Inner.Ytilde P v| ≤ |b0 P * v| + |Inner.Ytilde P v| := abs_sub _ _
        _ ≤ b0 P * √(Ec P) + Inner.yc P := by
            rw [abs_mul, abs_of_pos (b0_pos P)]
            exact add_le_add (mul_le_mul_of_nonneg_left hv' (b0_pos P).le) hYt.le
    calc (1 - s) * |b0 P * v - Inner.Ytilde P v| ≤ delta_s P * Dy P :=
          mul_le_mul h1ms' hb (abs_nonneg _) (delta_s_pos P).1.le
      _ ≤ Deltay P / 2 := delta_s_mul_Dy P
  rw [fs_re_uv, fs_im_uv]
  refine ⟨by linarith [hdx'.1], by linarith [hdx'.2], ?_⟩
  have := abs_sub_abs_le_abs_sub (Ys P s v) (Inner.Ytilde P v)
  unfold Deltay at *
  linarith

/-- **`lem:pll-bounds` (c).** For `s = 1` (`f₁ = f`) and `z ∈ D̄(p†)`:
`(2e - δ')/A ≤ p* + Re f(z) ≤ h - (2e - δ')/B`. -/
theorem late_margin_one {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    cP P / P.A ≤ P.pstar + (Inner.finner P z).re ∧
      P.pstar + (Inner.finner P z).re ≤ P.h - cP P / P.B := by
  have hs : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hE := Es_lt_Ec P hs (by linarith [(delta_s_pos P).1]) hz
  set w := uv P 1 z
  have hw : ‖w‖ ^ 2 < Ec P := by rw [uv_normSq P hs z]; exact hE
  have hu : w.re ^ 2 < Ec P := (re_sq_le_normSq w).trans_lt hw
  have hre : (Inner.finner P z).re = Inner.Xtilde P w.re := by
    rw [← fs_eq_finner, fs_re_uv]; simp [Xs, w]
  rw [hre]
  exact endpoint_margin P hu

end SymplecticPacking.Qhat
