import Mathlib
import SymplecticPacking.Inner.Map

/-!
# Constants of the density family and the source disk

`sec:pll-data`: the constants of the density family (`def:pll-density`)
and of the common source disk (`def:pll-source-constants`), and their order
(`lem:pll-source-order`).

Conventions: `e = e_q = P.eq_`, `A = P.A`, `B = P.B`; the constants of `sec:pll-constants` are those of
`SymplecticPacking.Inner` (`Inner.a0`, `Inner.b0`, `Inner.j0`, `Inner.deltaPrime`, `Inner.yc`, …).
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Set
open scoped Real

variable (P : Params)

/-! ### Constants of the density family (`def:pll-density`) -/

/-- `a₀ = X̃'(0) = √(2/α₀)`. -/
abbrev a0 : ℝ := Inner.a0 P

/-- `b₀ = Ỹ'(0) = √(2/e)`. -/
abbrev b0 : ℝ := Inner.b0 P

/-- `j₀ = a₀ b₀`. -/
abbrev j0 : ℝ := Inner.j0 P

/-- `K₀ = π j₀`. -/
def K0 : ℝ := π * j0 P

/-- `κ = K₀/(1 + K₀)`. -/
def kappa : ℝ := K0 P / (1 + K0 P)

lemma a0_pos : 0 < a0 P := Inner.a0_pos P
lemma b0_pos : 0 < b0 P := Inner.b0_pos P
lemma j0_pos : 0 < j0 P := Inner.j0_pos P
lemma K0_pos : 0 < K0 P := mul_pos Real.pi_pos (j0_pos P)
lemma kappa_pos : 0 < kappa P := div_pos (K0_pos P) (by linarith [K0_pos P])

/-- The minimum of `K₀(1-s)² + s²` over `s ∈ ℝ` is `κ`. -/
lemma kappa_le (s : ℝ) : kappa P ≤ K0 P * (1 - s) ^ 2 + s ^ 2 := by
  have hK := K0_pos P
  rw [kappa, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (K0 P - (1 + K0 P) * s)]

/-! ### Constants of the common source disk (`def:pll-source-constants`) -/

/-- `E_c = h - 2e`. -/
def Ec : ℝ := P.h - 2 * P.eq_

lemma Ec_eq : Ec P = P.Ec := rfl

/-- `ΔP = (2e - δ')/max(A, B)`. -/
def DeltaP : ℝ := (2 * P.eq_ - Inner.deltaPrime P) / max P.A P.B

/-- `Δy = 1/2 - y_c`. -/
def Deltay : ℝ := 1 / 2 - Inner.yc P

/-- `Q_X(E) = (|m| E + n √(E(E + 2ηr)))/r²` bounds `|X(u)|` for `u² ≤ E`. -/
def QX (E : ℝ) : ℝ := (|P.m| * E + P.n * √(E * (E + 2 * P.eta * P.r))) / P.r ^ 2

/-- `Q̃_X(E) = Q_X(E) + 2ε_R` bounds `|X̃(u)|` for `u² ≤ E`. -/
def QXt (E : ℝ) : ℝ := QX P E + 2 * Inner.epsR P

/-- `D_x = a₀ √E_c + Q̃_X(E_c)`. -/
def Dx : ℝ := a0 P * √(Ec P) + QXt P (Ec P)

/-- `D_y = b₀ √E_c + y_c`. -/
def Dy : ℝ := b0 P * √(Ec P) + Inner.yc P

/-- `δ_s = min(1/4, (1 - √(p₊/(E_c - d₀)))/2, ΔP/(2D_x), Δy/(2D_y))`. -/
def delta_s : ℝ :=
  min (min (1 / 4) ((1 - √(P.pplus / (Ec P - P.d0))) / 2))
    (min (DeltaP P / (2 * Dx P)) (Deltay P / (2 * Dy P)))

/-- `p† = (p₊ + (1 - δ_s)²(E_c - d₀))/2`. -/
def pdag : ℝ := (P.pplus + (1 - delta_s P) ^ 2 * (Ec P - P.d0)) / 2

/-- `Ē = (p† + d₀)/κ`. -/
def Ebar : ℝ := (pdag P + P.d0) / kappa P

/-- `X̄ = max(a₀ √Ē, Q̃_X(Ē))`. -/
def Xbar : ℝ := max (a0 P * √(Ebar P)) (QXt P (Ebar P))

/-- `Ȳ = b₀ √Ē`. -/
def Ybar : ℝ := b0 P * √(Ebar P)

/-- `c_P = 2e - δ'`, the moment margin of the endpoint (`= 15e/8 - κ_R`). -/
def cP : ℝ := 2 * P.eq_ - Inner.deltaPrime P

/-! ### Elementary facts -/

lemma Ec_pos : 0 < Ec P := by
  have := P.eq_le_h; have := P.eq_pos; unfold Ec; linarith

lemma Ec_lt_h : Ec P < P.h := by have := P.eq_pos; unfold Ec; linarith

lemma Ec_sub_d0_pos : 0 < Ec P - P.d0 := by
  have := P.pplus_lt_Ec_sub_d0; have := P.pplus_pos; rw [Ec_eq]; linarith

lemma pplus_lt_Ec_sub_d0 : P.pplus < Ec P - P.d0 := P.pplus_lt_Ec_sub_d0

lemma cP_pos : 0 < cP P := by
  have := P.eq_pos; unfold cP; rw [Params.deltaPrime_eq]; linarith

lemma cP_lt_h : cP P < P.h := by
  have := P.eq_le_h; have := P.eq_pos; have := P.deltaPrime_pos; unfold cP; linarith

lemma max_AB_pos : 0 < max P.A P.B := lt_max_of_lt_left P.A_pos

lemma DeltaP_pos : 0 < DeltaP P := div_pos (cP_pos P) (max_AB_pos P)

lemma Deltay_pos : 0 < Deltay P := by
  have := (Inner.yc_bounds P).2; unfold Deltay; linarith

lemma yc_pos : 0 < Inner.yc P := by
  have h1 := (Inner.yc_bounds P).1; have := Inner.wV_le P; linarith

lemma QX_nonneg {E : ℝ} (hE : 0 ≤ E) : 0 ≤ QX P E := by
  have := P.n_pos; have := P.r_pos
  unfold QX; positivity

lemma QX_mono {E E' : ℝ} (hE : 0 ≤ E) (h : E ≤ E') : QX P E ≤ QX P E' := by
  have hn := P.n_pos; have hr := P.r_pos; have h2 := Inner.two_eta_r_pos P
  unfold QX
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : |P.m| * E ≤ |P.m| * E' := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h3 : √(E * (E + 2 * P.eta * P.r)) ≤ √(E' * (E' + 2 * P.eta * P.r)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

lemma QXt_nonneg {E : ℝ} (hE : 0 ≤ E) : 0 ≤ QXt P E := by
  have := QX_nonneg P hE; have := Inner.epsR_pos P; unfold QXt; linarith

lemma QXt_mono {E E' : ℝ} (hE : 0 ≤ E) (h : E ≤ E') : QXt P E ≤ QXt P E' := by
  have := QX_mono P hE h; unfold QXt; linarith

lemma Dx_pos : 0 < Dx P := by
  have := QXt_nonneg P (Ec_pos P).le
  have : 0 < a0 P * √(Ec P) := mul_pos (a0_pos P) (Real.sqrt_pos.2 (Ec_pos P))
  unfold Dx; linarith

lemma Dy_pos : 0 < Dy P := by
  have := yc_pos P
  have : 0 < b0 P * √(Ec P) := mul_pos (b0_pos P) (Real.sqrt_pos.2 (Ec_pos P))
  unfold Dy; linarith

lemma sqrt_ratio_lt_one : √(P.pplus / (Ec P - P.d0)) < 1 := by
  have h := Ec_sub_d0_pos P
  rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one h]
  exact pplus_lt_Ec_sub_d0 P

/-! ### Order of the constants (`lem:pll-source-order`) -/

/-- **`lem:pll-source-order`.** `0 < δ_s ≤ 1/4`. -/
theorem delta_s_pos : 0 < delta_s P ∧ delta_s P ≤ 1 / 4 := by
  have h2 := sqrt_ratio_lt_one P
  refine ⟨lt_min (lt_min (by norm_num) (by linarith))
    (lt_min (div_pos (DeltaP_pos P) (by linarith [Dx_pos P]))
      (div_pos (Deltay_pos P) (by linarith [Dy_pos P]))), ?_⟩
  exact (min_le_left _ _).trans (min_le_left _ _)

lemma delta_s_le_half_gap : delta_s P ≤ (1 - √(P.pplus / (Ec P - P.d0))) / 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

lemma delta_s_le_DeltaP : delta_s P ≤ DeltaP P / (2 * Dx P) :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma delta_s_le_Deltay : delta_s P ≤ Deltay P / (2 * Dy P) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- `δ_s D_x ≤ ΔP/2`. -/
lemma delta_s_mul_Dx : delta_s P * Dx P ≤ DeltaP P / 2 := by
  have h := delta_s_le_DeltaP P; have hD := Dx_pos P
  rw [le_div_iff₀ (by linarith)] at h; linarith

/-- `δ_s D_y ≤ Δy/2`. -/
lemma delta_s_mul_Dy : delta_s P * Dy P ≤ Deltay P / 2 := by
  have h := delta_s_le_Deltay P; have hD := Dy_pos P
  rw [le_div_iff₀ (by linarith)] at h; linarith

/-- `p₊ < (1 - δ_s)²(E_c - d₀)`. -/
lemma pplus_lt_late : P.pplus < (1 - delta_s P) ^ 2 * (Ec P - P.d0) := by
  have hE := Ec_sub_d0_pos P
  have hq := sqrt_ratio_lt_one P
  set q := √(P.pplus / (Ec P - P.d0))
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q ^ 2 = P.pplus / (Ec P - P.d0) := Real.sq_sqrt (div_nonneg P.pplus_pos.le hE.le)
  have h1 : q < 1 - delta_s P := by have := delta_s_le_half_gap P; linarith
  have h2 : q ^ 2 < (1 - delta_s P) ^ 2 := pow_lt_pow_left₀ h1 hq0 (by norm_num)
  rw [hqsq, div_lt_iff₀ hE] at h2
  linarith

/-- `(1 - δ_s)²(E_c - d₀) < h`. -/
lemma late_lt_h : (1 - delta_s P) ^ 2 * (Ec P - P.d0) < P.h := by
  have hδ := delta_s_pos P
  have hE := Ec_sub_d0_pos P
  have h1 : (1 - delta_s P) ^ 2 < 1 := by nlinarith
  have := P.d0_nonneg
  have := Ec_lt_h P
  nlinarith

/-- **`lem:pll-source-order`.** `p₊ < p† < (1 - δ_s)²(E_c - d₀) < h`. -/
theorem pdag_bounds : P.pplus < pdag P ∧ pdag P < (1 - delta_s P) ^ 2 * (Ec P - P.d0) ∧
    (1 - delta_s P) ^ 2 * (Ec P - P.d0) < P.h := by
  have := pplus_lt_late P
  exact ⟨by unfold pdag; linarith, by unfold pdag; linarith, late_lt_h P⟩

lemma pdag_pos' : 0 < pdag P := P.pplus_pos.trans (pdag_bounds P).1

lemma pdag_lt_h : pdag P < P.h := (pdag_bounds P).2.1.trans (pdag_bounds P).2.2

lemma Ebar_pos : 0 < Ebar P :=
  div_pos (by linarith [pdag_pos' P, P.d0_nonneg]) (kappa_pos P)

lemma Xbar_pos : 0 < Xbar P :=
  lt_max_of_lt_left (mul_pos (a0_pos P) (Real.sqrt_pos.2 (Ebar_pos P)))

lemma Ybar_pos : 0 < Ybar P := mul_pos (b0_pos P) (Real.sqrt_pos.2 (Ebar_pos P))

end SymplecticPacking.Qhat
