import Mathlib
import SymplecticPacking.Qhat.InnerFamily

/-!
# The five-segment ordinary path

`sec:pln-five`: the constants of the ordinary path
(`def:pll-path-constants`, `lem:pln-data`),
the five segments and the path `𝔢_t` (`cons:pln-five-segment`) and its properties (`lem:pln-five-segment`).

`ordPath` is written as one closed (telescoped) formula in the five flat clocks
`σ_j(t) = S(5t - j)`; `ordPath_eq_seg` shows it is the paper's piecewise definition
`𝔢_t = 𝔢^j_{S(5t-j)}` on `[j/5, (j+1)/5]`, `id` for `t ≤ 0` and `𝔢_1` for `t ≥ 1`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Filter Topology Set Complex
open scoped ContDiff Real

variable (P : Params)

/-! ### Constants (`def:pll-path-constants`) -/

/-- `M_C = 1/(2√(π P_min)) + 2√(π P_max)` bounds `‖DC‖` on `[P_min, P_max]`. -/
def MC : ℝ := 1 / (2 * √(π * Pmin P)) + 2 * √(π * Pmax P)

/-- `B* = min(M_C √(X̄² + Ȳ²), X̄/√(πp*) + 2π √(p*/π) Ȳ)` bounds `|q^in_s - b|`. -/
def Bstar : ℝ :=
  min (MC P * √(Xbar P ^ 2 + Ybar P ^ 2)) (Xbar P / √(π * P.pstar) + 2 * π * √(P.pstar / π) * Ybar P)

/-- `R† = √(p†/π)`. -/
def Rdag : ℝ := √(pdag P / π)

/-- `R_h = √(h/π)`. -/
def Rh : ℝ := √(P.h / π)

/-- `𝐌_σ = Rot_{πσ} diag(|A₁₁|^σ, |A₂₂|^σ)`. -/
def Msig (σ : ℝ) (z : ℂ) : ℂ :=
  Inner.Rot (π * σ) (((|A11 P| ^ σ * z.re : ℝ) : ℂ) + ((|A22 P| ^ σ * z.im : ℝ) : ℂ) * I)

/-- `B₃ = R† max(1, |A₁₁|, |A₂₂|)`. -/
def B3 : ℝ := Rdag P * max 1 (max |A11 P| |A22 P|)

/-- `c_new = min(1/4, (R_h - r_b)/(8 max(R†, B₃, B*)))`. -/
def cnew : ℝ := min (1 / 4) ((Rh P - rb P) / (8 * max (Rdag P) (max (B3 P) (Bstar P))))

/-- `R_q = √((h - (2e - δ')/B)/π)`. -/
def Rq : ℝ := √((P.h - cP P / P.B) / π)

/-- `R_supp = max(R†, r_b + c B₃, r_b + c B*, R_q)`. -/
def Rsupp : ℝ :=
  max (max (Rdag P) (rb P + cnew P * B3 P)) (max (rb P + cnew P * Bstar P) (Rq P))

/-- `P_supp = π R_supp²`. -/
def Psupp : ℝ := π * Rsupp P ^ 2

/-! ### Elementary facts -/

lemma Rdag_pos : 0 < Rdag P := Real.sqrt_pos.2 (div_pos (pdag_pos' P) Real.pi_pos)

lemma rb_lt_Rh : rb P < Rh P :=
  Real.sqrt_lt_sqrt (div_nonneg (pstar_pos P).le Real.pi_pos.le)
    (div_lt_div_of_pos_right P.pstar_mem.2 Real.pi_pos)

lemma Rdag_lt_Rh : Rdag P < Rh P :=
  Real.sqrt_lt_sqrt (div_nonneg (pdag_pos' P).le Real.pi_pos.le)
    (div_lt_div_of_pos_right (pdag_lt_h P) Real.pi_pos)

lemma norm_lt_Rdag {z : ℂ} (hz : z ∈ srcDisk P) : ‖z‖ < Rdag P := by
  have hpi := Real.pi_pos
  rw [Rdag, ← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [lt_div_iff₀ hpi]; have : π * ‖z‖ ^ 2 < pdag P := hz; linarith)

lemma max3_pos : 0 < max (Rdag P) (max (B3 P) (Bstar P)) := lt_max_of_lt_left (Rdag_pos P)

/-- **`lem:pln-data` (c).** `0 < c ≤ 1/4`. -/
theorem cnew_pos : 0 < cnew P ∧ cnew P ≤ 1 / 4 :=
  ⟨lt_min (by norm_num) (div_pos (by linarith [rb_lt_Rh P]) (by linarith [max3_pos P])),
    min_le_left _ _⟩

lemma cnew_mul_le {B : ℝ} (hB : B ≤ max (Rdag P) (max (B3 P) (Bstar P))) :
    cnew P * B ≤ (Rh P - rb P) / 8 := by
  have hc := cnew_pos P
  have hm := max3_pos P
  have h1 : cnew P ≤ (Rh P - rb P) / (8 * max (Rdag P) (max (B3 P) (Bstar P))) := min_le_right _ _
  rw [le_div_iff₀ (by linarith)] at h1
  have : cnew P * B ≤ cnew P * max (Rdag P) (max (B3 P) (Bstar P)) :=
    mul_le_mul_of_nonneg_left hB hc.1.le
  linarith

lemma Rq_lt_Rh : Rq P < Rh P := by
  have hB : 0 < cP P / P.B := div_pos (cP_pos P) P.B_pos
  have hB1 : 1 ≤ P.B := by
    unfold Params.B; rw [le_div_iff₀ (by linarith [P.a_lt_h])]; linarith [P.a_pos]
  have h1 : cP P / P.B ≤ cP P := div_le_self (cP_pos P).le hB1
  have h2 := cP_lt_h P
  exact Real.sqrt_lt_sqrt (div_nonneg (by linarith) Real.pi_pos.le)
    (div_lt_div_of_pos_right (by linarith) Real.pi_pos)

/-- **`lem:pln-data` (c).** `R_supp < R_h`. -/
theorem Rsupp_lt : Rsupp P < Rh P := by
  have h1 := Rdag_lt_Rh P
  have h2 := cnew_mul_le P (B := B3 P) ((le_max_left _ _).trans (le_max_right _ _))
  have h3 := cnew_mul_le P (B := Bstar P) ((le_max_right _ _).trans (le_max_right _ _))
  have h4 := Rq_lt_Rh P
  have h5 := rb_lt_Rh P
  exact max_lt (max_lt h1 (by linarith)) (max_lt (by linarith) h4)

lemma Rsupp_nonneg : 0 ≤ Rsupp P :=
  (Rdag_pos P).le.trans ((le_max_left _ _).trans (le_max_left _ _))

/-- **`lem:pln-data` (c).** `P_supp < h`. -/
theorem Psupp_lt : Psupp P < P.h := by
  have h := Rsupp_lt P
  have h0 := Rsupp_nonneg P
  have hpi := Real.pi_pos
  have hRh : Rh P ^ 2 = P.h / π := Real.sq_sqrt (div_nonneg P.h_pos.le hpi.le)
  have : Rsupp P ^ 2 < Rh P ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  rw [hRh, lt_div_iff₀ hpi] at this
  unfold Psupp; linarith

/-! ### (a) The bound `|q^in_s - b| ≤ B*` -/

lemma norm_Hy_le (lam : ℝ) (w : ℂ) : ‖Hy P lam w‖ ≤ 2 * π * rb P := by
  have := rb_pos P; have := Real.pi_pos
  unfold Hy
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have := norm_gexp_le (2 * π * lam * w.im)
  have h2 : 0 < 2 * π * rb P := by positivity
  calc 2 * π * rb P * ‖gexp (((2 * π * lam * w.im : ℝ) : ℂ) * I)‖ ≤ 2 * π * rb P * 1 :=
        mul_le_mul_of_nonneg_left this h2.le
    _ = 2 * π * rb P := mul_one _

lemma norm_Hx_eq (lam : ℝ) (w : ℂ) :
    ‖Hx P lam w‖ = (π * (rb P + √((P.pstar + lam * w.re) / π)))⁻¹ := by
  have := rb_pos P; have := Real.pi_pos
  unfold Hx
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by have := Real.sqrt_nonneg ((P.pstar + lam * w.re) / π); positivity)]

lemma Clam_sub_b (lam : ℝ) (w : ℂ) :
    Clam P lam w - bpt P = -((w.im : ℂ) * Hy P lam w) - (w.re : ℂ) * Hx P lam w := by
  unfold Clam; ring

/-- `|C_λ(w) - b| ≤ |u|/(π(r_b + ρ)) + 2π r_b |v|`. -/
lemma Clam_sub_b_le (lam : ℝ) (w : ℂ) :
    ‖Clam P lam w - bpt P‖ ≤
      (π * (rb P + √((P.pstar + lam * w.re) / π)))⁻¹ * |w.re| + 2 * π * rb P * |w.im| := by
  rw [Clam_sub_b]
  calc ‖-((w.im : ℂ) * Hy P lam w) - (w.re : ℂ) * Hx P lam w‖
      ≤ ‖(w.im : ℂ) * Hy P lam w‖ + ‖(w.re : ℂ) * Hx P lam w‖ := by
        rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]; exact norm_add_le _ _
    _ = |w.im| * ‖Hy P lam w‖ + |w.re| * ‖Hx P lam w‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ |w.im| * (2 * π * rb P) + |w.re| * (π * (rb P + √((P.pstar + lam * w.re) / π)))⁻¹ := by
        rw [norm_Hx_eq]
        gcongr
        exact norm_Hy_le P lam w
    _ = _ := by ring

lemma pi_mul_sqrt (x : ℝ) (hx : 0 ≤ x) : π * √(x / π) = √(π * x) := by
  have hpi := Real.pi_pos
  rw [← Real.sqrt_sq (by positivity : 0 ≤ π * √(x / π)), mul_pow,
    Real.sq_sqrt (div_nonneg hx hpi.le)]
  congr 1; field_simp

/-- **`lem:pln-data` (a).** `|q^in_s(z) - b| ≤ B*` for `s ∈ [0, 1]`,
`z ∈ D̄(p†)`. -/
theorem qinner_sub_b_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) :
    ‖qinner P s z - bpt P‖ ≤ Bstar P := by
  set w := fs P s z
  set lam' := lam P s
  have hX : |w.re| ≤ Xbar P := Xs_le_Xbar P hs hz
  have hY : |w.im| ≤ Ybar P := Ys_le_Ybar P hs hz
  have hrad := (qinner_radial P hs hz (t := 1) ⟨zero_le_one, le_rfl⟩)
  simp only [one_mul] at hrad
  set Prad := P.pstar + lam' * w.re
  have hpi := Real.pi_pos
  have hrb := rb_pos P
  have hp := pstar_pos P
  have hPmin := Pmin_pos P
  have hPP : Pmin P ≤ Prad := hrad.1
  set ρ := √(Prad / π)
  have hbase := Clam_sub_b_le P lam' w
  have hden_eq : π * (rb P + ρ) = √(π * P.pstar) + √(π * Prad) := by
    rw [mul_add, pi_mul_rb, pi_mul_sqrt _ (by linarith)]
  have hsqp : 0 < √(π * P.pstar) := Real.sqrt_pos.2 (by positivity)
  refine le_min ?_ ?_
  · -- first bound
    have hPmin_p : Pmin P ≤ P.pstar := by
      have := min_le_left P.pstar (DeltaP P); unfold Pmin; linarith
    have hm : 0 < √(π * Pmin P) := Real.sqrt_pos.2 (by positivity)
    have hd1 : √(π * Pmin P) ≤ √(π * P.pstar) := Real.sqrt_le_sqrt (by nlinarith)
    have hd2 : √(π * Pmin P) ≤ √(π * Prad) := Real.sqrt_le_sqrt (by nlinarith)
    have hinv : (π * (rb P + ρ))⁻¹ ≤ 1 / (2 * √(π * Pmin P)) := by
      rw [hden_eq, one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    have hPmax : 2 * π * rb P ≤ 2 * √(π * Pmax P) := by
      rw [mul_assoc, pi_mul_rb]
      have : P.pstar ≤ Pmax P := (by linarith : P.pstar ≤ 3 * P.pstar / 2).trans (le_max_left _ _)
      have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left this hpi.le)
      linarith
    have hw1 : |w.re| ≤ ‖w‖ := abs_re_le_norm w
    have hw2 : |w.im| ≤ ‖w‖ := abs_im_le_norm w
    have hnorm : ‖w‖ ≤ √(Xbar P ^ 2 + Ybar P ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      apply Real.sqrt_le_sqrt
      have h1 : w.re * w.re ≤ Xbar P ^ 2 := by rw [← sq, ← sq_abs]; gcongr
      have h2 : w.im * w.im ≤ Ybar P ^ 2 := by rw [← sq, ← sq_abs]; gcongr
      linarith
    have hMC : 0 ≤ MC P := by unfold MC; positivity
    calc ‖qinner P s z - bpt P‖ ≤ (π * (rb P + ρ))⁻¹ * |w.re| + 2 * π * rb P * |w.im| := hbase
      _ ≤ 1 / (2 * √(π * Pmin P)) * ‖w‖ + 2 * √(π * Pmax P) * ‖w‖ := by
          gcongr
      _ = MC P * ‖w‖ := by unfold MC; ring
      _ ≤ MC P * √(Xbar P ^ 2 + Ybar P ^ 2) := mul_le_mul_of_nonneg_left hnorm hMC
  · -- second bound
    have hinv : (π * (rb P + ρ))⁻¹ ≤ 1 / √(π * P.pstar) := by
      rw [hden_eq, one_div]
      exact inv_anti₀ hsqp (by linarith [Real.sqrt_nonneg (π * Prad)])
    have hrbdef : rb P = √(P.pstar / π) := rfl
    calc ‖qinner P s z - bpt P‖ ≤ (π * (rb P + ρ))⁻¹ * |w.re| + 2 * π * rb P * |w.im| := hbase
      _ ≤ 1 / √(π * P.pstar) * Xbar P + 2 * π * rb P * Ybar P := by
          gcongr
      _ = _ := by rw [hrbdef]; ring

/-- **`lem:pln-data` (d).** `|q^in_1(z)| ≤ R_q` for `z ∈ D̄(p†)`. -/
theorem qinner_one_norm_le {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ pdag P) : ‖qinner P 1 z‖ ≤ Rq P := by
  rw [qinner_one P hz]
  obtain ⟨h1, h2⟩ := late_margin_one P hz
  have hA : 0 ≤ cP P / P.A := div_nonneg (cP_pos P).le P.A_pos.le
  have hm := Inner.chartC_moment P (w := Inner.finner P z) (by linarith)
  have hpi := Real.pi_pos
  rw [Rq, ← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hpi]; linarith

/-! ### (b) The linear segment -/

lemma abs_A11_pos : 0 < |A11 P| := abs_pos.mpr (A11_neg P).ne
lemma abs_A22_pos : 0 < |A22 P| := abs_pos.mpr (A22_neg P).ne

lemma abs_A11_mul_A22 : |A11 P| * |A22 P| = 1 := by rw [← abs_mul, A11_mul_A22, abs_one]

lemma Msig_re_im (σ : ℝ) (z : ℂ) :
    Msig P σ z = Complex.exp (((π * σ : ℝ) : ℂ) * I) *
      (((|A11 P| ^ σ * z.re : ℝ) : ℂ) + ((|A22 P| ^ σ * z.im : ℝ) : ℂ) * I) := rfl

/-- `𝐌_σ` as a continuous linear map. -/
def MsigL (σ : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.exp (((π * σ : ℝ) : ℂ) * I) •
    (ofRealCLM.comp ((|A11 P| ^ σ) • reCLM) + (ofRealCLM.comp ((|A22 P| ^ σ) • imCLM)).smulRight I)

lemma MsigL_apply (σ : ℝ) (z : ℂ) : MsigL P σ z = Msig P σ z := by
  simp [MsigL, Msig_re_im]; ring

lemma Msig_eq : Msig P = fun σ => ⇑(MsigL P σ) := funext fun σ => funext fun z =>
  (MsigL_apply P σ z).symm

/-- **`lem:pln-data` (b).** `det 𝐌_σ = 1`. -/
theorem Msig_det (σ : ℝ) : LinearMap.det (MsigL P σ : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [Inner.det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe, MsigL_apply, Msig_re_im]
  set c := Real.cos (π * σ)
  set sn := Real.sin (π * σ)
  have he : Complex.exp (((π * σ : ℝ) : ℂ) * I) = (c : ℂ) + (sn : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [he]
  simp
  have h1 : (|A11 P| ^ σ) * (|A22 P| ^ σ) = 1 := by
    rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_A11_mul_A22, Real.one_rpow]
  have h2 := Real.cos_sq_add_sin_sq (π * σ)
  linear_combination (c ^ 2 + sn ^ 2) * h1 + h2

lemma Msig_zero (z : ℂ) : Msig P 0 z = z := by
  rw [Msig_re_im]; simp

lemma Msig_one (z : ℂ) : Msig P 1 z = A0 P z := by
  rw [Msig_re_im, A0_apply, abs_of_neg (A11_neg P), abs_of_neg (A22_neg P)]
  simp only [Real.rpow_one, mul_one]
  rw [show ((π : ℝ) : ℂ) * I = (π : ℂ) * I from rfl, Complex.exp_pi_mul_I]
  push_cast; ring

lemma rpow_le_max {d σ : ℝ} (hd : 0 < d) (hσ : σ ∈ Icc (0 : ℝ) 1) : d ^ σ ≤ max 1 d := by
  rcases le_or_gt 1 d with h | h
  · exact (by simpa using Real.rpow_le_rpow_of_exponent_le h hσ.2 : d ^ σ ≤ d).trans
      (le_max_right _ _)
  · exact (Real.rpow_le_one hd.le h.le hσ.1).trans (le_max_left _ _)

/-- **`lem:pln-data` (b).** `|𝐌_σ z| ≤ B₃` for `|z| ≤ R†`, `σ ∈ [0, 1]`. -/
theorem Msig_norm_le {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : ‖z‖ ≤ Rdag P) :
    ‖Msig P σ z‖ ≤ B3 P := by
  set D := max 1 (max |A11 P| |A22 P|)
  have hD0 : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  have hd1 : |A11 P| ^ σ ≤ D := (rpow_le_max (abs_A11_pos P) hσ).trans
    (max_le_max le_rfl (le_max_left _ _))
  have hd2 : |A22 P| ^ σ ≤ D := (rpow_le_max (abs_A22_pos P) hσ).trans
    (max_le_max le_rfl (le_max_right _ _))
  have hd1' : 0 ≤ |A11 P| ^ σ := Real.rpow_nonneg (abs_nonneg _) _
  have hd2' : 0 ≤ |A22 P| ^ σ := Real.rpow_nonneg (abs_nonneg _) _
  rw [Msig, Inner.norm_Rot]
  set a := |A11 P| ^ σ * z.re
  set b := |A22 P| ^ σ * z.im
  have hn : ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I‖ = √(a ^ 2 + b ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring_nf
  rw [hn]
  have hz2 : z.re ^ 2 + z.im ^ 2 ≤ Rdag P ^ 2 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [← this]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have ha : a ^ 2 ≤ D ^ 2 * z.re ^ 2 := by
    simp only [a]; rw [mul_pow]; gcongr
  have hb : b ^ 2 ≤ D ^ 2 * z.im ^ 2 := by
    simp only [b]; rw [mul_pow]; gcongr
  calc √(a ^ 2 + b ^ 2) ≤ √((Rdag P * D) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = B3 P := by rw [Real.sqrt_sq (mul_nonneg (Rdag_pos P).le hD0)]; rfl

lemma one_le_D : 1 ≤ max 1 (max |A11 P| |A22 P|) := le_max_left _ _

lemma Rdag_le_B3 : Rdag P ≤ B3 P := by
  unfold B3
  have := Rdag_pos P
  nlinarith [one_le_D P]

lemma Msig_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Msig P p.1 p.2) := by
  have hr1 : ContDiff ℝ ∞ (fun σ : ℝ => |A11 P| ^ σ) :=
    contDiff_const.rpow contDiff_id fun _ => (abs_A11_pos P).ne'
  have hr2 : ContDiff ℝ ∞ (fun σ : ℝ => |A22 P| ^ σ) :=
    contDiff_const.rpow contDiff_id fun _ => (abs_A22_pos P).ne'
  have hre : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.re) := reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.im) := imCLM.contDiff.comp contDiff_snd
  simp only [Msig_re_im]
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp ((ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_fst)).mul contDiff_const)).mul
    ((ofRealCLM.contDiff.comp ((hr1.comp contDiff_fst).mul hre)).add
      ((ofRealCLM.contDiff.comp ((hr2.comp contDiff_fst).mul him)).mul contDiff_const))

/-! ### The five segments and the path (`cons:pln-five-segment`) -/

/-- The flat clock `σ_j(t) = S(5t - j)`. -/
def clock (j : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (5 * t - j)

/-- **`cons:pln-five-segment`.** The five segments `𝔢^j_σ`. -/
def seg : ℕ → ℝ → ℂ → ℂ
  | 0, σ, z => ((cnew P ^ σ : ℝ) : ℂ) * z
  | 1, σ, z => (σ : ℂ) * bpt P + (cnew P : ℂ) * z
  | 2, σ, z => bpt P + (cnew P : ℂ) * Msig P σ z
  | 3, σ, z => bpt P + (cnew P : ℂ) * (qinner P σ z - bpt P)
  | _, σ, z => bpt P + ((cnew P ^ (1 - σ) : ℝ) : ℂ) * (qinner P 1 z - bpt P)

/-- **`cons:pln-five-segment`.** The ordinary path `𝔢_t`, as one telescoped formula in the clocks. -/
def ordPath (t : ℝ) (z : ℂ) : ℂ :=
  ((cnew P ^ clock 0 t : ℝ) : ℂ) * z + (clock 1 t : ℂ) * bpt P +
    (cnew P : ℂ) * (Msig P (clock 2 t) z - z) +
    (cnew P : ℂ) * (qinner P (clock 3 t) z - bpt P - A0 P z) +
    ((cnew P ^ (1 - clock 4 t) - cnew P : ℝ) : ℂ) * (qinner P 1 z - bpt P)

/-- **`cons:pln-five-segment`.** `γ_t = det D𝔢_t = c^{2S(5t) - 2S(5t-4)}`. -/
def gammaDet (t : ℝ) : ℝ := cnew P ^ (2 * clock 0 t - 2 * clock 4 t)

/-! ### Clocks -/

lemma clock_mem (j : ℕ) (t : ℝ) : clock j t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_eq_zero {j : ℕ} {t : ℝ} (h : 5 * t ≤ j) : clock j t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma clock_eq_one {j : ℕ} {t : ℝ} (h : (j : ℝ) + 1 ≤ 5 * t) : clock j t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma clock_contDiff (j : ℕ) : ContDiff ℝ ∞ (clock j) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma clock4_le_clock0 (t : ℝ) : clock 4 t ≤ clock 0 t :=
  Real.smoothTransition.monotone (by push_cast; linarith)

/-! ### `(a)` matching and the piecewise description -/

lemma ordPath_of_nonpos {t : ℝ} (ht : t ≤ 0) (z : ℂ) : ordPath P t z = z := by
  have h : ∀ j : ℕ, clock j t = 0 := fun j => clock_eq_zero (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  simp only [ordPath, h, Real.rpow_zero, Msig_zero, qinner_zero, sub_zero]
  simp

lemma ordPath_of_one_le {t : ℝ} (ht : 1 ≤ t) (z : ℂ) : ordPath P t z = qinner P 1 z := by
  have h : ∀ j : ℕ, j ≤ 4 → clock j t = 1 := fun j hj => clock_eq_one (by
    have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
    linarith)
  simp only [ordPath, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 le_rfl, Real.rpow_one, Msig_one, sub_self, Real.rpow_zero]
  push_cast; ring

/-- **`cons:pln-five-segment`.** On `[j/5, (j+1)/5]`, `𝔢_t = 𝔢^j_{S(5t-j)}`. -/
theorem ordPath_eq_seg {j : ℕ} (hj : j ≤ 4) {t : ℝ} (ht : t ∈ Icc ((j : ℝ) / 5) ((j + 1) / 5))
    (z : ℂ) : ordPath P t z = seg P j (clock j t) z := by
  have h5 : (j : ℝ) ≤ 5 * t ∧ 5 * t ≤ j + 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlo : ∀ i : ℕ, i < j → clock i t = 1 := fun i hi => clock_eq_one (by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hi
    linarith)
  have hhi : ∀ i : ℕ, j < i → clock i t = 0 := fun i hi => clock_eq_zero (by
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hi
    linarith)
  interval_cases j
  · simp only [ordPath, seg, hhi 1 (by norm_num), hhi 2 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), Msig_zero, qinner_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hhi 2 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), Msig_zero, qinner_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), qinner_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hlo 2 (by norm_num),
      hhi 4 (by norm_num), Msig_one, Real.rpow_one, sub_zero]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hlo 2 (by norm_num),
      hlo 3 (by norm_num), Msig_one, Real.rpow_one]
    push_cast; ring

/-- Case analysis on the time slots. -/
theorem time_cases {Q : ℝ → Prop} (h0 : ∀ t ≤ 0, Q t) (h1 : ∀ t, 1 ≤ t → Q t)
    (hj : ∀ j : ℕ, j ≤ 4 → ∀ t ∈ Icc ((j : ℝ) / 5) ((j + 1) / 5), Q t) (t : ℝ) : Q t := by
  rcases le_or_gt t 0 with ht | ht
  · exact h0 t ht
  rcases le_or_gt t (1 / 5) with ht1 | ht1
  · exact hj 0 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (2 / 5) with ht2 | ht2
  · exact hj 1 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (3 / 5) with ht3 | ht3
  · exact hj 2 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (4 / 5) with ht4 | ht4
  · exact hj 3 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t 1 with ht5 | ht5
  · exact hj 4 le_rfl t ⟨by norm_num; linarith, by norm_num; linarith⟩
  · exact h1 t ht5.le

/-! ### `(a)` smoothness -/

lemma cpow_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun t => cnew P ^ f t) :=
  contDiff_const.rpow hf fun _ => (cnew_pos P).1.ne'

/-- **`lem:pln-five-segment` (a).** `(t, z) ↦ 𝔢_t(z)` is `C^∞` on `ℝ × D(p†)`. -/
theorem ordPath_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ordPath P p.1 p.2) (univ ×ˢ srcDisk P) := by
  have hq := qinner_smooth P
  have hc : ∀ j, ContDiff ℝ ∞ (fun p : ℝ × ℂ => clock j p.1) := fun j =>
    (clock_contDiff j).comp contDiff_fst
  have hq3 : ContDiffOn ℝ ∞ ((fun q : ℝ × ℂ => qinner P q.1 q.2) ∘
      (fun p : ℝ × ℂ => (clock 3 p.1, p.2))) (univ ×ˢ srcDisk P) :=
    hq.comp ((hc 3).contDiffOn.prodMk contDiffOn_snd) fun p hp => ⟨clock_mem 3 p.1, hp.2⟩
  have hq1 : ContDiffOn ℝ ∞ ((fun q : ℝ × ℂ => qinner P q.1 q.2) ∘
      (fun p : ℝ × ℂ => ((1 : ℝ), p.2))) (univ ×ˢ srcDisk P) :=
    hq.comp ((contDiffOn_const (c := (1 : ℝ))).prodMk contDiffOn_snd)
      fun p hp => ⟨⟨zero_le_one, le_rfl⟩, hp.2⟩
  have hM : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Msig P (clock 2 p.1) p.2) :=
    (Msig_contDiff P).comp ((hc 2).prodMk contDiff_snd)
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℂ => A0 P p.2) := (A0 P).contDiff.comp contDiff_snd
  have hz : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2) := contDiff_snd
  have hc0 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((cnew P ^ clock 0 p.1 : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp ((cpow_contDiff P _ (clock_contDiff 0)).comp contDiff_fst)
  have hc4 : ContDiff ℝ ∞
      (fun p : ℝ × ℂ => ((cnew P ^ (1 - clock 4 p.1) - cnew P : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (((cpow_contDiff P _ (contDiff_const.sub (clock_contDiff 4))).sub
      contDiff_const).comp contDiff_fst)
  have hc1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (clock 1 p.1 : ℂ)) :=
    ofRealCLM.contDiff.comp (hc 1)
  set S := univ ×ˢ srcDisk P
  have t1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ((cnew P ^ clock 0 p.1 : ℝ) : ℂ) * p.2) S :=
    (hc0.mul hz).contDiffOn
  have t2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (clock 1 p.1 : ℂ) * bpt P) S :=
    (hc1.mul contDiff_const).contDiffOn
  have t3 : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => (cnew P : ℂ) * (Msig P (clock 2 p.1) p.2 - p.2)) S :=
    (contDiff_const.mul (hM.sub hz)).contDiffOn
  have t4 := (contDiffOn_const (c := (cnew P : ℂ))).mul
    ((hq3.sub (contDiffOn_const (c := bpt P))).sub hA.contDiffOn)
  have t5 := hc4.contDiffOn.mul (hq1.sub (contDiffOn_const (c := bpt P)))
  refine ((((t1.add t2).add t3).add t4).add t5).congr fun p _ => ?_
  simp only [ordPath, Function.comp]

/-! ### `(b)` injectivity and the Jacobian determinant -/

lemma qinner_one_injOn : InjOn (qinner P 1) (srcDisk P) := qinner_injOn P ⟨zero_le_one, le_rfl⟩

lemma ofReal_ne_zero_of_pos {r : ℝ} (hr : 0 < r) : (r : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr hr.ne'

/-- Each segment is injective on `D(p†)`. -/
theorem seg_injOn {j : ℕ} {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : InjOn (seg P j σ) (srcDisk P) := by
  have hc := (cnew_pos P).1
  have hc' := ofReal_ne_zero_of_pos hc
  intro z₁ hz₁ z₂ hz₂ h
  match j with
  | 0 =>
    simp only [seg] at h
    exact mul_left_cancel₀ (ofReal_ne_zero_of_pos (Real.rpow_pos_of_pos hc σ)) h
  | 1 =>
    simp only [seg, add_right_inj] at h
    exact mul_left_cancel₀ hc' h
  | 2 =>
    simp only [seg, add_right_inj] at h
    have h' := mul_left_cancel₀ hc' h
    rw [Msig_eq] at h'
    exact Inner.injective_of_det_ne_zero _ (by rw [Msig_det]; norm_num) h'
  | 3 =>
    simp only [seg, add_right_inj] at h
    exact qinner_injOn P hσ hz₁ hz₂ (sub_left_inj.mp (mul_left_cancel₀ hc' h))
  | j + 4 =>
    simp only [seg, add_right_inj] at h
    exact qinner_one_injOn P hz₁ hz₂
      (sub_left_inj.mp (mul_left_cancel₀ (ofReal_ne_zero_of_pos (Real.rpow_pos_of_pos hc _)) h))

/-- **`lem:pln-five-segment` (b).** Each `𝔢_t` is injective on `D(p†)`. -/
theorem ordPath_injOn (t : ℝ) : InjOn (ordPath P t) (srcDisk P) := by
  refine time_cases (Q := fun t => InjOn (ordPath P t) (srcDisk P)) ?_ ?_ ?_ t
  · intro t ht
    have : ordPath P t = id := funext (ordPath_of_nonpos P ht)
    rw [this]; exact injOn_id _
  · intro t ht
    have : ordPath P t = qinner P 1 := funext (ordPath_of_one_le P ht)
    rw [this]; exact qinner_one_injOn P
  · intro j hj t ht
    have : ordPath P t = seg P j (clock j t) := funext (ordPath_eq_seg P hj ht)
    rw [this]; exact seg_injOn P (clock_mem j t)

/-- `det D(p + r F) = r² det DF`. -/
lemma det_affine_scale {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (p : ℂ) (r : ℝ) :
    LinearMap.det (fderiv ℝ (fun z => p + (r : ℂ) * F z) z : ℂ →ₗ[ℝ] ℂ) =
      r ^ 2 * LinearMap.det (fderiv ℝ F z : ℂ →ₗ[ℝ] ℂ) := by
  have h := (hF.hasFDerivAt.const_mul (r : ℂ)).const_add p
  have hsm : ((r : ℂ) • fderiv ℝ F z : ℂ →L[ℝ] ℂ) = r • fderiv ℝ F z := by
    ext1 x; simp [Complex.real_smul]
  rw [h.fderiv, hsm, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, Complex.finrank_real_complex]

lemma qinner_differentiableAt {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ srcDisk P) :
    DifferentiableAt ℝ (qinner P σ) z := by
  have hdom := (qinner_dom P hσ (le_of_lt hz)).2
  exact ((Clam_slice_contDiffAt P hdom).differentiableAt (by simp)).comp z
    ((fs_contDiff P hσ).differentiable (by simp) z)

lemma cnew_rpow_sq (x : ℝ) : (cnew P ^ x) ^ 2 = cnew P ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (cnew_pos P).1.le]; norm_num; ring_nf

/-- The spatial determinant of each segment. -/
theorem seg_det {j : ℕ} (hj : j ≤ 4) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z ∈ srcDisk P) :
    LinearMap.det (fderiv ℝ (seg P j σ) z : ℂ →ₗ[ℝ] ℂ) =
      if j = 0 then cnew P ^ (2 * σ) else if j = 4 then cnew P ^ (2 - 2 * σ) else cnew P ^ 2 := by
  have hid : DifferentiableAt ℝ (fun z : ℂ => z) z := differentiableAt_id
  have hq1 := qinner_differentiableAt P (σ := 1) ⟨zero_le_one, le_rfl⟩ hz
  have hqs := qinner_differentiableAt P hσ hz
  interval_cases j
  · have hfun : seg P 0 σ = fun z => 0 + ((cnew P ^ σ : ℝ) : ℂ) * z := by
      funext z; simp [seg]
    rw [hfun, det_affine_scale hid, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id,
      mul_one, cnew_rpow_sq]
    simp
  · have hfun : seg P 1 σ = fun z => (σ : ℂ) * bpt P + ((cnew P : ℝ) : ℂ) * z := rfl
    rw [hfun, det_affine_scale hid, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
    simp
  · have hfun : seg P 2 σ = fun z => bpt P + ((cnew P : ℝ) : ℂ) * MsigL P σ z := by
      funext z; simp [seg, MsigL_apply]
    rw [hfun, det_affine_scale (MsigL P σ).differentiableAt, ContinuousLinearMap.fderiv,
      Msig_det]
    simp
  · have hfun : seg P 3 σ = fun z => bpt P + ((cnew P : ℝ) : ℂ) * (qinner P σ z - bpt P) := rfl
    rw [hfun, det_affine_scale (hqs.sub_const _)]
    have : fderiv ℝ (fun z => qinner P σ z - bpt P) z = fderiv ℝ (qinner P σ) z :=
      fderiv_sub_const _
    rw [this, qinner_symplectic P hσ (le_of_lt hz)]
    simp
  · have hfun : seg P 4 σ = fun z => bpt P + ((cnew P ^ (1 - σ) : ℝ) : ℂ) *
        (qinner P 1 z - bpt P) := rfl
    rw [hfun, det_affine_scale (hq1.sub_const _)]
    have : fderiv ℝ (fun z => qinner P 1 z - bpt P) z = fderiv ℝ (qinner P 1) z :=
      fderiv_sub_const _
    rw [this, qinner_symplectic P ⟨zero_le_one, le_rfl⟩ (le_of_lt hz), cnew_rpow_sq]
    simp; ring_nf

/-- **`lem:pln-five-segment` (b).** `det D𝔢_t = γ_t` on `D(p†)`, a constant in `z`. -/
theorem ordPath_det (t : ℝ) {z : ℂ} (hz : z ∈ srcDisk P) :
    LinearMap.det (fderiv ℝ (ordPath P t) z : ℂ →ₗ[ℝ] ℂ) = gammaDet P t := by
  refine time_cases (Q := fun t => LinearMap.det (fderiv ℝ (ordPath P t) z : ℂ →ₗ[ℝ] ℂ) =
    gammaDet P t) ?_ ?_ ?_ t
  · intro t ht
    have : ordPath P t = id := funext (ordPath_of_nonpos P ht)
    have h0 : ∀ j : ℕ, clock j t = 0 := fun j => clock_eq_zero (by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    rw [this, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id, gammaDet, h0, h0]
    simp
  · intro t ht
    have : ordPath P t = qinner P 1 := funext (ordPath_of_one_le P ht)
    have h1 : ∀ j : ℕ, j ≤ 4 → clock j t = 1 := fun j hj => clock_eq_one (by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
      linarith)
    rw [this, qinner_symplectic P ⟨zero_le_one, le_rfl⟩ (le_of_lt hz), gammaDet,
      h1 0 (by norm_num), h1 4 le_rfl]
    simp
  · intro j hj t ht
    have hfun : ordPath P t = seg P j (clock j t) := funext (ordPath_eq_seg P hj ht)
    have h5a : (j : ℝ) ≤ 5 * t := by linarith [ht.1]
    have h5b : 5 * t ≤ j + 1 := by linarith [ht.2]
    rw [hfun, seg_det P hj (clock_mem j t) hz, gammaDet]
    interval_cases j
    · norm_num at h5a h5b
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      simp [h0]

/-- **`lem:pln-five-segment` (b).** `c² ≤ γ_t ≤ 1`, `γ_0 = γ_1 = 1`. -/
theorem gammaDet_bounds (t : ℝ) :
    cnew P ^ 2 ≤ gammaDet P t ∧ gammaDet P t ≤ 1 ∧ gammaDet P 0 = 1 ∧ gammaDet P 1 = 1 := by
  have hc := cnew_pos P
  have hc1 : cnew P ≤ 1 := by linarith [hc.2]
  have h40 := clock4_le_clock0 t
  have h0 := clock_mem 0 t
  have h4 := clock_mem 4 t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_exponent_ge hc.1 hc1
      (show 2 * clock 0 t - 2 * clock 4 t ≤ 2 by linarith [h0.2, h4.1])
    rw [gammaDet]; simpa using this
  · exact Real.rpow_le_one hc.1.le hc1 (by linarith)
  · rw [gammaDet, clock_eq_zero (j := 0) (by norm_num), clock_eq_zero (j := 4) (by norm_num)]
    simp
  · rw [gammaDet, clock_eq_one (j := 0) (by norm_num), clock_eq_one (j := 4) (by norm_num)]
    simp

/-! ### `(c)` the image -/

lemma norm_bpt : ‖bpt P‖ = rb P := by
  rw [bpt, norm_neg, Complex.norm_real, Real.norm_of_nonneg (rb_pos P).le]

lemma rb_le_Rsupp : rb P ≤ Rsupp P := by
  have := mul_nonneg (cnew_pos P).1.le ((Rdag_pos P).le.trans (Rdag_le_B3 P))
  exact (by linarith : rb P ≤ rb P + cnew P * B3 P).trans
    ((le_max_right _ _).trans (le_max_left _ _))

/-- Each segment maps `D(p†)` into the closed disk of radius `R_supp`. -/
theorem seg_image {j : ℕ} {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ srcDisk P) :
    ‖seg P j σ z‖ ≤ Rsupp P := by
  have hc := cnew_pos P
  have hzR := (norm_lt_Rdag P hz).le
  have hb := norm_bpt P
  have hR1 : Rdag P ≤ Rsupp P := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : rb P + cnew P * B3 P ≤ Rsupp P := (le_max_right _ _).trans (le_max_left _ _)
  have hR3 : rb P + cnew P * Bstar P ≤ Rsupp P := (le_max_left _ _).trans (le_max_right _ _)
  have hR4 : Rq P ≤ Rsupp P := (le_max_right _ _).trans (le_max_right _ _)
  have hcB : cnew P * Rdag P ≤ cnew P * B3 P := mul_le_mul_of_nonneg_left (Rdag_le_B3 P) hc.1.le
  match j with
  | 0 =>
    simp only [seg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.1.le _)]
    have := Real.rpow_le_one hc.1.le (by linarith [hc.2]) hσ.1
    nlinarith [norm_nonneg z]
  | 1 =>
    simp only [seg]
    calc ‖(σ : ℂ) * bpt P + (cnew P : ℂ) * z‖ ≤ ‖(σ : ℂ) * bpt P‖ + ‖(cnew P : ℂ) * z‖ :=
          norm_add_le _ _
      _ = σ * rb P + cnew P * ‖z‖ := by
          rw [norm_mul, norm_mul, hb, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hσ.1, Real.norm_of_nonneg hc.1.le]
      _ ≤ 1 * rb P + cnew P * Rdag P := by
          have := mul_le_mul_of_nonneg_left hzR hc.1.le
          have := mul_le_mul_of_nonneg_right hσ.2 (rb_pos P).le
          linarith
      _ ≤ Rsupp P := by linarith
  | 2 =>
    simp only [seg]
    calc ‖bpt P + (cnew P : ℂ) * Msig P σ z‖ ≤ ‖bpt P‖ + ‖(cnew P : ℂ) * Msig P σ z‖ :=
          norm_add_le _ _
      _ = rb P + cnew P * ‖Msig P σ z‖ := by
          rw [norm_mul, hb, Complex.norm_real, Real.norm_of_nonneg hc.1.le]
      _ ≤ rb P + cnew P * B3 P := by
          have := mul_le_mul_of_nonneg_left (Msig_norm_le P hσ hzR) hc.1.le; linarith
      _ ≤ Rsupp P := hR2
  | 3 =>
    simp only [seg]
    calc ‖bpt P + (cnew P : ℂ) * (qinner P σ z - bpt P)‖
        ≤ ‖bpt P‖ + ‖(cnew P : ℂ) * (qinner P σ z - bpt P)‖ := norm_add_le _ _
      _ = rb P + cnew P * ‖qinner P σ z - bpt P‖ := by
          rw [norm_mul, hb, Complex.norm_real, Real.norm_of_nonneg hc.1.le]
      _ ≤ rb P + cnew P * Bstar P := by
          have := mul_le_mul_of_nonneg_left (qinner_sub_b_le P hσ (le_of_lt hz)) hc.1.le
          linarith
      _ ≤ Rsupp P := hR3
  | j + 4 =>
    simp only [seg]
    set μ := cnew P ^ (1 - σ)
    have hμ0 : 0 ≤ μ := Real.rpow_nonneg hc.1.le _
    have hμ1 : μ ≤ 1 := Real.rpow_le_one hc.1.le (by linarith [hc.2]) (by linarith [hσ.2])
    have hq := qinner_one_norm_le P (le_of_lt hz)
    have heq : bpt P + (μ : ℂ) * (qinner P 1 z - bpt P) =
        ((1 - μ : ℝ) : ℂ) * bpt P + (μ : ℂ) * qinner P 1 z := by push_cast; ring
    rw [heq]
    calc ‖((1 - μ : ℝ) : ℂ) * bpt P + (μ : ℂ) * qinner P 1 z‖
        ≤ ‖((1 - μ : ℝ) : ℂ) * bpt P‖ + ‖(μ : ℂ) * qinner P 1 z‖ := norm_add_le _ _
      _ = (1 - μ) * rb P + μ * ‖qinner P 1 z‖ := by
          rw [norm_mul, norm_mul, hb, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hμ0]
      _ ≤ (1 - μ) * Rsupp P + μ * Rsupp P := by
          have h1 := mul_le_mul_of_nonneg_left (rb_le_Rsupp P) (by linarith : (0 : ℝ) ≤ 1 - μ)
          have h2 := mul_le_mul_of_nonneg_left (hq.trans hR4) hμ0
          linarith
      _ = Rsupp P := by ring

/-- **`lem:pln-five-segment` (c).** `𝔢_t(D(p†)) ⊂ {|y| ≤ R_supp}` for all `t`. -/
theorem ordPath_image (t : ℝ) {z : ℂ} (hz : z ∈ srcDisk P) : ‖ordPath P t z‖ ≤ Rsupp P := by
  refine time_cases (Q := fun t => ‖ordPath P t z‖ ≤ Rsupp P) ?_ ?_ ?_ t
  · intro t ht
    rw [ordPath_of_nonpos P ht]
    exact (norm_lt_Rdag P hz).le.trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro t ht
    rw [ordPath_of_one_le P ht]
    exact (qinner_one_norm_le P (le_of_lt hz)).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro j hj t ht
    rw [ordPath_eq_seg P hj ht]
    exact seg_image P (clock_mem j t) hz

/-- **`lem:pln-five-segment` (c), area form.** `π|𝔢_t(z)|² ≤ P_supp`. -/
theorem ordPath_image_area (t : ℝ) {z : ℂ} (hz : z ∈ srcDisk P) :
    π * ‖ordPath P t z‖ ^ 2 ≤ Psupp P := by
  have h := ordPath_image P t hz
  unfold Psupp
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) Real.pi_pos.le

lemma ordPath_eq_one {t : ℝ} (ht : 1 ≤ t) (z : ℂ) : ordPath P t z = ordPath P 1 z := by
  rw [ordPath_of_one_le P ht, ordPath_of_one_le P le_rfl]

/-- `t ↦ γ_t` is `C^∞`. -/
theorem gammaDet_contDiff : ContDiff ℝ ∞ (gammaDet P) :=
  cpow_contDiff P _ ((contDiff_const.mul (clock_contDiff 0)).sub
    (contDiff_const.mul (clock_contDiff 4)))

end SymplecticPacking.Qhat
