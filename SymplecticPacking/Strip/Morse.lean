import Mathlib
import SymplecticPacking.Explicit

/-!
# The strip Morse functions and their inverses

`sec:str` (paper `cons:str-morse`, `lem:str-morse-inverse`, `lem:str-area` (i), (ii)):
the strip Morse functions `R_st`, `V_st`, their explicit Morse inverses `X_st`, `Y_st`, and the
width of the sublevel sets of `R_st`.

All functions take the parameter `b = b_st > 0` (in the paper `b_st = δ/π`, see `bst`).
-/

noncomputable section

namespace SymplecticPacking.Strip

open Filter Topology Set
open scoped ContDiff Real

set_option linter.unusedSectionVars false

/-! ### Definitions (`cons:str-morse`) -/

/-- `b_st = δ/π`. -/
def bst (δ : ℝ) : ℝ := δ / π

/-- `R_st(x) = x + b²/(4x) - b` (meaningful for `x > 0`). -/
def Rst (b x : ℝ) : ℝ := x + b ^ 2 / (4 * x) - b

/-- `V_st(T) = b [1/(2√(T(1-T))) - 1]` (meaningful for `0 < T < 1`). -/
def Vst (b T : ℝ) : ℝ := b * (1 / (2 * Real.sqrt (T * (1 - T))) - 1)

/-- `X_st(u) = [u² + b + u √(u² + 2b)]/2`. -/
def Xst (b u : ℝ) : ℝ := (u ^ 2 + b + u * Real.sqrt (u ^ 2 + 2 * b)) / 2

/-- The odd function `φ(v) = v √(v² + 2b)/(v² + b)`, so that `Y_st = 1/2 + φ/2`. -/
def phiSt (b v : ℝ) : ℝ := v * Real.sqrt (v ^ 2 + 2 * b) / (v ^ 2 + b)

/-- `Y_st(v) = 1/2 + v √(v² + 2b) / (2 (v² + b))`. -/
def Yst (b v : ℝ) : ℝ := 1 / 2 + v * Real.sqrt (v ^ 2 + 2 * b) / (2 * (v ^ 2 + b))

/-- `X_st'(u) = (u + √(u² + 2b))² / (2 √(u² + 2b))`. -/
def XstD (b u : ℝ) : ℝ :=
  (u + Real.sqrt (u ^ 2 + 2 * b)) ^ 2 / (2 * Real.sqrt (u ^ 2 + 2 * b))

/-- `Y_st'(v) = b² / (√(v² + 2b) (v² + b)²)`. -/
def YstD (b v : ℝ) : ℝ := b ^ 2 / (Real.sqrt (v ^ 2 + 2 * b) * (v ^ 2 + b) ^ 2)

theorem bst_pos {δ : ℝ} (hδ : 0 < δ) : 0 < bst δ := div_pos hδ Real.pi_pos

theorem Yst_eq_phi (b v : ℝ) : Yst b v = 1 / 2 + phiSt b v / 2 := by
  unfold Yst phiSt; rw [mul_comm 2 (v ^ 2 + b), ← div_div]

/-- `T(1-T) ≤ 1/4`. -/
theorem mul_one_sub_le (T : ℝ) : T * (1 - T) ≤ 1 / 4 := by nlinarith [sq_nonneg (T - 1 / 2)]

section
variable {b : ℝ} (hb : 0 < b)
include hb

/-! ### Elementary facts on the square roots -/

theorem sq_sqrt_u (u : ℝ) : Real.sqrt (u ^ 2 + 2 * b) ^ 2 = u ^ 2 + 2 * b :=
  Real.sq_sqrt (by positivity)

theorem sqrt_u_pos (u : ℝ) : 0 < Real.sqrt (u ^ 2 + 2 * b) := Real.sqrt_pos.mpr (by positivity)

/-- `|u| < √(u² + 2b)`. -/
theorem abs_lt_sqrt_u (u : ℝ) : |u| < Real.sqrt (u ^ 2 + 2 * b) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

theorem add_sqrt_u_pos (u : ℝ) : 0 < u + Real.sqrt (u ^ 2 + 2 * b) := by
  have := abs_lt_sqrt_u hb u; have := neg_abs_le u; linarith

theorem Vst_nonneg {T : ℝ} (h0 : 0 < T) (h1 : T < 1) : 0 ≤ Vst b T := by
  have hp : 0 < T * (1 - T) := mul_pos h0 (by linarith)
  have hs : Real.sqrt (T * (1 - T)) ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [mul_one_sub_le T]
  have hs0 := Real.sqrt_pos.mpr hp
  unfold Vst
  have : 1 ≤ 1 / (2 * Real.sqrt (T * (1 - T))) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  nlinarith

/-! ### `lem:str-morse-inverse` (ii) -/

theorem Xst_pos (u : ℝ) : 0 < Xst b u := by
  have h1 := sq_sqrt_u hb u
  have h2 := sqrt_u_pos hb u
  unfold Xst
  have hsq : (u * Real.sqrt (u ^ 2 + 2 * b)) ^ 2 < (u ^ 2 + b) ^ 2 := by
    rw [mul_pow, h1]; nlinarith
  have := (abs_lt_of_sq_lt_sq' hsq (by positivity)).1
  linarith

theorem Rst_Xst (u : ℝ) : Rst b (Xst b u) = u ^ 2 := by
  have hX := Xst_pos hb u
  have h1 := sq_sqrt_u hb u
  have key : 4 * Xst b u ^ 2 - 4 * (u ^ 2 + b) * Xst b u + b ^ 2 = 0 := by
    unfold Xst; linear_combination u ^ 2 * h1
  unfold Rst
  field_simp
  linear_combination key

/-- `φ(v)² = 1 - b²/(v² + b)²`. -/
theorem phiSt_sq (v : ℝ) : phiSt b v ^ 2 = 1 - (b / (v ^ 2 + b)) ^ 2 := by
  have h1 := sq_sqrt_u hb v
  have hv : 0 < v ^ 2 + b := by positivity
  unfold phiSt
  field_simp
  rw [h1]; ring

theorem abs_phiSt_lt (v : ℝ) : |phiSt b v| < 1 := by
  have h := phiSt_sq hb v
  have hv : 0 < b / (v ^ 2 + b) := by positivity
  have : phiSt b v ^ 2 < 1 ^ 2 := by nlinarith
  exact abs_lt_of_sq_lt_sq this (by norm_num)

/-- `√(1 - φ²) = b/(v² + b)`. -/
theorem sqrt_one_sub_phiSt_sq (v : ℝ) : Real.sqrt (1 - phiSt b v ^ 2) = b / (v ^ 2 + b) := by
  rw [phiSt_sq hb, sub_sub_cancel, Real.sqrt_sq (by positivity)]

theorem Yst_mem (v : ℝ) : 0 < Yst b v ∧ Yst b v < 1 := by
  have := abs_lt.mp (abs_phiSt_lt hb v)
  rw [Yst_eq_phi]; constructor <;> linarith

theorem Vst_Yst (v : ℝ) : Vst b (Yst b v) = v ^ 2 := by
  have hv : 0 < v ^ 2 + b := by positivity
  have hT : Yst b v * (1 - Yst b v) = (b / (2 * (v ^ 2 + b))) ^ 2 := by
    rw [Yst_eq_phi]
    have := phiSt_sq hb v
    have e : (1 / 2 + phiSt b v / 2) * (1 - (1 / 2 + phiSt b v / 2)) = (1 - phiSt b v ^ 2) / 4 := by
      ring
    rw [e, this]; field_simp; ring
  unfold Vst
  rw [hT, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-! ### `lem:str-morse-inverse` (iii) -/

theorem hasDerivAt_sqrt_u (u : ℝ) :
    HasDerivAt (fun u => Real.sqrt (u ^ 2 + 2 * b))
      (2 * u / (2 * Real.sqrt (u ^ 2 + 2 * b))) u := by
  have h := ((hasDerivAt_pow 2 u).add_const (2 * b)).sqrt (by positivity)
  convert h using 1; push_cast; ring

theorem deriv_Xst (u : ℝ) : HasDerivAt (Xst b) (XstD b u) u := by
  have hr := sqrt_u_pos hb u
  have h1 := sq_sqrt_u hb u
  have h := ((((hasDerivAt_pow 2 u).add_const b).add
    ((hasDerivAt_id u).mul (hasDerivAt_sqrt_u hb u))).div_const 2)
  convert h using 1
  · funext x; simp [Xst]
  · unfold XstD
    field_simp
    simp only [id]
    ring

theorem XstD_pos (u : ℝ) : 0 < XstD b u := by
  unfold XstD
  have := add_sqrt_u_pos hb u; have := sqrt_u_pos hb u; positivity

theorem deriv_Yst (v : ℝ) : HasDerivAt (Yst b) (YstD b v) v := by
  have hr := sqrt_u_pos hb v
  have h1 := sq_sqrt_u hb v
  have hv : 0 < v ^ 2 + b := by positivity
  have hd : HasDerivAt (fun v => 2 * (v ^ 2 + b)) (2 * (2 * v)) v := by
    simpa using ((hasDerivAt_pow 2 v).add_const b).const_mul 2
  have h := ((hasDerivAt_id v).mul (hasDerivAt_sqrt_u hb v)).div hd (by positivity)
  have h' := h.const_add (1 / 2)
  convert h' using 1
  · funext x; simp [Yst]
  · unfold YstD
    simp only [Pi.mul_apply, id]
    generalize Real.sqrt (v ^ 2 + 2 * b) = R at h1 hr ⊢
    field_simp
    linear_combination (v ^ 2 - b) * h1

theorem YstD_pos (v : ℝ) : 0 < YstD b v := by
  unfold YstD
  have := sqrt_u_pos hb v
  have : 0 < v ^ 2 + b := by positivity
  positivity

theorem contDiff_sqrt_u : ContDiff ℝ ∞ (fun u : ℝ => Real.sqrt (u ^ 2 + 2 * b)) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt fun u => by positivity

theorem contDiff_Xst : ContDiff ℝ ∞ (Xst b) := by
  unfold Xst
  exact ((((contDiff_id.pow 2).add contDiff_const).add
    (contDiff_id.mul (contDiff_sqrt_u hb))).div_const 2)

theorem contDiff_Yst : ContDiff ℝ ∞ (Yst b) := by
  unfold Yst
  exact contDiff_const.add ((contDiff_id.mul (contDiff_sqrt_u hb)).div
    (contDiff_const.mul ((contDiff_id.pow 2).add contDiff_const)) fun v => by positivity)

theorem contDiff_XstD : ContDiff ℝ ∞ (XstD b) := by
  unfold XstD
  exact ((contDiff_id.add (contDiff_sqrt_u hb)).pow 2).div
    (contDiff_const.mul (contDiff_sqrt_u hb)) fun u => by have := sqrt_u_pos hb u; positivity

theorem contDiff_YstD : ContDiff ℝ ∞ (YstD b) := by
  unfold YstD
  exact contDiff_const.div ((contDiff_sqrt_u hb).mul
    (((contDiff_id.pow 2).add contDiff_const).pow 2)) fun v => by
      have := sqrt_u_pos hb v
      have : 0 < v ^ 2 + b := by positivity
      positivity

theorem Xst_strictMono : StrictMono (Xst b) :=
  strictMono_of_hasDerivAt_pos (deriv_Xst hb) (XstD_pos hb)

theorem Yst_strictMono : StrictMono (Yst b) :=
  strictMono_of_hasDerivAt_pos (deriv_Yst hb) (YstD_pos hb)

/-! ### `lem:str-morse-inverse` (iv) -/

/-- The explicit preimage `u = (x - b/2)/√x` of `x > 0` under `X_st`. -/
theorem Xst_preimage {x : ℝ} (hx : 0 < x) : Xst b ((x - b / 2) / Real.sqrt x) = x := by
  have hs := Real.sqrt_pos.mpr hx
  have hs2 := Real.sq_sqrt hx.le
  set u := (x - b / 2) / Real.sqrt x
  have hr : Real.sqrt (u ^ 2 + 2 * b) = (x + b / 2) / Real.sqrt x := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    simp only [u]; field_simp; rw [hs2]; ring
  unfold Xst
  rw [hr]; simp only [u]; field_simp; rw [hs2]; ring

theorem Xst_bijOn : BijOn (Xst b) univ (Ioi 0) :=
  ⟨fun u _ => Xst_pos hb u, (Xst_strictMono hb).injective.injOn,
    fun _ hx => ⟨_, mem_univ _, Xst_preimage hb hx⟩⟩

/-- The explicit preimage of `T ∈ (0,1)` under `Y_st`: with `s = 2T - 1`, `c = √(1 - s²)`,
`v = s √(b/(c(1+c)))`. -/
theorem Yst_preimage {T : ℝ} (h0 : 0 < T) (h1 : T < 1) :
    Yst b ((2 * T - 1) * Real.sqrt (b / (Real.sqrt (1 - (2 * T - 1) ^ 2) *
      (1 + Real.sqrt (1 - (2 * T - 1) ^ 2))))) = T := by
  set s := 2 * T - 1
  have hs2 : s ^ 2 < 1 := by simp only [s]; nlinarith
  set c := Real.sqrt (1 - s ^ 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  set k := Real.sqrt (b / (c * (1 + c)))
  have hk2 : k ^ 2 = b / (c * (1 + c)) := Real.sq_sqrt (by positivity)
  have hk : 0 < k := Real.sqrt_pos.mpr (by positivity)
  set v := s * k
  have hv2 : v ^ 2 + b = b / c := by
    simp only [v]; rw [mul_pow, hk2]; field_simp; linear_combination hc2
  have hr : Real.sqrt (v ^ 2 + 2 * b) = k * (1 + c) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    have : (k * (1 + c)) * (k * (1 + c)) = k ^ 2 * (1 + c) ^ 2 := by ring
    rw [this, hk2]
    have : v ^ 2 + 2 * b = b / c + b := by linarith
    rw [this]; field_simp
  rw [Yst, hr, hv2]
  simp only [v]
  field_simp
  rw [hk2]
  field_simp
  simp only [s]; ring

theorem Yst_bijOn : BijOn (Yst b) univ (Ioo 0 1) :=
  ⟨fun v _ => Yst_mem hb v, (Yst_strictMono hb).injective.injOn,
    fun _ hT => ⟨_, mem_univ _, Yst_preimage hb hT.1 hT.2⟩⟩

/-! ### `lem:str-area` (i): the sublevel sets of `R_st` -/

/-- Direct form used in the strip estimate: `R_st(x) ≤ q`, `x > 0` imply `x < q + b`. -/
theorem lt_of_Rst_le {x q : ℝ} (hx : 0 < x) (h : Rst b x ≤ q) : x < q + b := by
  unfold Rst at h
  have : 0 < b ^ 2 / (4 * x) := by positivity
  linarith

end

/-! ### `lem:str-area` (ii): `∫₀¹ V_st = b (π/2 - 1)` -/

end SymplecticPacking.Strip
