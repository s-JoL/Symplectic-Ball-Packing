import Mathlib

/-!
# Parameters of the equal-capacity case

The packing parameters for `k` equal balls, the functions `H, P, K, F` with the rearrangement
`Rcal`, the scalar comparison with its margins, and the radii of `sec:iso-parameters`. The
four-dimensional equal-capacity case is run through the general cubic model
(`Branch2.CubicData.ofParams`); these parameters provide its closed-form data and the
comparison isotopy.

All statements here are pure real arithmetic; no geometry is involved.
Notation follows the paper (`t0, rho, a, h, d_n, c_s, g`), with `s = √k`.
-/

noncomputable section

namespace SymplecticPacking

open Real

/-- The packing parameters for given `k` and `ε`. -/
structure Params where
  k : ℕ
  ε : ℝ
  hk : 10 ≤ k
  hε0 : 0 < ε
  hε1 : ε < 1

namespace Params

variable (P : Params)

/-- `s = √k`. -/
def s : ℝ := Real.sqrt P.k
def t0 : ℝ := 1 - P.ε / 8
def rho : ℝ := (1 - P.ε / 4) / P.s
def a : ℝ := P.t0 / P.s
def h : ℝ := P.t0 / 3
def dn : ℝ := (P.h + 1 / 3) / 2
def cs : ℝ := 3 * P.s - 9
def g : ℝ := 3 * P.ε / 8

lemma k_real_ge : (10 : ℝ) ≤ P.k := by exact_mod_cast P.hk

lemma s_sq : P.s ^ 2 = P.k := Real.sq_sqrt (by positivity)

lemma s_gt_three : 3 < P.s := by
  have h10 := P.k_real_ge
  have : Real.sqrt 9 < Real.sqrt P.k :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simpa [s, h9] using this

lemma s_pos : 0 < P.s := by linarith [P.s_gt_three]

lemma t0_pos : 0 < P.t0 := by unfold t0; linarith [P.hε1]
lemma t0_lt_one : P.t0 < 1 := by unfold t0; linarith [P.hε0]

lemma rho_pos : 0 < P.rho := by
  unfold rho; have := P.s_pos; have := P.hε1; apply div_pos <;> linarith

lemma a_pos : 0 < P.a := div_pos P.t0_pos P.s_pos
lemma h_pos : 0 < P.h := by unfold h; linarith [P.t0_pos]

/-- `a - ρ = ε / (8 √k)`. -/
lemma a_sub_rho : P.a - P.rho = P.ε / (8 * P.s) := by
  have := P.s_pos.ne'
  unfold a rho t0; field_simp; ring

lemma rho_lt_a : P.rho < P.a := by
  have : 0 < P.ε / (8 * P.s) := div_pos P.hε0 (by linarith [P.s_pos])
  linarith [P.a_sub_rho]

lemma a_lt_h : P.a < P.h := by
  unfold a h
  have := P.t0_pos; have := P.s_gt_three
  rw [div_lt_div_iff₀ P.s_pos (by norm_num)]
  nlinarith

lemma h_lt_third : P.h < 1 / 3 := by unfold h; linarith [P.t0_lt_one]

lemma h_lt_dn : P.h < P.dn := by unfold dn; linarith [P.h_lt_third]

lemma dn_lt_third : P.dn < 1 / 3 := by unfold dn; linarith [P.h_lt_third]

lemma cs_pos : 0 < P.cs := by unfold cs; linarith [P.s_gt_three]

lemma g_pos : 0 < P.g := by unfold g; linarith [P.hε0]

/-! ### The functions `H, P, K, F` and the rearrangement `Rcal` -/

/-- Base area available at fibre level `p`: `H(p) = 3(1 - 3p)`. -/
def Hb (p : ℝ) : ℝ := 3 * (1 - 3 * p)
/-- `P(p) = H(p) - k (a - p)_+`. -/
def Pb (p : ℝ) : ℝ := Hb p - P.k * max (P.a - p) 0
/-- `K(p) = c_s p`. -/
def K (p : ℝ) : ℝ := P.cs * p
/-- `F = K - P`. -/
def F (p : ℝ) : ℝ := P.K p - P.Pb p

def A : ℝ := P.h / P.a
def B : ℝ := P.h / (P.h - P.a)

lemma A_pos : 0 < P.A := div_pos P.h_pos P.a_pos
lemma B_pos : 0 < P.B := div_pos P.h_pos (by linarith [P.a_lt_h])

/-- `1/A + 1/B = 1`. -/
lemma inv_A_add_inv_B : 1 / P.A + 1 / P.B = 1 := by
  have := P.h_pos.ne'
  have := P.a_pos.ne'
  have : P.h - P.a ≠ 0 := by linarith [P.a_lt_h]
  unfold A B; field_simp; ring

/-- `Rcal(P) = A (a - P)` for `P ≤ a`, `B (P - a)` for `P ≥ a`. -/
def Rcal (x : ℝ) : ℝ := if x ≤ P.a then P.A * (P.a - x) else P.B * (x - P.a)

lemma Rcal_nonneg (x : ℝ) : 0 ≤ P.Rcal x := by
  unfold Rcal; split_ifs with hx
  · exact mul_nonneg P.A_pos.le (by linarith)
  · exact mul_nonneg P.B_pos.le (by linarith)

lemma cs_mul_A : P.cs * P.A = P.k - 3 * P.s := by
  have hs := P.s_pos.ne'
  have ht := P.t0_pos.ne'
  unfold cs A h a
  field_simp
  rw [← P.s_sq]; ring

lemma cs_mul_B : P.cs * P.B = 3 * P.s := by
  have hs3 : P.s - 3 ≠ 0 := by linarith [P.s_gt_three]
  have hs := P.s_pos.ne'
  have ht := P.t0_pos.ne'
  have hha : P.h - P.a = P.t0 * (P.s - 3) / (3 * P.s) := by
    unfold h a; field_simp
  unfold B; rw [hha]; unfold cs h
  field_simp; ring

lemma three_s_a : 3 * P.s * P.a = 3 - P.g := by
  have := P.s_pos.ne'
  unfold a g t0; field_simp

/-- **Identity**: `F(P) = -g + c_s · Rcal(P)` for all real `P`. -/
theorem F_eq (x : ℝ) : P.F x = -P.g + P.cs * P.Rcal x := by
  have h3 := P.three_s_a
  unfold F K Pb Hb Rcal
  split_ifs with hx
  · rw [max_eq_left (by linarith)]
    have : P.cs * (P.A * (P.a - x)) = (P.k - 3 * P.s) * (P.a - x) := by
      rw [← mul_assoc, P.cs_mul_A]
    rw [this]
    have hcs : P.cs = 3 * P.s - 9 := rfl
    rw [hcs]; nlinarith
  · rw [max_eq_right (by linarith)]
    have : P.cs * (P.B * (x - P.a)) = 3 * P.s * (x - P.a) := by
      rw [← mul_assoc, P.cs_mul_B]
    rw [this]
    have hcs : P.cs = 3 * P.s - 9 := rfl
    rw [hcs]; nlinarith

/-- The sublevel set `{Rcal ≤ b}` is the interval `[a - b/A, a + b/B]` (for `b ≥ 0`). -/
lemma Rcal_le_iff {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    P.Rcal x ≤ b ↔ x ∈ Set.Icc (P.a - b / P.A) (P.a + b / P.B) := by
  have hA := P.A_pos
  have hB := P.B_pos
  unfold Rcal
  simp only [Set.mem_Icc]
  split_ifs with hx
  · constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [sub_le_comm, le_div_iff₀ hA]; linarith
      · have : 0 ≤ b / P.B := div_nonneg hb hB.le
        linarith
    · rintro ⟨h1, -⟩
      rw [sub_le_comm, le_div_iff₀ hA] at h1; linarith
  · rw [not_le] at hx
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have : 0 ≤ b / P.A := div_nonneg hb hA.le
        linarith
      · rw [← sub_le_iff_le_add', le_div_iff₀ hB]; linarith
    · rintro ⟨-, h2⟩
      rw [← sub_le_iff_le_add', le_div_iff₀ hB] at h2; linarith

/-- The sublevel interval has length exactly `b`. -/
lemma sublevel_length (b : ℝ) : (P.a + b / P.B) - (P.a - b / P.A) = b := by
  have h := P.inv_A_add_inv_B
  calc (P.a + b / P.B) - (P.a - b / P.A) = b * (1 / P.A + 1 / P.B) := by ring
    _ = b := by rw [h, mul_one]

/-! ### The inner smoothing parameter and margins (1), (10) -/

/-- `e_q = min(h/100, g/(128 c_s))`. -/
def eq_ : ℝ := min (P.h / 100) (P.g / (128 * P.cs))

lemma eq_pos : 0 < P.eq_ :=
  lt_min (by linarith [P.h_pos]) (div_pos P.g_pos (by linarith [P.cs_pos]))

lemma eq_le_h : P.eq_ ≤ P.h / 100 := min_le_left _ _

/-- Margin (1): `g - 4 c_s e_q ≥ 31 g / 32`. -/
theorem margin_one : 31 * P.g / 32 ≤ P.g - 4 * P.cs * P.eq_ := by
  have hcs := P.cs_pos
  have : P.eq_ ≤ P.g / (128 * P.cs) := min_le_right _ _
  have : P.cs * P.eq_ ≤ P.g / 128 := by
    calc P.cs * P.eq_ ≤ P.cs * (P.g / (128 * P.cs)) :=
          mul_le_mul_of_nonneg_left this hcs.le
      _ = P.g / 128 := by field_simp
  linarith

/-- Consequence (1): if `Rcal(p(q z)) ≤ I + 4 e_q` then `K(I) - F(p(q z)) ≥ 31g/32`. -/
theorem K_sub_F_ge {I x : ℝ} (hx : P.Rcal x ≤ I + 4 * P.eq_) :
    31 * P.g / 32 ≤ P.K I - P.F x := by
  rw [P.F_eq]
  have := P.margin_one
  have hcs := P.cs_pos
  unfold K
  nlinarith

/-- Handle background `e_h = g/16`. -/
def eh : ℝ := P.g / 16

/-- `Hstar(p) = 3(1-3p) - e_h`. -/
def Hstar (p : ℝ) : ℝ := Hb p - P.eh

/-- `μ_h = g/(16 k)`. -/
def muh : ℝ := P.g / (16 * P.k)

/-- Smoothed positive part `h_i(p) = [a - p + √((a-p)² + μ_h²)]/2`. -/
def hi (p : ℝ) : ℝ := (P.a - p + Real.sqrt ((P.a - p) ^ 2 + P.muh ^ 2)) / 2

/-- `J(p) = K(p) - Hstar(p)`. -/
def J (p : ℝ) : ℝ := P.K p - P.Hstar p

/-! ### Density -/

/-! ### `sec:iso-parameters` radii -/

def rhoBar : ℝ := (P.rho + P.a) / 2
def r4 : ℝ := Real.sqrt (P.rhoBar / P.rho)
def r3 : ℝ := (1 + P.r4) / 2
def r2 : ℝ := (1 + P.r3) / 2
def r1 : ℝ := (1 + P.r2) / 2

lemma r4_sq : P.r4 ^ 2 = (1 + P.a / P.rho) / 2 := by
  unfold r4
  rw [Real.sq_sqrt (div_nonneg (by unfold rhoBar; linarith [P.rho_pos, P.a_pos]) P.rho_pos.le)]
  unfold rhoBar; field_simp [P.rho_pos.ne']

lemma a_div_rho : P.a / P.rho = (1 - P.ε / 8) / (1 - P.ε / 4) := by
  have := P.s_pos.ne'
  have : 1 - P.ε / 4 ≠ 0 := by linarith [P.hε1]
  unfold a rho t0; field_simp

lemma a_div_rho_lt : P.a / P.rho < 7 / 6 := by
  rw [P.a_div_rho, div_lt_iff₀ (by linarith [P.hε1])]; linarith [P.hε1]

lemma one_lt_r4 : 1 < P.r4 := by
  have h : 1 < P.a / P.rho := by
    rw [one_lt_div P.rho_pos]; exact P.rho_lt_a
  have h4 : 1 < P.r4 ^ 2 := by rw [P.r4_sq]; linarith
  have h0 : 0 ≤ P.r4 := Real.sqrt_nonneg _
  nlinarith

lemma r4_sq_lt : P.r4 ^ 2 < 13 / 12 := by rw [P.r4_sq]; linarith [P.a_div_rho_lt]

/-- **`sec:iso-parameters`**: `1 < r1 < r2 < r3 < r4 < √(13/12) < 3/2`. -/
theorem radii_chain :
    1 < P.r1 ∧ P.r1 < P.r2 ∧ P.r2 < P.r3 ∧ P.r3 < P.r4 ∧
      P.r4 < Real.sqrt (13 / 12) ∧ Real.sqrt (13 / 12) < 3 / 2 := by
  have h1 := P.one_lt_r4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold r1 r2 r3; linarith
  · unfold r1 r2 r3; linarith
  · unfold r2 r3; linarith
  · unfold r3; linarith
  · rw [← Real.sqrt_sq (by linarith : 0 ≤ P.r4)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) P.r4_sq_lt
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

end Params

end SymplecticPacking
