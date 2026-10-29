import SymplecticPacking.General.Ham.Isotopy.Route

/-!
# The common isotopy as one closed formula

Eight time slots of length `1/8`, run by the flat clocks `clk m t = S(8t - m)`: route phases
`0 … 4`, linear slot `5`, shape slot `6`, tail slot `7`. The formula telescopes: on slot `m` all
earlier clocks are `1` and all later ones `0`.

  `F_{i,t}(u) = pᵢ(clk₀ … clk₄) + u + (M_{i,clk₅} u - u) + (κ_{i, τ clk₆}(u) - Aᵢ u)
               + (fᵢ(v u)/v |_{v = τ + (1-τ) clk₇} - fᵢ(τ u)/τ)`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Problem
open scoped ContDiff

variable {n k : ℕ}

/-- The flat clock of slot `m`. -/
def clk (m : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (8 * t - m)

/-- The route clock values at time `t`. -/
def routeClocks (t : ℝ) : Fin 5 → ℝ := fun l => clk l t

/-- The tail map `v⁻¹ fᵢ(v u)`. -/
def tailMap (f : Fin k → E n → E n) (i : Fin k) (v : ℝ) (u : E n) : E n := v⁻¹ • f i (v • u)

/-- **The common isotopy.** -/
def isoF (f : Fin k → E n → E n) (s : Fin k → E n) (r3 : Fin k → ℝ) (i : Fin k) (t : ℝ)
    (u : E n) : E n :=
  routePos s (farC f r3) (routeConst s (farC f r3) r3) (routeClocks t) i + u
    + (linPath f i (clk 5 t) u - u)
    + (shape (f i) (tau f r3 * clk 6 t) u - lin f i u)
    + (tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 t) u - tailMap f i (tau f r3) u)

/-! ### Clocks -/

lemma clk_mem (m : ℕ) (t : ℝ) : clk m t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clk_eq_zero {m : ℕ} {t : ℝ} (h : 8 * t ≤ m) : clk m t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma clk_eq_one {m : ℕ} {t : ℝ} (h : (m : ℝ) + 1 ≤ 8 * t) : clk m t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma contDiff_clk (m : ℕ) : ContDiff ℝ ∞ (clk m) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The time slot of `t` (clamped to `0 … 7`). -/
def slot (t : ℝ) : ℕ := min (⌊(8 : ℝ) * t⌋₊) 7

lemma slot_le (t : ℝ) : slot t ≤ 7 := min_le_right _ _

/-- Earlier clocks have run out. -/
lemma clk_eq_one_of_lt {m : ℕ} {t : ℝ} (hm : m < slot t) : clk m t = 1 := by
  apply clk_eq_one
  have h1 : m + 1 ≤ ⌊(8 : ℝ) * t⌋₊ := (Nat.succ_le_of_lt hm).trans (min_le_left _ _)
  have h2 : ((m + 1 : ℕ) : ℝ) ≤ (8 : ℝ) * t := by
    have hpos : 0 < ⌊(8 : ℝ) * t⌋₊ := lt_of_lt_of_le (Nat.succ_pos m) h1
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by
      by_contra hneg; push Not at hneg
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hpos; exact lt_irrefl 0 hpos))
  push_cast at h2; linarith

/-- Later clocks have not started. -/
lemma clk_eq_zero_of_gt {m : ℕ} {t : ℝ} (hm : slot t < m) (hm7 : m ≤ 7) : clk m t = 0 := by
  apply clk_eq_zero
  have hslot : slot t = ⌊(8 : ℝ) * t⌋₊ := by
    unfold slot; rw [min_eq_left]; by_contra h; push Not at h
    have := min_eq_right h.le; unfold slot at hm; rw [this] at hm; omega
  rw [hslot] at hm
  rcases le_or_gt 0 ((8 : ℝ) * t) with h0 | h0
  · have := Nat.lt_floor_add_one ((8 : ℝ) * t)
    have : ((⌊(8 : ℝ) * t⌋₊ : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast hm
    linarith
  · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith

lemma clk_of_nonpos {m : ℕ} {t : ℝ} (ht : t ≤ 0) : clk m t = 0 :=
  clk_eq_zero (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)

lemma clk_of_one_le {m : ℕ} (hm : m ≤ 7) {t : ℝ} (ht : 1 ≤ t) : clk m t = 1 :=
  clk_eq_one (by
    have : (m : ℝ) ≤ 7 := by exact_mod_cast hm
    linarith)

/-- The route clocks form a valid clock tuple while `slot t ≤ 4`. -/
lemma routeClocks_valid {t : ℝ} (h : slot t ≤ 4) : RouteClocks (routeClocks t) :=
  ⟨⟨slot t, by omega⟩, fun l hl => clk_eq_one_of_lt (by simpa [Fin.lt_def] using hl),
    fun l hl => clk_eq_zero_of_gt (by simpa [Fin.lt_def] using hl) (by omega), clk_mem _ _⟩

/-! ### Stage evaluation -/

variable {f : Fin k → E n → E n} {s : Fin k → E n} {r1 r2 r3 r4 ρ : Fin k → ℝ}

lemma tailMap_tau_sub (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {u : E n}
    (hu : u ∈ ball (0 : E n) (r4 i)) :
    tailMap f i (tau f r3) u - shape (f i) (tau f r3) u = farC f r3 i := by
  have hτ := hf.tau_pos
  obtain ⟨-, -, -, -, h45⟩ := hf.radii i
  have hτu : tau f r3 • u ∈ ball (0 : E n) (ρ i) := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hτ.le]
    have := mem_ball_zero_iff.mp hu
    have h12 : tau f r3 ≤ 1 := tau_le_half.trans (by norm_num)
    calc tau f r3 * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
      _ < ρ i := by linarith
  rw [shape_eq (hf.smooth i) hτ.ne' hτu, tailMap, farC, cen, smul_sub]
  abel

/-- Route slots (`0 … 4`). -/
lemma isoF_route (i : Fin k) {t : ℝ} (h5 : clk 5 t = 0) (h6 : clk 6 t = 0) (h7 : clk 7 t = 0)
    (u : E n) :
    isoF f s r3 i t u =
      routePos s (farC f r3) (routeConst s (farC f r3) r3) (routeClocks t) i + u := by
  rw [isoF, h5, h6, h7, linPath_zero, mul_zero, shape_zero, mul_zero, add_zero]
  simp [lin]

/-- After the route, the ball sits at its far centre. -/
lemma routePos_arrived (i : Fin k) {t : ℝ} (h : ∀ l : Fin 5, clk l t = 1) :
    routePos s (farC f r3) (routeConst s (farC f r3) r3) (routeClocks t) i = farC f r3 i := by
  have : routeClocks t = fun _ => 1 := funext h
  rw [this, routePos_one]

/-- Linear slot. -/
lemma isoF_linear (i : Fin k) {t : ℝ} (h : ∀ l : Fin 5, clk l t = 1) (h6 : clk 6 t = 0)
    (h7 : clk 7 t = 0) (u : E n) :
    isoF f s r3 i t u = farC f r3 i + linPath f i (clk 5 t) u := by
  rw [isoF, routePos_arrived i h, h6, h7, mul_zero, shape_zero, mul_zero, add_zero]
  simp [lin]

/-- Shape slot. -/
lemma isoF_shape (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {t : ℝ}
    (h : ∀ l : Fin 5, clk l t = 1) (h5 : clk 5 t = 1) (h7 : clk 7 t = 0) (u : E n) :
    isoF f s r3 i t u = farC f r3 i + shape (f i) (tau f r3 * clk 6 t) u := by
  rw [isoF, routePos_arrived i h, h5, hf.linPath_one, h7, mul_zero, add_zero]
  simp only [sub_self, add_zero]
  abel

/-- Tail slot (on `B(r₄ᵢ)`). -/
lemma isoF_tail (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {t : ℝ}
    (h : ∀ l : Fin 5, clk l t = 1) (h5 : clk 5 t = 1) (h6 : clk 6 t = 1) {u : E n}
    (hu : u ∈ ball (0 : E n) (r4 i)) :
    isoF f s r3 i t u = tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 t) u := by
  rw [isoF, routePos_arrived i h, h5, hf.linPath_one, h6, mul_one]
  have := tailMap_tau_sub hf i hu
  rw [← this]
  abel

end SymplecticPacking.General.Ham.Isotopy
