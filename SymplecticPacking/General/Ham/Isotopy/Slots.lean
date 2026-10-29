import SymplecticPacking.General.Ham.Isotopy.Assemble

/-!
# Slot structure of the common isotopy

On each time slot the isotopy has a simple form: a translation (route slots `0 … 4`), an affine
symplectic map (slot `5`), a far centre plus the relative shape (slot `6`), a tail (slot `7`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Problem
open scoped ContDiff

variable {n k : ℕ} {f : Fin k → E n → E n} {s : Fin k → E n} {r1 r2 r3 r4 ρ : Fin k → ℝ}

/-- Positions on the route at time `t`. -/
def pos (f : Fin k → E n → E n) (s : Fin k → E n) (r3 : Fin k → ℝ) (t : ℝ) (i : Fin k) : E n :=
  routePos s (farC f r3) (routeConst s (farC f r3) r3) (routeClocks t) i

lemma after_route {t : ℝ} (h : 5 ≤ slot t) : ∀ l : Fin 5, clk l t = 1 :=
  fun l => clk_eq_one_of_lt (by have := l.isLt; omega)

lemma isoF_route' {t : ℝ} (h : slot t ≤ 4) (i : Fin k) (u : E n) :
    isoF f s r3 i t u = pos f s r3 t i + u :=
  isoF_route i (clk_eq_zero_of_gt (by omega) (by omega)) (clk_eq_zero_of_gt (by omega) (by omega))
    (clk_eq_zero_of_gt (by omega) le_rfl) u

lemma isoF_linear' {t : ℝ} (h : slot t = 5) (i : Fin k) (u : E n) :
    isoF f s r3 i t u = farC f r3 i + linPath f i (clk 5 t) u :=
  isoF_linear i (after_route (by omega)) (clk_eq_zero_of_gt (by omega) (by omega))
    (clk_eq_zero_of_gt (by omega) le_rfl) u

lemma isoF_shape' (hf : IsoInput f s r1 r2 r3 r4 ρ) {t : ℝ} (h : slot t = 6) (i : Fin k)
    (u : E n) : isoF f s r3 i t u = farC f r3 i + shape (f i) (tau f r3 * clk 6 t) u :=
  isoF_shape hf i (after_route (by omega)) (clk_eq_one_of_lt (by omega))
    (clk_eq_zero_of_gt (by omega) le_rfl) u

lemma isoF_tail' (hf : IsoInput f s r1 r2 r3 r4 ρ) {t : ℝ} (h : slot t = 7) (i : Fin k)
    {u : E n} (hu : u ∈ ball (0 : E n) (r4 i)) :
    isoF f s r3 i t u = tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 t) u :=
  isoF_tail hf i (after_route (by omega)) (clk_eq_one_of_lt (by omega))
    (clk_eq_one_of_lt (by omega)) hu

lemma slot_cases (t : ℝ) : slot t ≤ 4 ∨ slot t = 5 ∨ slot t = 6 ∨ slot t = 7 := by
  have := slot_le t; omega

/-- The tail parameter lies in `[τ, 1]`. -/
lemma tailParam_mem (t : ℝ) :
    tau f r3 + (1 - tau f r3) * clk 7 t ∈ Icc (tau f r3) 1 := by
  have hc := clk_mem 7 t
  have hτ : tau f r3 ≤ 1 / 2 := tau_le_half
  constructor <;> nlinarith [hc.1, hc.2]

lemma IsoInput.shapeParam_mem (hf : IsoInput f s r1 r2 r3 r4 ρ) (t : ℝ) :
    tau f r3 * clk 6 t ∈ Icc (0 : ℝ) (1 / 2) := by
  have hc := clk_mem 6 t
  have hτ : tau f r3 ≤ 1 / 2 := tau_le_half
  have hτ0 := hf.tau_pos
  constructor <;> nlinarith [hc.1, hc.2]

/-- Route positions keep the balls `B̄(r₃ᵢ)` apart. -/
lemma IsoInput.pos_sep (hf : IsoInput f s r1 r2 r3 r4 ρ) {t : ℝ} (h : slot t ≤ 4) {i j : Fin k}
    (hij : i ≠ j) : r3 i + r3 j < dist (pos f s r3 t i) (pos f s r3 t j) := by
  have hL := hf.one_le_L
  have hr := hf.rsum_pos
  refine route_sep (by have := hf.one_le_n; omega) (fun a => (hf.r3_pos a).le) hf.sep
    (fun a b hab => ?_) (routeClocks_valid h) hij
  have h1 := hf.farC_sep hab
  have h2 := hf.r3_add_r3_lt hab
  nlinarith

end SymplecticPacking.General.Ham.Isotopy
