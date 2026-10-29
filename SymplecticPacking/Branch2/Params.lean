import Mathlib

/-!
# Branch n = 2: auxiliary capacities and the area profile (`lem:cub-auxiliary`)

Normalised input: `k ≥ 1`, capacities `0 < ρ_i < 1/3` with `Σ ρ_i² < 1` (target capacity `1`).
All parameters are explicit real formulas in `ρ` (paper `lem:cub-auxiliary`):

`A₀ = Σ ρ_i`, `D = 1 - Σ ρ_i²`, `m₀ = 1/3 - max ρ_i`,
`δ = min(m₀/8, D/(8(A₀+k)), 1/8)`, `a_i = ρ_i + δ`, `D_a = 1 - Σ a_i²`,
`ζ = min((1/3 - a_max)/2, D_a/12)`, `h = 1/3 - ζ`, `τ = (a_max + h)/(2h)`,
`P_b(p) = 3(1 - 3p) - Σ (a_i - p)_+`, `γ = 3(1 - 3h)`, `μ = (1 - Σ a_i² - (1-3h)²)/(2h)`
(the mean of `P_b` on `[0,h]`), `d = min(μ, γ)/2`, `d_n = (h + 1/3)/2`.

The paper chooses rational `ρ'_i` first (needed only for the finite polyhedral form of the
comparator, i.e. for L2/L3); at level L1 the real formulas are used directly.
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Finset

variable {k : ℕ} (ρ : Fin k → ℝ)

/-- `max_i ρ_i` (`0` for `k = 0`). -/
def rhoMax : ℝ := ⨆ i, ρ i

/-- `A₀ = Σ ρ_i`. -/
def sumRho : ℝ := ∑ i, ρ i

/-- `D = 1 - Σ ρ_i²`. -/
def volDefect : ℝ := 1 - ∑ i, ρ i ^ 2

/-- `δ = min(m₀/8, D/(8(A₀+k)), 1/8)`, `m₀ = 1/3 - max ρ_i`. -/
def delta : ℝ := min (min ((1 / 3 - rhoMax ρ) / 8) (volDefect ρ / (8 * (sumRho ρ + k)))) (1 / 8)

/-- Auxiliary capacities `a_i = ρ_i + δ`. -/
def aux (i : Fin k) : ℝ := ρ i + delta ρ

/-- `a_max = max ρ_i + δ`. -/
def auxMax : ℝ := rhoMax ρ + delta ρ

/-- `D_a = 1 - Σ a_i²`. -/
def auxDefect : ℝ := 1 - ∑ i, aux ρ i ^ 2

/-- `ζ = min((1/3 - a_max)/2, D_a/12)`. -/
def zeta : ℝ := min ((1 / 3 - auxMax ρ) / 2) (auxDefect ρ / 12)

/-- The fibre height `h = 1/3 - ζ`. -/
def height : ℝ := 1 / 3 - zeta ρ

/-- The core fraction `τ = (a_max + h)/(2h)`. -/
def tau : ℝ := (auxMax ρ + height ρ) / (2 * height ρ)

/-- The base area profile of the cubic model, `H_b(p) = 3(1 - 3p)`. -/
def Hb (p : ℝ) : ℝ := 3 * (1 - 3 * p)

/-- The unused area `P_b(p) = H_b(p) - Σ_i (a_i - p)_+`. -/
def Pb (p : ℝ) : ℝ := Hb p - ∑ i, max (aux ρ i - p) 0

/-- The outer bound `γ = 3(1 - 3h)`. -/
def gammaOut : ℝ := 3 * (1 - 3 * height ρ)

/-- The mean of `P_b` on `[0, h]`: `μ = (1 - Σ a_i² - (1-3h)²)/(2h)`. -/
def meanP : ℝ := (1 - ∑ i, aux ρ i ^ 2 - (1 - 3 * height ρ) ^ 2) / (2 * height ρ)

/-- The comparator gap parameter `d = min(μ, γ)/2`. -/
def dGap : ℝ := min (meanP ρ) (gammaOut ρ) / 2

/-- `d_n = (h + 1/3)/2`, the radius of the transfer domain. -/
def dn : ℝ := (height ρ + 1 / 3) / 2

/-- `∫_x^y (α + β p + γ p²) dp` by the fundamental theorem of calculus. -/
lemma integral_quadratic (α β γ x y : ℝ) :
    ∫ p in x..y, (α + β * p + γ * p ^ 2) =
      (α * y + β / 2 * y ^ 2 + γ / 3 * y ^ 3) - (α * x + β / 2 * x ^ 2 + γ / 3 * x ^ 3) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun p =>
    α * p + β / 2 * p ^ 2 + γ / 3 * p ^ 3)
  · intro t _
    have := (((hasDerivAt_id t).const_mul α).add ((hasDerivAt_pow 2 t).const_mul (β / 2))).add
      ((hasDerivAt_pow 3 t).const_mul (γ / 3))
    convert this using 1
    · funext p; simp only [Pi.add_apply, id]
    · norm_num; ring
  · exact (by fun_prop : Continuous fun p : ℝ => α + β * p + γ * p ^ 2).intervalIntegrable _ _

/-- `∫_0^h (a - p)_+ dp = a²/2` for `0 ≤ a ≤ h`. -/
lemma integral_cap {a h : ℝ} (ha : 0 < a) (hah : a < h) :
    ∫ p in (0 : ℝ)..h, max (a - p) 0 = a ^ 2 / 2 := by
  have hc : Continuous fun p : ℝ => max (a - p) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ p in (0 : ℝ)..a, max (a - p) 0 =
      ∫ p in (0 : ℝ)..a, (a + -1 * p + 0 * p ^ 2) := by
    apply intervalIntegral.integral_congr
    intro p hp
    rw [Set.uIcc_of_le ha.le] at hp
    simp only
    rw [max_eq_left (by linarith [hp.2])]; ring
  have h2 : ∫ p in a..h, max (a - p) 0 = ∫ p in a..h, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro p hp
    rw [Set.uIcc_of_le hah.le] at hp
    exact max_eq_right (by linarith [hp.1])
  rw [h1, h2, intervalIntegral.integral_zero, add_zero,
    integral_quadratic a (-1) 0 0 a]
  ring

/-- Hypotheses on the normalised input. -/
structure Hyp (ρ : Fin k → ℝ) : Prop where
  one_le : 1 ≤ k
  pos : ∀ i, 0 < ρ i
  third : ∀ i, ρ i < 1 / 3
  vol : ∑ i, ρ i ^ 2 < 1

namespace Hyp

variable {ρ}
variable (H : Hyp ρ)
include H

lemma nonempty : Nonempty (Fin k) := ⟨⟨0, H.one_le⟩⟩

lemma bddAbove : BddAbove (Set.range ρ) := (Set.finite_range ρ).bddAbove

lemma le_rhoMax (i : Fin k) : ρ i ≤ rhoMax ρ := le_ciSup H.bddAbove i

lemma rhoMax_lt : rhoMax ρ < 1 / 3 := by
  have := H.nonempty
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := ρ)
  unfold rhoMax; rw [← hi]; exact H.third i

lemma rhoMax_pos : 0 < rhoMax ρ := (H.pos ⟨0, H.one_le⟩).trans_le (H.le_rhoMax _)

lemma sumRho_nonneg : 0 ≤ sumRho ρ := Finset.sum_nonneg fun i _ => (H.pos i).le

lemma volDefect_pos : 0 < volDefect ρ := by unfold volDefect; linarith [H.vol]

lemma delta_pos : 0 < delta ρ := by
  have h1 : 0 < (1 / 3 - rhoMax ρ) / 8 := by linarith [H.rhoMax_lt]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast H.one_le
  have h2 : 0 < volDefect ρ / (8 * (sumRho ρ + k)) :=
    div_pos H.volDefect_pos (by linarith [H.sumRho_nonneg])
  unfold delta
  exact lt_min (lt_min h1 h2) (by norm_num)

lemma delta_le_one_eighth : delta ρ ≤ 1 / 8 := min_le_right _ _

lemma delta_le_m0 : delta ρ ≤ (1 / 3 - rhoMax ρ) / 8 :=
  (min_le_left _ _).trans (min_le_left _ _)

lemma delta_le_D : delta ρ ≤ volDefect ρ / (8 * (sumRho ρ + k)) :=
  (min_le_left _ _).trans (min_le_right _ _)

lemma rho_lt_aux (i : Fin k) : ρ i < aux ρ i := by unfold aux; linarith [H.delta_pos]

lemma aux_pos (i : Fin k) : 0 < aux ρ i := (H.pos i).trans (H.rho_lt_aux i)

lemma aux_le_auxMax (i : Fin k) : aux ρ i ≤ auxMax ρ := by
  unfold aux auxMax; linarith [H.le_rhoMax i]

lemma auxMax_lt : auxMax ρ < 1 / 3 := by
  unfold auxMax; linarith [H.delta_le_m0, H.rhoMax_lt]

lemma auxMax_pos : 0 < auxMax ρ := by unfold auxMax; linarith [H.rhoMax_pos, H.delta_pos]

/-- `Σ a_i² - Σ ρ_i² ≤ D/4`. -/
lemma sum_aux_sq_le : ∑ i, aux ρ i ^ 2 ≤ ∑ i, ρ i ^ 2 + volDefect ρ / 4 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast H.one_le
  have hd := H.delta_pos
  have hd8 := H.delta_le_one_eighth
  have hS := H.sumRho_nonneg
  have hexp : ∑ i, aux ρ i ^ 2 = ∑ i, ρ i ^ 2 + 2 * delta ρ * sumRho ρ + k * delta ρ ^ 2 := by
    unfold aux sumRho
    simp only [add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hexp]
  have hpos : 0 < 8 * (sumRho ρ + k) := by linarith
  have hD := H.delta_le_D
  rw [le_div_iff₀ hpos] at hD
  nlinarith [mul_le_mul_of_nonneg_left hd8 (by positivity : (0 : ℝ) ≤ k * delta ρ)]

lemma auxDefect_pos : 0 < auxDefect ρ := by
  have := H.sum_aux_sq_le
  have h0 := H.volDefect_pos
  unfold auxDefect; unfold volDefect at this h0; linarith

lemma auxDefect_le_one : auxDefect ρ ≤ 1 := by
  unfold auxDefect; linarith [Finset.sum_nonneg fun i (_ : i ∈ univ) => sq_nonneg (aux ρ i)]

lemma zeta_pos : 0 < zeta ρ :=
  lt_min (by linarith [H.auxMax_lt]) (by linarith [H.auxDefect_pos])

lemma zeta_le_left : zeta ρ ≤ (1 / 3 - auxMax ρ) / 2 := min_le_left _ _

lemma zeta_le_right : zeta ρ ≤ auxDefect ρ / 12 := min_le_right _ _

lemma height_lt_third : height ρ < 1 / 3 := by unfold height; linarith [H.zeta_pos]

lemma auxMax_lt_height : auxMax ρ < height ρ := by
  unfold height; linarith [H.zeta_le_left, H.auxMax_lt]

lemma height_pos : 0 < height ρ := H.auxMax_pos.trans H.auxMax_lt_height

lemma aux_lt_height (i : Fin k) : aux ρ i < height ρ :=
  (H.aux_le_auxMax i).trans_lt H.auxMax_lt_height

lemma tau_mul_height : tau ρ * height ρ = (auxMax ρ + height ρ) / 2 := by
  have := H.height_pos.ne'; unfold tau; field_simp

lemma auxMax_lt_tau_mul : auxMax ρ < tau ρ * height ρ := by
  rw [H.tau_mul_height]; linarith [H.auxMax_lt_height]

lemma tau_mul_lt_height : tau ρ * height ρ < height ρ := by
  rw [H.tau_mul_height]; linarith [H.auxMax_lt_height]

lemma tau_pos : 0 < tau ρ := div_pos (by linarith [H.auxMax_pos, H.height_pos])
  (by linarith [H.height_pos])

lemma tau_lt_one : tau ρ < 1 := by
  have := H.tau_mul_lt_height
  have hh := H.height_pos
  nlinarith

/-- **(ii)** `Σ a_i² + (1 - 3h)² < 1`. -/
lemma sum_aux_sq_add_lt : ∑ i, aux ρ i ^ 2 + (1 - 3 * height ρ) ^ 2 < 1 := by
  have hz : 1 - 3 * height ρ = 3 * zeta ρ := by unfold height; ring
  rw [hz]
  have h1 := H.zeta_le_right
  have h2 := H.zeta_pos
  have h3 := H.auxDefect_pos
  have h4 := H.auxDefect_le_one
  have : (3 * zeta ρ) ^ 2 < auxDefect ρ := by nlinarith
  unfold auxDefect at this; linarith

lemma gammaOut_pos : 0 < gammaOut ρ := by unfold gammaOut; linarith [H.height_lt_third]

lemma meanP_pos : 0 < meanP ρ :=
  div_pos (by linarith [H.sum_aux_sq_add_lt]) (by linarith [H.height_pos])

lemma dGap_pos : 0 < dGap ρ := by
  unfold dGap; exact half_pos (lt_min H.meanP_pos H.gammaOut_pos)

lemma dGap_lt_meanP : dGap ρ < meanP ρ := by
  have h1 := min_le_left (meanP ρ) (gammaOut ρ)
  have h2 := lt_min H.meanP_pos H.gammaOut_pos
  unfold dGap; linarith

lemma dGap_lt_gammaOut : dGap ρ < gammaOut ρ := by
  unfold dGap; linarith [min_le_right (meanP ρ) (gammaOut ρ), H.dGap_pos, H.meanP_pos,
    lt_min H.meanP_pos H.gammaOut_pos]

lemma height_lt_dn : height ρ < dn ρ := by unfold dn; linarith [H.height_lt_third]

lemma dn_lt_third : dn ρ < 1 / 3 := by unfold dn; linarith [H.height_lt_third]

/-- **(iv)** On the outer part `[τh, h]` all caps vanish: `P_b = H_b ≥ γ > 0`. -/
lemma Pb_outer {p : ℝ} (hp : tau ρ * height ρ ≤ p) (hph : p ≤ height ρ) :
    Pb ρ p = Hb p ∧ gammaOut ρ ≤ Pb ρ p := by
  have hcap : ∀ i, max (aux ρ i - p) 0 = 0 := fun i =>
    max_eq_right (by linarith [H.aux_le_auxMax i, H.auxMax_lt_tau_mul])
  have hP : Pb ρ p = Hb p := by simp [Pb, hcap]
  refine ⟨hP, ?_⟩
  rw [hP]; unfold Hb gammaOut; linarith

/-- A cap `p ↦ (a - p)_+` is convex. -/
lemma cap_convex (a : ℝ) : ConvexOn ℝ Set.univ (fun p : ℝ => max (a - p) 0) := by
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ => a - p) :=
    ⟨convex_univ, fun x _ y _ s t _ _ hst => by
      simp only [smul_eq_mul]
      have : a = (s + t) * a := by rw [hst, one_mul]
      nlinarith⟩
  exact hlin.sup (convexOn_const 0 convex_univ)

/-- `P_b` is concave on `ℝ`. -/
lemma Pb_concave : ConcaveOn ℝ Set.univ (Pb ρ) := by
  have hH : ConcaveOn ℝ Set.univ Hb :=
    ⟨convex_univ, fun x _ y _ s t _ _ hst => by
      simp only [Hb, smul_eq_mul]
      have : (3 : ℝ) = (s + t) * 3 := by rw [hst, one_mul]
      nlinarith⟩
  have hsum : ConvexOn ℝ Set.univ (fun p => ∑ i, max (aux ρ i - p) 0) := by
    have := Finset.sum_induction (fun i => fun p : ℝ => max (aux ρ i - p) 0)
      (fun f : ℝ → ℝ => ConvexOn ℝ Set.univ f) (fun f g hf hg => hf.add hg)
      (convexOn_const 0 convex_univ) (fun i _ => H.cap_convex (aux ρ i)) (s := Finset.univ)
    convert this using 1
    funext p; simp [Finset.sum_apply]
  exact hH.sub hsum

/-- `P_b` is continuous. -/
lemma Pb_continuous : Continuous (Pb ρ) := by
  unfold Pb Hb; fun_prop

/-- **(iii)** `∫_0^h P_b = (1 - Σ a_i² - (1-3h)²)/2 = h μ > 0`. -/
lemma integral_Pb : ∫ p in (0 : ℝ)..height ρ, Pb ρ p =
    (1 - ∑ i, aux ρ i ^ 2 - (1 - 3 * height ρ) ^ 2) / 2 := by
  have hcapI : ∀ i, ∫ p in (0 : ℝ)..height ρ, max (aux ρ i - p) 0 = aux ρ i ^ 2 / 2 :=
    fun i => integral_cap (H.aux_pos i) (H.aux_lt_height i)
  have hint : ∀ i, IntervalIntegrable (fun p : ℝ => max (aux ρ i - p) 0) MeasureTheory.volume
      0 (height ρ) := fun i => (by fun_prop : Continuous fun p : ℝ => max (aux ρ i - p) 0)
        |>.intervalIntegrable _ _
  unfold Pb Hb
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun p : ℝ => 3 * (1 - 3 * p)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun p : ℝ => ∑ i, max (aux ρ i - p) 0).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  simp only [hcapI]
  rw [← Finset.sum_div]
  have : ∫ p in (0 : ℝ)..height ρ, 3 * (1 - 3 * p) = 3 * height ρ - 9 / 2 * height ρ ^ 2 := by
    have e := integral_quadratic 3 (-9) 0 0 (height ρ)
    rw [show (fun p : ℝ => 3 * (1 - 3 * p)) = fun p => 3 + -9 * p + 0 * p ^ 2 by
      funext p; ring] 
    rw [e]; ring
  rw [this]; ring

end Hyp

end SymplecticPacking.Branch2
