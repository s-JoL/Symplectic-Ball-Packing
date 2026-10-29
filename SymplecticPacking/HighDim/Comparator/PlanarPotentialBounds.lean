import SymplecticPacking.HighDim.Comparator.PlanarLSEBounds
import SymplecticPacking.Branch2.Planar.UVWells

/-!
# The genuine critical point and angular well of the planar family

The scalar potential API is instantiated with its own smooth convex log-sum-exp
profile. This uses the already proved exponential-moment bounds and does not
assume any Morse inverse or endpoint comparison properties.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)

/-- An auxiliary scalar input for the same proper potential; its profile is `U₀` itself. -/
def scalarInput : Branch2.Planar.PlanarInput where
  h := 1
  e := D.xi
  L := D.L
  F := D.U0 y
  U0 := D.U0 y
  sig := 0

theorem U0_convex (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) : ConvexOn ℝ univ (D.U0 y) := by
  have hs := D.U0_smooth y hne
  apply convexOn_univ_of_deriv2_nonneg (hs.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp))
  intro v
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    (D.U0_second_bounds y hξ hL hne hb v).1

theorem scalarInput_hyp (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) : (D.scalarInput y).Hyp where
  h_pos := by norm_num [scalarInput]
  e_pos := hξ
  L_nonneg := hL
  F_cont := (D.U0_smooth y hne).continuous.continuousOn
  F_convex := (D.U0_convex y hξ hL hne hb).subset (subset_univ _) (convex_Icc _ _)
  F_lip := by
    intro a ha b hb'
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun v _ => (D.U0_smooth y hne).differentiable (by simp) v)
      (fun v _ => by simpa only [Real.norm_eq_abs] using D.U0_deriv_abs_le y hξ hL hne hb v)
      hb' ha
    simpa only [Real.norm_eq_abs, scalarInput] using h
  U0_smooth := D.U0_smooth y hne
  U0_convex := D.U0_convex y hξ hL hne hb
  U0_ge := fun _ _ => le_rfl
  U0_le := fun _ _ => by simp [scalarInput]
  sig_nonneg := le_rfl
  sig_le := by change 0 ≤ D.xi / 16; positivity

theorem scalarInput_U : (D.scalarInput y).U = D.U y := by
  funext v
  simp [scalarInput, Branch2.Planar.PlanarInput.U, Branch2.Planar.PlanarInput.kappa,
    Branch2.Planar.PlanarInput.sigma, Branch2.Planar.PlanarInput.eta, U, kappa, sig, eta]

theorem scalarInput_V : (D.scalarInput y).V = D.V := by
  funext θ
  simp [scalarInput, Branch2.Planar.PlanarInput.V, Branch2.Planar.PlanarInput.nu,
    Branch2.Planar.PlanarInput.sigma, Branch2.Planar.PlanarInput.betaY,
    Branch2.Planar.PlanarInput.eta, V, nu, sig, beta, eta]

theorem scalarInput_pstar : (D.scalarInput y).pstar = D.vstar y := by
  unfold Branch2.Planar.PlanarInput.pstar vstar
  rw [scalarInput_U]
  rfl

theorem exists_unique_critical (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) :
    ∃! v, v ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) v = 0 := by
  have h := Branch2.Planar.PlanarInput.exists_unique_crit (D.scalarInput_hyp y hξ hL hne hb)
  change ∃! v, v ∈ Ioo (0 : ℝ) 1 ∧ deriv ((D.scalarInput y).U) v = 0 at h
  rwa [scalarInput_U] at h

theorem vstar_spec (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) :
    D.vstar y ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) (D.vstar y) = 0 := by
  have h := D.exists_unique_critical y hξ hL hne hb
  unfold vstar
  rw [dif_pos h]
  exact Explicit.the_spec h

theorem vstar_minimum (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    D.U y (D.vstar y) ≤ D.U y v := by
  have h := Branch2.Planar.PlanarInput.pstar_isMin (D.scalarInput_hyp y hξ hL hne hb) hv
  simpa only [scalarInput_U, scalarInput_pstar] using h

theorem wellV_hyp (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) : D.wellV.Hyp := by
  have h := Branch2.Planar.PlanarInput.wellV_hyp (D.scalarInput_hyp y hξ hL hne hb)
  have heq : (D.scalarInput y).wellV = D.wellV := by
    unfold Branch2.Planar.PlanarInput.wellV wellV
    rw [scalarInput_V]
    rfl
  rwa [heq] at h

theorem deriv_U_formula (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (D.U y) v = deriv (D.U0 y) v +
      D.kappa * (-(v ^ 2)⁻¹ + ((1 - v) ^ 2)⁻¹) := by
  have h := (Branch2.Planar.PlanarInput.hasDerivAt_U (D.scalarInput_hyp y hξ hL hne hb) hv).deriv
  rw [scalarInput_U] at h
  exact h

theorem r0_square_bound (hξ : 0 < D.xi) (hL : 0 ≤ D.L) :
    4 * (D.L + 2 * D.kappa + 1) * D.r0 ^ 2 ≤ D.kappa := by
  have hk := kappa_pos hξ hL
  have hd : 0 < 4 * (D.L + 2 * D.kappa + 1) := by positivity
  have hq : 0 ≤ D.kappa / (4 * (D.L + 2 * D.kappa + 1)) := (div_pos hk hd).le
  have hr := (Real.le_sqrt (r0_pos hξ hL).le hq).mp (min_le_right _ _ : D.r0 ≤ _)
  have h := (le_div_iff₀ hd).mp hr
  nlinarith

private theorem critical_left_bound {κ L r a p : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (hr : 0 ≤ r) (hr8 : r ≤ 1 / 8) (hrsq : 4 * (L + 2 * κ + 1) * r ^ 2 ≤ κ)
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : |a| ≤ L)
    (hc : a + κ * (-(p ^ 2)⁻¹ + ((1 - p) ^ 2)⁻¹) = 0) : r ≤ p := by
  by_contra hn
  have hpr : p < r := not_le.mp hn
  have hp8 : p < 1 / 8 := hpr.trans_le hr8
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp.1
  have hback : κ / (1 - p) ^ 2 ≤ 2 * κ := by
    rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - p))]
    have hs : (1 / 2 : ℝ) ≤ (1 - p) ^ 2 := by nlinarith [sq_nonneg p]
    nlinarith
  have hc' : a - κ / p ^ 2 + κ / (1 - p) ^ 2 = 0 := by
    simpa only [div_eq_mul_inv, mul_add, mul_neg, sub_eq_add_neg, add_assoc] using hc
  have hbal : κ ≤ (L + 2 * κ) * p ^ 2 := by
    have hdiv : κ / p ^ 2 ≤ L + 2 * κ := by linarith [(abs_le.mp ha).2]
    exact (div_le_iff₀ hp2).mp hdiv
  have hsq : p ^ 2 ≤ r ^ 2 := by nlinarith [hp.1]
  have ht : 0 ≤ 4 * (L + 2 * κ + 1) := by positivity
  have hsmall := (mul_le_mul_of_nonneg_left hsq ht).trans hrsq
  nlinarith [mul_pos (by linarith : 0 < 3 * L + 6 * κ + 4) hp2]

/-- The critical point stays uniformly away from both endpoints. -/
theorem vstar_uniform_bounds (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) :
    D.r0 ≤ D.vstar y ∧ D.vstar y ≤ 1 - D.r0 := by
  have hp := D.vstar_spec y hξ hL hne hb
  have hc := D.deriv_U_formula y hξ hL hne hb hp.1
  rw [hp.2] at hc
  have ha := D.U0_deriv_abs_le y hξ hL hne hb (D.vstar y)
  have hk := kappa_pos hξ hL
  have hr := (r0_pos hξ hL).le
  have hs := D.r0_square_bound hξ hL
  constructor
  · exact critical_left_bound hk hL hr D.r0_le hs hp.1 ha hc.symm
  · have hc' : -deriv (D.U0 y) (D.vstar y) + D.kappa *
        (-((1 - D.vstar y) ^ 2)⁻¹ + ((1 - (1 - D.vstar y)) ^ 2)⁻¹) = 0 := by
      rw [sub_sub_cancel]
      linarith [hc]
    have h := critical_left_bound hk hL hr D.r0_le hs
      (show 1 - D.vstar y ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hp.1.1, hp.1.2])
      (by rwa [abs_neg]) hc'
    linarith

theorem U_second_formula (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (D.U y)) v = deriv (deriv (D.U0 y)) v +
      2 * D.kappa * ((v ^ 3)⁻¹ + ((1 - v) ^ 3)⁻¹) := by
  have he : deriv (D.U y) =ᶠ[𝓝 v] fun t => deriv (D.U0 y) t +
      D.kappa * (-(t ^ 2)⁻¹ + ((1 - t) ^ 2)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    exact D.deriv_U_formula y hξ hL hne hb ht
  rw [he.deriv_eq]
  have h0 := (((contDiff_infty_iff_deriv.mp (D.U0_smooth y hne)).2).differentiable (by simp) v).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2)⁻¹) (2 / v ^ 3) v := by
    have hh := (((hasDerivAt_id v).pow 2).inv (pow_ne_zero 2 hv.1.ne')).neg
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp [hv.1.ne']
      <;> ring
  have h2 : HasDerivAt (fun t : ℝ => ((1 - t) ^ 2)⁻¹) (2 / (1 - v) ^ 3) v := by
    have hh := ((((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).pow 2).inv
      (pow_ne_zero 2 (sub_pos.mpr hv.2).ne'))
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub, mul_neg_one]
      field_simp [(sub_pos.mpr hv.2).ne']
      <;> ring
  have hh : HasDerivAt (fun t => deriv (D.U0 y) t +
      D.kappa * (-(t ^ 2)⁻¹ + ((1 - t) ^ 2)⁻¹))
      (deriv (deriv (D.U0 y)) v + D.kappa * (2 / v ^ 3 + 2 / (1 - v) ^ 3)) v :=
    h0.add ((h1.add h2).const_mul D.kappa)
  convert hh.deriv using 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

private theorem inverse_cubes_lower {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    16 ≤ (v ^ 3)⁻¹ + ((1 - v) ^ 3)⁻¹ := by
  let a := 1 / v
  let b := 1 / (1 - v)
  have ha : 0 < a := div_pos one_pos hv.1
  have hb : 0 < b := div_pos one_pos (sub_pos.mpr hv.2)
  have hprod : 0 < v * (1 - v) := mul_pos hv.1 (sub_pos.mpr hv.2)
  have hs : 4 ≤ a + b := by
    have he : a + b = 1 / (v * (1 - v)) := by dsimp [a, b]; field_simp [hv.1.ne', (sub_pos.mpr hv.2).ne']; ring
    rw [he, le_div_iff₀ hprod]
    nlinarith [sq_nonneg (2 * v - 1)]
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hs 3
  have hvar := mul_nonneg (sq_nonneg (a - b)) (add_pos ha hb).le
  have hbound : 16 ≤ a ^ 3 + b ^ 3 := by nlinarith
  simpa only [a, b, one_div, inv_pow] using hbound

theorem U_second_lower (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    D.alphaMin ≤ deriv (deriv (D.U y)) v := by
  rw [D.U_second_formula y hξ hL hne hb hv]
  have h0 := (D.U0_second_bounds y hξ hL hne hb v).1
  have h1 := mul_le_mul_of_nonneg_left (inverse_cubes_lower hv) (by
    have := kappa_pos hξ hL; positivity : 0 ≤ 2 * D.kappa)
  unfold alphaMin
  linarith

theorem alphaU_bounds (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) :
    D.alphaMin ≤ D.alphaU y ∧ D.alphaU y ≤ D.alphaMax := by
  have hp := D.vstar_spec y hξ hL hne hb
  have hr := D.vstar_uniform_bounds y hξ hL hne hb
  refine ⟨D.U_second_lower y hξ hL hne hb hp.1, ?_⟩
  unfold alphaU
  rw [D.U_second_formula y hξ hL hne hb hp.1]
  have hu := (D.U0_second_bounds y hξ hL hne hb (D.vstar y)).2
  have hr0 := r0_pos hξ hL
  have h1 := one_div_le_one_div_of_le (pow_pos hr0 3)
    (pow_le_pow_left₀ hr0.le hr.1 3)
  have h2 := one_div_le_one_div_of_le (pow_pos hr0 3)
    (pow_le_pow_left₀ hr0.le (by linarith [hr.2] : D.r0 ≤ 1 - D.vstar y) 3)
  have hk := kappa_pos hξ hL
  have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ 2 * D.kappa)
  simp only [one_div] at hmul
  unfold alphaMax
  rw [div_eq_mul_inv]
  nlinarith

theorem b0_pos_of_pieces (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) : 0 < D.b0 := by
  exact one_div_pos.mpr (Branch2.Planar.Well.lin_pos (D.wellV_hyp y hξ hL hne hb))

theorem XV_smooth (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) : ContDiff ℝ ∞ D.XV :=
  Branch2.Planar.Well.X_smooth (D.wellV_hyp y hξ hL hne hb)

theorem U_third_formula (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (deriv (D.U y))) v = deriv (deriv (deriv (D.U0 y))) v +
      6 * D.kappa * (((1 - v) ^ 4)⁻¹ - (v ^ 4)⁻¹) := by
  have he : deriv (deriv (D.U y)) =ᶠ[𝓝 v] fun t => deriv (deriv (D.U0 y)) t +
      2 * D.kappa * ((t ^ 3)⁻¹ + ((1 - t) ^ 3)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    exact D.U_second_formula y hξ hL hne hb ht
  rw [he.deriv_eq]
  have hs := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (D.U0_smooth y hne)).2).2
  have h0 := (hs.differentiable (by simp) v).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (t ^ 3)⁻¹) (-3 / v ^ 4) v := by
    have hh := ((hasDerivAt_id v).pow 3).inv (pow_ne_zero 3 hv.1.ne')
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
      field_simp [hv.1.ne']
      <;> ring
  have h2 : HasDerivAt (fun t : ℝ => ((1 - t) ^ 3)⁻¹) (3 / (1 - v) ^ 4) v := by
    have hh := (((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).pow 3).inv
      (pow_ne_zero 3 (sub_pos.mpr hv.2).ne')
    convert hh using 1
    · rfl
    · simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, zero_sub, mul_neg_one]
      field_simp [(sub_pos.mpr hv.2).ne']
      <;> ring
  have hh : HasDerivAt (fun t => deriv (deriv (D.U0 y)) t +
      2 * D.kappa * ((t ^ 3)⁻¹ + ((1 - t) ^ 3)⁻¹))
      (deriv (deriv (deriv (D.U0 y))) v + 2 * D.kappa * (-3 / v ^ 4 + 3 / (1 - v) ^ 4)) v :=
    h0.add ((h1.add h2).const_mul (2 * D.kappa))
  convert hh.deriv using 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The prescribed third-derivative bound holds on the uniform critical-point neighbourhood. -/
theorem U_third_abs_le (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L) {v : ℝ}
    (hv : v ∈ Icc (D.r0 / 2) (1 - D.r0 / 2)) :
    |deriv (deriv (deriv (D.U y))) v| ≤ D.K3max := by
  have hr := r0_pos hξ hL
  have hp : v ∈ Ioo (0 : ℝ) 1 := ⟨(half_pos hr).trans_le hv.1, by linarith [hv.2]⟩
  have h1 := one_div_le_one_div_of_le (pow_pos (half_pos hr) 4)
    (pow_le_pow_left₀ (half_pos hr).le hv.1 4)
  have h2 := one_div_le_one_div_of_le (pow_pos (half_pos hr) 4)
    (pow_le_pow_left₀ (half_pos hr).le (by linarith [hv.2] : D.r0 / 2 ≤ 1 - v) 4)
  have hscale : 1 / (D.r0 / 2) ^ 4 = 16 / D.r0 ^ 4 := by field_simp; ring
  rw [hscale] at h1 h2
  have hdiff : |((1 - v) ^ 4)⁻¹ - (v ^ 4)⁻¹| ≤ 32 / D.r0 ^ 4 := by
    have ht := abs_add_le (((1 - v) ^ 4)⁻¹) (-((v ^ 4)⁻¹))
    simp only [← sub_eq_add_neg, abs_neg,
      abs_of_pos (inv_pos.mpr (pow_pos (sub_pos.mpr hp.2) 4)),
      abs_of_pos (inv_pos.mpr (pow_pos hp.1 4))] at ht
    simp only [div_eq_mul_inv, one_mul] at h1 h2 ⊢
    linarith
  rw [D.U_third_formula y hξ hL hne hb hp]
  have hk := kappa_pos hξ hL
  have hm : |6 * D.kappa * (((1 - v) ^ 4)⁻¹ - (v ^ 4)⁻¹)| ≤ 192 * D.kappa / D.r0 ^ 4 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 6 * D.kappa)]
    have hh := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 6 * D.kappa)
    convert hh using 1 <;> ring
  have hu := D.U0_third_abs_le y hξ hL hne hb v
  have ht := (abs_add_le _ _).trans (add_le_add hu hm)
  unfold K3max
  linarith

end SymplecticPacking.HighDim.PlanarGen.Input
