import SymplecticPacking.HighDim.Comparator.PlanarPotentialBounds

/-!
# Uniform quadratic modification of the radial well

The Taylor estimates use only derivatives on a fixed neighbourhood of the
critical point; they do not replace the prescribed width by a parameterwise
supremum.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Filter Topology
open scoped ContDiff Real

private theorem abs_le_local_aux {f f' : ℝ → ℝ} {c R : ℝ} (k : ℕ)
    (hf : ∀ t, |t| ≤ R → HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t, |t| ≤ R → |f' t| ≤ c * |t| ^ k) {x : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) :
    |f x| ≤ c * x ^ (k + 1) / (k + 1) := by
  have hpow : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c * t ^ (k + 1) / (k + 1)) (c * t ^ k) t := by
    intro t
    have h := ((hasDerivAt_pow (k + 1) t).const_mul c).div_const ((k : ℝ) + 1)
    convert h using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hsub : ∀ t ∈ Icc 0 x, |t| ≤ R := fun t ht => by
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans hxR
  have hm : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      MonotoneOn (fun t => c * t ^ (k + 1) / (k + 1) - s * f t) (Icc 0 x) := by
    intro s hs
    have hd : ∀ t ∈ Icc 0 x, HasDerivAt (fun t => c * t ^ (k + 1) / (k + 1) - s * f t)
        (c * t ^ k - s * f' t) t := fun t ht => (hpow t).sub ((hf t (hsub t ht)).const_mul s)
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 x := interior_subset ht
      rw [(hd t ht').deriv]
      have h1 := hb t (hsub t ht')
      rw [abs_of_nonneg ht'.1] at h1
      have habs : |s * f' t| = |f' t| := by rcases hs with rfl | rfl <;> simp
      have h2 := le_abs_self (s * f' t)
      linarith
  have h1 := hm 1 (Or.inl rfl) (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  have h2 := hm (-1) (Or.inr rfl) (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  simp only [zero_pow (Nat.succ_ne_zero k), h0, mul_zero, zero_div, sub_zero] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Integrating a derivative estimate on the symmetric local interval. -/
theorem abs_le_local {f f' : ℝ → ℝ} {c R : ℝ} (k : ℕ)
    (hf : ∀ t, |t| ≤ R → HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t, |t| ≤ R → |f' t| ≤ c * |t| ^ k) {x : ℝ} (hx : |x| ≤ R) :
    |f x| ≤ c * |x| ^ (k + 1) / (k + 1) := by
  rcases le_total 0 x with hxp | hxn
  · rw [abs_of_nonneg hxp] at hx ⊢
    exact abs_le_local_aux k hf h0 hb hxp hx
  · have h := abs_le_local_aux (f := fun t => f (-t)) (f' := fun t => -f' (-t)) k
      (fun t ht => by
        have hh := (hf (-t) (by simpa only [abs_neg] using ht)).comp t (hasDerivAt_neg t)
        simpa [Function.comp_def] using hh)
      (by simp [h0]) (fun t ht => by simpa using hb (-t) (by simpa only [abs_neg] using ht))
      (x := -x) (by linarith) (by simpa only [abs_of_nonpos hxn] using hx)
    simpa only [neg_neg, abs_of_nonpos hxn] using h

namespace Input

open OAI.PackingSufficiencySupport.MomentPolytope (Moments)

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
    (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
include hξ hL hne hb

lemma alphaMin_pos_of_pieces : 0 < D.alphaMin := by
  unfold alphaMin
  exact mul_pos (by norm_num) (kappa_pos hξ hL)

lemma alphaMax_pos_of_pieces : 0 < D.alphaMax :=
  (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1 |>.trans_le
    (D.alphaU_bounds y hξ hL hne hb).2

lemma K3max_pos : 0 < D.K3max := by
  have hk := kappa_pos hξ hL
  have hr := r0_pos hξ hL
  unfold K3max
  positivity

lemma epsU_pos : 0 < D.epsU := by
  have hr := r0_pos hξ hL
  have ha := D.alphaMin_pos_of_pieces y hξ hL hne hb
  have hA := D.alphaMax_pos_of_pieces y hξ hL hne hb
  have hK := D.K3max_pos y hξ hL hne hb
  have hC := Inner.Cpsi_nonneg
  have hδ := tol_pos hξ
  unfold epsU
  exact lt_min (lt_min (by positivity) (by positivity)) (Real.sqrt_pos.mpr (by positivity))

lemma epsU_le_r0 : D.epsU ≤ D.r0 / 8 := (min_le_left _ _).trans (min_le_left _ _)

lemma shifted_critical_mem {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    D.vstar y + x ∈ Icc (D.r0 / 2) (1 - D.r0 / 2) := by
  have h := D.vstar_uniform_bounds y hξ hL hne hb
  have hx' := abs_le.mp hx
  constructor <;> linarith

lemma U_contDiffAt {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ ∞ (D.U y) v := by
  have h := (D.scalarInput_hyp y hξ hL hne hb).U_smooth
  rw [scalarInput_U] at h
  exact h.contDiffAt (isOpen_Ioo.mem_nhds hv)

lemma shifted_critical_mem_open {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    D.vstar y + x ∈ Ioo (0 : ℝ) 1 := by
  have h := D.shifted_critical_mem y hξ hL hne hb hx
  have hr := r0_pos hξ hL
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma shifted_U_deriv {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    HasDerivAt (D.gU y) (deriv (D.U y) (D.vstar y + x)) x := by
  change HasDerivAt (fun t => D.U y (D.vstar y + t) - D.U y (D.vstar y)) _ x
  have hs := (D.U_contDiffAt y hξ hL hne hb (D.shifted_critical_mem_open y hξ hL hne hb hx)).differentiableAt (by simp)
  have h := hs.hasDerivAt.comp x ((hasDerivAt_const x (D.vstar y)).add (hasDerivAt_id x))
  simpa only [gU, Function.comp_def, zero_add, mul_one] using h.sub_const (D.U y (D.vstar y))

lemma shifted_U_second {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    HasDerivAt (fun t => deriv (D.U y) (D.vstar y + t))
      (deriv (deriv (D.U y)) (D.vstar y + x)) x := by
  have hs : ContDiffAt ℝ ∞ (deriv (D.U y)) (D.vstar y + x) :=
    (D.U_contDiffAt y hξ hL hne hb (D.shifted_critical_mem_open y hξ hL hne hb hx)).derivWithin (by simp)
  have h := (hs.differentiableAt (by simp)).hasDerivAt.comp x
    ((hasDerivAt_const x (D.vstar y)).add (hasDerivAt_id x))
  simpa only [Function.comp_def, zero_add, mul_one] using h

lemma shifted_U_third {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    HasDerivAt (fun t => deriv (deriv (D.U y)) (D.vstar y + t))
      (deriv (deriv (deriv (D.U y))) (D.vstar y + x)) x := by
  have hs1 : ContDiffAt ℝ ∞ (deriv (D.U y)) (D.vstar y + x) :=
    (D.U_contDiffAt y hξ hL hne hb
      (D.shifted_critical_mem_open y hξ hL hne hb hx)).derivWithin (by simp)
  have hs : ContDiffAt ℝ ∞ (deriv (deriv (D.U y))) (D.vstar y + x) := hs1.derivWithin (by simp)
  have h := (hs.differentiableAt (by simp)).hasDerivAt.comp x
    ((hasDerivAt_const x (D.vstar y)).add (hasDerivAt_id x))
  simpa only [Function.comp_def, zero_add, mul_one] using h

lemma gcU_second_error {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    |D.alphaU y - deriv (deriv (D.U y)) (D.vstar y + x)| ≤ D.K3max * |x| := by
  have h := abs_le_local (f := fun t => D.alphaU y - deriv (deriv (D.U y)) (D.vstar y + t))
    (f' := fun t => -deriv (deriv (deriv (D.U y))) (D.vstar y + t)) (c := D.K3max) 0
    (fun t ht => (D.shifted_U_third y hξ hL hne hb ht).const_sub _)
    (by simp [alphaU])
    (fun t ht => by
      simpa using D.U_third_abs_le y hξ hL hne hb (D.shifted_critical_mem y hξ hL hne hb ht)) hx
  simpa using h

lemma gcU_first_error {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    |D.alphaU y * x - deriv (D.U y) (D.vstar y + x)| ≤ D.K3max * x ^ 2 / 2 := by
  have h := abs_le_local (f := fun t => D.alphaU y * t - deriv (D.U y) (D.vstar y + t))
    (f' := fun t => D.alphaU y - deriv (deriv (D.U y)) (D.vstar y + t)) (c := D.K3max) 1
    (fun t ht => by
      convert ((hasDerivAt_id t).const_mul (D.alphaU y)).sub (D.shifted_U_second y hξ hL hne hb ht) using 1
      · funext u; rfl
      · simp)
    (by simp [(D.vstar_spec y hξ hL hne hb).2])
    (fun t ht => by simpa using D.gcU_second_error y hξ hL hne hb ht) hx
  simpa only [Nat.cast_one, one_add_one_eq_two, sq_abs] using h

lemma gcU_error {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    |D.gcU y x| ≤ D.K3max * |x| ^ 3 / 6 := by
  have h := abs_le_local (f := D.gcU y)
    (f' := fun t => D.alphaU y * t - deriv (D.U y) (D.vstar y + t)) (c := D.K3max / 2) 2
    (fun t ht => by
      have hq := (((hasDerivAt_id t).pow 2).const_mul (D.alphaU y)).div_const 2
      have hh := hq.sub (D.shifted_U_deriv y hξ hL hne hb ht)
      convert hh using 1
      · rfl
      · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one]
        ring)
    (by simp [gcU, gU])
    (fun t ht => by
      have hh := D.gcU_first_error y hξ hL hne hb ht
      rw [← sq_abs] at hh
      nlinarith) hx
  norm_num at h
  convert h using 1 <;> ring

lemma epsU_energy_bound : D.alphaU y * D.epsU ^ 2 ≤ D.tol := by
  have hA := D.alphaMax_pos_of_pieces y hξ hL hne hb
  have he := D.epsU_pos y hξ hL hne hb
  have hδ := tol_pos hξ
  have hr : D.epsU ≤ Real.sqrt (D.tol / D.alphaMax) := min_le_right _ _
  have hs := pow_le_pow_left₀ he.le hr 2
  rw [Real.sq_sqrt (div_pos hδ hA).le] at hs
  have hh := (le_div_iff₀ hA).mp hs
  have ha := mul_le_mul_of_nonneg_right (D.alphaU_bounds y hξ hL hne hb).2 (sq_nonneg D.epsU)
  nlinarith

lemma K3max_mul_epsU : D.K3max * D.epsU ≤ D.alphaU y / (32 * (1 + Inner.Cpsi)) := by
  have hK := D.K3max_pos y hξ hL hne hb
  have hC := Inner.Cpsi_nonneg
  have he : D.epsU ≤ D.alphaMin / (32 * D.K3max * (1 + Inner.Cpsi)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have h1 := mul_le_mul_of_nonneg_left he hK.le
  have heq : D.K3max * (D.alphaMin / (32 * D.K3max * (1 + Inner.Cpsi))) =
      D.alphaMin / (32 * (1 + Inner.Cpsi)) := by field_simp
  rw [heq] at h1
  exact h1.trans (div_le_div_of_nonneg_right (D.alphaU_bounds y hξ hL hne hb).1 (by positivity))

lemma ftU_eq_quad {x : ℝ} (hx : |x| ≤ D.epsU) : D.ftU y x = D.alphaU y * x ^ 2 / 2 := by
  have he := D.epsU_pos y hξ hL hne hb
  have hpsi := Inner.psiR_eq_one (t := x / D.epsU)
    (by rw [abs_div, abs_of_pos he, div_le_one he]; exact hx)
  unfold ftU gcU
  rw [hpsi]
  ring

lemma ftU_eq_far {x : ℝ} (hx : 2 * D.epsU ≤ |x|) : D.ftU y x = D.gU y x := by
  have he := D.epsU_pos y hξ hL hne hb
  have hpsi := Inner.psiR_eq_zero (t := x / D.epsU)
    (by rw [abs_div, abs_of_pos he, le_div_iff₀ he]; exact hx)
  unfold ftU
  rw [hpsi, zero_mul, add_zero]

/-- The fixed-width modification changes the original centred potential by at most `tol`. -/
theorem ftU_close (x : ℝ) : |D.ftU y x - D.gU y x| ≤ D.tol := by
  have he := D.epsU_pos y hξ hL hne hb
  have hδ := tol_pos hξ
  rcases le_or_gt (2 * D.epsU) |x| with hx | hx
  · rw [D.ftU_eq_far y hξ hL hne hb hx, sub_self, abs_zero]
    exact hδ.le
  have h1 : |D.ftU y x - D.gU y x| ≤ |D.gcU y x| := by
    unfold ftU
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Inner.psiR_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Inner.psiR_le_one _)
  have hxr : |x| ≤ D.r0 / 2 := by
    have hh := D.epsU_le_r0 y hξ hL hne hb
    linarith
  have h2 := D.gcU_error y hξ hL hne hb hxr
  have hK := D.K3max_pos y hξ hL hne hb
  have h3 : |D.gcU y x| ≤ D.K3max * (2 * D.epsU) ^ 3 / 6 := h2.trans (by gcongr)
  have ha : 0 < D.alphaU y := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  have hC := Inner.Cpsi_nonneg
  have h4 : D.K3max * D.epsU ≤ D.alphaU y / 32 := by
    refine (D.K3max_mul_epsU y hξ hL hne hb).trans ?_
    apply div_le_div_of_nonneg_left ha.le (by norm_num)
    nlinarith
  have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg D.epsU)
  have h6 := D.epsU_energy_bound y hξ hL hne hb
  nlinarith

lemma ftU_hasDerivAt {x : ℝ} (hx : |x| ≤ D.r0 / 2) :
    HasDerivAt (D.ftU y) (deriv (D.U y) (D.vstar y + x) +
      deriv Inner.psiR (x / D.epsU) / D.epsU * D.gcU y x +
      Inner.psiR (x / D.epsU) * (D.alphaU y * x - deriv (D.U y) (D.vstar y + x))) x := by
  have hpsi := (Inner.psiR_differentiable (x / D.epsU)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const D.epsU)
  have hgc : HasDerivAt (D.gcU y) (D.alphaU y * x - deriv (D.U y) (D.vstar y + x)) x := by
    have hq := (((hasDerivAt_id x).pow 2).const_mul (D.alphaU y)).div_const 2
    convert hq.sub (D.shifted_U_deriv y hξ hL hne hb hx) using 1
    · rfl
    · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one]
      ring
  have hh := (D.shifted_U_deriv y hξ hL hne hb hx).add (hpsi.mul hgc)
  convert hh using 1
  · rfl
  · simp only [id_eq, Function.comp_apply]
    ring

/-- The fixed-width quadratic modification remains a nondegenerate well near the origin. -/
theorem ftU_deriv_near {x : ℝ} (hx : |x| ≤ 2 * D.epsU) :
    91 / 96 * D.alphaU y * x ^ 2 ≤ x * deriv (D.ftU y) x := by
  have he := D.epsU_pos y hξ hL hne hb
  have hxr : |x| ≤ D.r0 / 2 := by
    have hh := D.epsU_le_r0 y hξ hL hne hb
    linarith
  rw [(D.ftU_hasDerivAt y hξ hL hne hb hxr).deriv]
  set ε := D.epsU
  set a := D.alphaU y
  set K := D.K3max
  set C := Inner.Cpsi
  set ψ := Inner.psiR (x / ε)
  set d := deriv Inner.psiR (x / ε)
  set Gc := D.gcU y x
  set G1 := a * x - deriv (D.U y) (D.vstar y + x)
  have e : x * (deriv (D.U y) (D.vstar y + x) + d / ε * Gc + ψ * G1) =
      a * x ^ 2 - (1 - ψ) * (x * G1) + x * (d / ε * Gc) := by simp only [G1]; ring
  set u := |x|
  have ha : 0 < a := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
    (D.alphaU_bounds y hξ hL hne hb).1
  have hK : 0 < K := D.K3max_pos y hξ hL hne hb
  have hC : 0 ≤ C := Inner.Cpsi_nonneg
  have hu : 0 ≤ u := abs_nonneg x
  have hx2 : x ^ 2 = u ^ 2 := (sq_abs x).symm
  have hKe : K * ε ≤ a / (32 * (1 + C)) := D.K3max_mul_epsU y hξ hL hne hb
  have hG1 : |G1| ≤ K * x ^ 2 / 2 := D.gcU_first_error y hξ hL hne hb hxr
  have hG : |Gc| ≤ K * u ^ 3 / 6 := D.gcU_error y hξ hL hne hb hxr
  have hd : |d| ≤ C := Inner.abs_deriv_psiR_le _
  have hψ0 : 0 ≤ ψ := Inner.psiR_nonneg _
  have hψ1 : ψ ≤ 1 := Inner.psiR_le_one _
  have h1 : |x * G1| ≤ (K * ε) * x ^ 2 := by
    rw [abs_mul]
    calc u * |G1| ≤ u * (K * x ^ 2 / 2) := mul_le_mul_of_nonneg_left hG1 hu
      _ = K * x ^ 2 * (u / 2) := by ring
      _ ≤ K * x ^ 2 * ε := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (K * ε) * x ^ 2 := by ring
  have h2 : |x * (d / ε * Gc)| ≤ 2 / 3 * C * (K * ε) * x ^ 2 := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos he]
    have hu2 : u ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
    have : u * (|d| * |Gc|) ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε := by
      calc u * (|d| * |Gc|) ≤ u * (C * (K * u ^ 3 / 6)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hd hG (abs_nonneg _) hC) hu
        _ = C * K * u ^ 2 * u ^ 2 / 6 := by ring
        _ ≤ C * K * u ^ 2 * (4 * ε ^ 2) / 6 := by gcongr
        _ = 2 / 3 * C * (K * ε) * x ^ 2 * ε := by rw [hx2]; ring
    calc u * (|d| / ε * |Gc|) = u * (|d| * |Gc|) / ε := by ring
      _ ≤ 2 / 3 * C * (K * ε) * x ^ 2 * ε / ε := by gcongr
      _ = 2 / 3 * C * (K * ε) * x ^ 2 := by field_simp
  have hKe1 : (K * ε) * x ^ 2 ≤ a / 32 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    refine hKe.trans ?_
    apply div_le_div_of_nonneg_left ha.le (by norm_num); nlinarith
  have hKe2 : 2 / 3 * C * (K * ε) * x ^ 2 ≤ a / 48 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
    have hCK : 2 / 3 * C * (K * ε) ≤ 2 / 3 * C * (a / (32 * (1 + C))) :=
      mul_le_mul_of_nonneg_left hKe (by positivity)
    refine hCK.trans ?_
    rw [show 2 / 3 * C * (a / (32 * (1 + C))) = a / 48 * (C / (1 + C)) by
      field_simp; ring]
    have : C / (1 + C) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith
  have b1 : (1 - ψ) * (x * G1) ≤ |x * G1| :=
    calc (1 - ψ) * (x * G1) ≤ (1 - ψ) * |x * G1| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ 1 * |x * G1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |x * G1| := one_mul _
  have b2 := neg_abs_le (x * (d / ε * Gc))
  rw [e]
  nlinarith


lemma gU_contDiffOn : ContDiffOn ℝ ∞ (D.gU y) (Ioo (-(D.vstar y)) (1 - D.vstar y)) := by
  intro x hx
  have hu := D.U_contDiffAt y hξ hL hne hb
    (show D.vstar y + x ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2])
  exact ((hu.comp x (contDiffAt_const.add contDiffAt_id)).sub contDiffAt_const).contDiffWithinAt

lemma ftU_contDiffOn : ContDiffOn ℝ ∞ (D.ftU y) (Ioo (-(D.vstar y)) (1 - D.vstar y)) := by
  have hg := D.gU_contDiffOn y hξ hL hne hb
  change ContDiffOn ℝ ∞ (fun x => D.gU y x + Inner.psiR (x / D.epsU) *
    (D.alphaU y * x ^ 2 / 2 - D.gU y x)) _
  exact hg.add ((Inner.psiR_contDiff.comp (contDiff_id.div_const _)).contDiffOn.mul
    (((contDiffOn_const.mul (contDiffOn_id.pow 2)).div_const 2).sub hg))

lemma ftU_zero : D.ftU y 0 = 0 := by
  rw [D.ftU_eq_quad y hξ hL hne hb (by simpa using (D.epsU_pos y hξ hL hne hb).le)]
  ring

lemma deriv_gU (x : ℝ) : deriv (D.gU y) x = deriv (D.U y) (D.vstar y + x) := by
  unfold gU
  rw [deriv_sub_const, deriv_comp_const_add]

/-- The prescribed modification has no additional critical point. -/
theorem ftU_mono {x : ℝ} (hx : x ∈ Ioo (-(D.vstar y)) (1 - D.vstar y)) (hx0 : x ≠ 0) :
    0 < x * deriv (D.ftU y) x := by
  rcases le_or_gt |x| (2 * D.epsU) with hn | hf
  · have h := D.ftU_deriv_near y hξ hL hne hb hn
    have ha : 0 < D.alphaU y := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le
      (D.alphaU_bounds y hξ hL hne hb).1
    have hpos : 0 < 91 / 96 * D.alphaU y * x ^ 2 := by positivity
    linarith
  · have heq : D.ftU y =ᶠ[𝓝 x] D.gU y := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hf] with t ht
      exact D.ftU_eq_far y hξ hL hne hb ht.le
    rw [heq.deriv_eq, D.deriv_gU y hξ hL hne hb]
    have hp : D.vstar y + x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have hp0 : D.vstar y + x ≠ (D.scalarInput y).pstar := by
      rw [scalarInput_pstar]
      intro he
      apply hx0
      linarith
    have hs := Branch2.Planar.PlanarInput.U_sign (D.scalarInput_hyp y hξ hL hne hb) hp hp0
    rw [scalarInput_U, scalarInput_pstar, add_sub_cancel_left] at hs
    exact hs

end Input

end SymplecticPacking.HighDim.PlanarGen
