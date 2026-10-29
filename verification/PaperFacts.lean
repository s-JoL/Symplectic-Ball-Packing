import SymplecticPacking.General.Ham.Defs
import SymplecticPacking.Branch2.Planar.Potential
import SymplecticPacking.Qhat.Main
import SymplecticPacking.Qhat.Density
import SymplecticPacking.Return.ReturnFlow
import SymplecticPacking.Return.BallChart
import SymplecticPacking.Branch2.Model.Cubic.Strip.LayerMaps

/-!
# Supporting facts used by the paper index

Small consequences of the construction's public API. Keeping these facts in the
verification layer avoids adding dependencies to the Hamiltonian construction.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace SymplecticPacking

namespace General.Ham

theorem radialCutoff_mem_Icc {n : ℕ} (ron roff : ℝ) (u : Problem.E n) :
    radialCutoff ron roff u ∈ Icc (0 : ℝ) 1 := by
  unfold radialCutoff
  constructor
  · linarith [Real.smoothTransition.le_one ((‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2))]
  · linarith [Real.smoothTransition.nonneg ((‖u‖ ^ 2 - ron ^ 2) / (roff ^ 2 - ron ^ 2))]

end General.Ham

namespace Branch2.Planar.PlanarInput

theorem Hyp.V_strictConvex {D : Branch2.Planar.PlanarInput} (hD : D.Hyp) :
    StrictConvexOn ℝ (Ioo (-(1 / 2 : ℝ)) (1 / 2)) D.V := by
  have he (t : ℝ) (ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      D.V t = D.nu / 4 * (1 / (t + 1 / 2) + 1 / (1 / 2 - t)) - D.nu := by
    have h1 : 0 < t + 1 / 2 := by linarith [ht.1]
    have h2 : 0 < 1 / 2 - t := by linarith [ht.2]
    have h3 : 0 < 1 / 4 - t ^ 2 := by nlinarith [mul_pos h1 h2]
    have h1n : (1 : ℝ) + t * 2 ≠ 0 := by linarith
    have h2n : (1 : ℝ) - t * 2 ≠ 0 := by linarith
    have h3n : (1 : ℝ) - t ^ 2 * 4 ≠ 0 := by linarith
    unfold V
    field_simp [h1n, h2n, h3n]
    ring_nf
    field_simp [h1n, h2n, h3n]
    ring
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hz := (convex_Ioo (-(1 / 2 : ℝ)) (1 / 2) : Convex ℝ _)
    hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hz ⊢
  rw [he _ hz, he x hx, he y hy]
  have h := barrier_strict hx hy hxy ha hb hab
  simp only [sub_neg_eq_add] at h
  have hprod := mul_lt_mul_of_pos_left h (div_pos hD.nu_pos (by norm_num : (0 : ℝ) < 4))
  have hab' := congrArg (fun t : ℝ => D.nu * t) hab
  nlinarith

end Branch2.Planar.PlanarInput

namespace Params
variable (P : Params)

theorem dn_sub_h : P.dn - P.h = (1 / 3 - P.h) / 2 := by
  unfold dn
  ring

theorem one_sub_three_dn : 1 - 3 * P.dn = (1 - P.t0) / 2 := by
  unfold dn h
  ring

theorem alpha0_eq : Inner.Rmorse2 P 0 = P.alpha0 := Inner.Rmorse2_zero P

theorem r_sq_eq_two_n : P.r ^ 2 = 2 * P.n := by
  rw [P.r_sq]
  unfold n A B
  field_simp [P.a_pos.ne', (sub_pos.mpr P.a_lt_h).ne']
  ring

theorem density : (P.k : ℝ) * P.rho ^ 2 = (1 - P.ε / 4) ^ 2 := by
  have hs := P.s_sq
  unfold rho
  rw [div_pow, ← hs]
  field_simp [P.s_pos.ne']

theorem pplus_add_d0_lt : P.pplus + P.d0 < P.h - Inner.deltaPrime P := by
  have h := P.pplus_lt_Ec_sub_d0
  have hd := P.deltaPrime_eq
  have he := P.eq_pos
  unfold Ec at h
  linarith

theorem Rmorse_nonneg (x : ℝ) : 0 ≤ P.Rmorse x := by
  rcases le_total 0 x with hx | hx
  · have h := (Inner.Rmorse_strictMonoOn P).monotoneOn (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx
    simpa only [P.Rmorse_zero] using h
  · have h := (Inner.Rmorse_strictAntiOn P).antitoneOn hx
      (show (0 : ℝ) ∈ Iic 0 from by simp) hx
    simpa only [P.Rmorse_zero] using h

theorem sublevel_subset {b : ℝ} (hb0 : 0 ≤ b) (hbh : b ≤ P.h) :
    {x : ℝ | P.Rcal x ≤ b} ⊆ Icc 0 P.h := by
  intro x hx
  have hx' := (P.Rcal_le_iff hb0 x).mp hx
  have ha : P.h / P.A = P.a := by unfold A; field_simp [P.a_pos.ne', P.h_pos.ne']
  have hb : P.h / P.B = P.h - P.a := by
    unfold B
    field_simp [(sub_pos.mpr P.a_lt_h).ne', P.h_pos.ne']
  have hba := div_le_div_of_nonneg_right hbh P.A_pos.le
  have hbb := div_le_div_of_nonneg_right hbh P.B_pos.le
  rw [ha] at hba
  rw [hb] at hbb
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

theorem volume_sublevel {b : ℝ} (hb : 0 ≤ b) :
    MeasureTheory.volume {x : ℝ | P.Rcal x ≤ b} = ENNReal.ofReal b := by
  have he : {x : ℝ | P.Rcal x ≤ b} = Icc (P.a - b / P.A) (P.a + b / P.B) :=
    Set.ext fun x => P.Rcal_le_iff hb x
  rw [he, Real.volume_Icc, P.sublevel_length]

end Params

namespace Inner
variable (P : Params)

theorem Xinv_smooth : ContDiff ℝ ∞ (Xinv P) := by
  have he := P.eta_pos
  have hr := P.r_pos
  have hs : ContDiff ℝ ∞ (fun u : ℝ => Real.sqrt (u ^ 2 + 2 * P.eta * P.r)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun u => by
      exact (show 0 < u ^ 2 + 2 * P.eta * P.r by positivity).ne')
  unfold Xinv
  have hi : ContDiff ℝ ∞ (fun u : ℝ => u) := contDiff_id
  exact ((contDiff_const.mul (hi.pow 2)).add
    ((contDiff_const.mul hi).mul hs)).div_const (P.r ^ 2)

private theorem Xinv_hasDerivAt (u : ℝ) :
    HasDerivAt (Xinv P)
      ((-P.m * (2 * u) + P.n * (Real.sqrt (u ^ 2 + 2 * P.eta * P.r) +
        u * (u / Real.sqrt (u ^ 2 + 2 * P.eta * P.r)))) / P.r ^ 2) u := by
  have hu : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hs : HasDerivAt (fun v : ℝ => Real.sqrt (v ^ 2 + 2 * P.eta * P.r))
      (u / Real.sqrt (u ^ 2 + 2 * P.eta * P.r)) u := by
    have he := P.eta_pos
    have hr := P.r_pos
    convert (hu.add_const (2 * P.eta * P.r)).sqrt (by positivity) using 1
    field_simp [(sX_pos P u).ne']
  have h := ((hu.const_mul (-P.m)).add
    (((hasDerivAt_id u).mul hs).const_mul P.n)).div_const (P.r ^ 2)
  convert h using 1
  · funext v
    dsimp [Xinv]
    ring
  · simp only [id_eq]
    ring

theorem Xinv_deriv_pos (u : ℝ) : 0 < deriv (Xinv P) u := by
  rw [(Xinv_hasDerivAt P u).deriv]
  apply div_pos _ (sq_pos_of_pos P.r_pos)
  have hs := sX_pos P u
  have hsq := sX_sq P u
  have hg := abs_lt_sX P u
  have he : Real.sqrt (u ^ 2 + 2 * P.eta * P.r) +
      u * (u / Real.sqrt (u ^ 2 + 2 * P.eta * P.r)) =
        (2 * u ^ 2 + 2 * P.eta * P.r) / Real.sqrt (u ^ 2 + 2 * P.eta * P.r) := by
    field_simp [hs.ne']
    nlinarith
  have hm : 2 * |u| < Real.sqrt (u ^ 2 + 2 * P.eta * P.r) +
      u * (u / Real.sqrt (u ^ 2 + 2 * P.eta * P.r)) := by
    rw [he, lt_div_iff₀ hs]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hg), sq_abs u]
  have hb : P.m * u ≤ P.n * |u| :=
    (m_mul_le P.m u).trans
      (mul_le_mul_of_nonneg_right (abs_m_lt_n P).le (abs_nonneg u))
  have hpos := mul_lt_mul_of_pos_left hm P.n_pos
  nlinarith

theorem Xinv_deriv_zero : deriv (Xinv P) 0 = a0 P := by
  have hc : 0 < 2 * P.eta * P.r := by have := P.eta_pos; have := P.r_pos; positivity
  have hp : 0 < P.n * Real.sqrt (2 * P.eta * P.r) / P.r ^ 2 :=
    div_pos (mul_pos P.n_pos (Real.sqrt_pos.mpr hc)) (sq_pos_of_pos P.r_pos)
  have he : (P.n * Real.sqrt (2 * P.eta * P.r) / P.r ^ 2) ^ 2 = (a0 P) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hc.le, a0,
      Real.sq_sqrt (div_pos (by norm_num : (0 : ℝ) < 2) P.alpha0_pos).le]
    unfold Params.alpha0
    field_simp [P.r_pos.ne', P.eta_pos.ne', P.n_pos.ne']
  have hv : P.n * Real.sqrt (2 * P.eta * P.r) / P.r ^ 2 = a0 P := by
    nlinarith [a0_pos P]
  rw [(Xinv_hasDerivAt P 0).deriv]
  simpa using hv

theorem Xinv_strictMono : StrictMono (Xinv P) := strictMono_of_deriv_pos (Xinv_deriv_pos P)

private theorem Xinv_growth (u : ℝ) :
    (0 ≤ u → (P.n - |P.m|) / P.r ^ 2 * u ^ 2 ≤ Xinv P u) ∧
      (u ≤ 0 → Xinv P u ≤ -((P.n - |P.m|) / P.r ^ 2) * u ^ 2) := by
  have hs := mul_le_mul_of_nonneg_left (abs_lt_sX P u).le P.n_pos.le
  have hm := m_mul_le P.m u
  have hF : (P.n - |P.m|) * |u| ≤
      P.n * Real.sqrt (u ^ 2 + 2 * P.eta * P.r) - P.m * u := by nlinarith
  constructor
  · intro hu
    calc
      _ = u * ((P.n - |P.m|) * |u|) / P.r ^ 2 := by rw [abs_of_nonneg hu]; ring
      _ ≤ u * (P.n * Real.sqrt (u ^ 2 + 2 * P.eta * P.r) - P.m * u) / P.r ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hu) (sq_nonneg _)
      _ = _ := (Xinv_eq_mul P u).symm
  · intro hu
    calc
      _ = u * (P.n * Real.sqrt (u ^ 2 + 2 * P.eta * P.r) - P.m * u) / P.r ^ 2 := Xinv_eq_mul P u
      _ ≤ u * ((P.n - |P.m|) * |u|) / P.r ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hF hu) (sq_nonneg _)
      _ = _ := by rw [abs_of_nonpos hu]; ring

theorem Xinv_tendsto_atTop : Tendsto (Xinv P) atTop atTop := by
  have hc : 0 < (P.n - |P.m|) / P.r ^ 2 :=
    div_pos (sub_pos.mpr (abs_m_lt_n P)) (sq_pos_of_pos P.r_pos)
  have ht : Tendsto (fun u : ℝ => (P.n - |P.m|) / P.r ^ 2 * u ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu using (Xinv_growth P u).1 hu

theorem Xinv_tendsto_atBot : Tendsto (Xinv P) atBot atBot := by
  have hc : 0 < (P.n - |P.m|) / P.r ^ 2 :=
    div_pos (sub_pos.mpr (abs_m_lt_n P)) (sq_pos_of_pos P.r_pos)
  have hs : Tendsto (fun u : ℝ => u ^ 2) atBot atTop := by
    have hp : Tendsto (fun u : ℝ => u ^ 2) atTop atTop :=
      tendsto_pow_atTop (by decide : 2 ≠ 0)
    simpa only [Function.comp_def, neg_sq] using
      hp.comp (tendsto_neg_atBot_atTop : Tendsto (fun u : ℝ => -u) atBot atTop)
  have ht : Tendsto (fun u : ℝ => -((P.n - |P.m|) / P.r ^ 2) * u ^ 2) atBot atBot := by
    simpa only [Function.comp_def, neg_mul] using
      tendsto_neg_atTop_atBot.comp (hs.const_mul_atTop hc)
  apply tendsto_atBot_mono' atBot _ ht
  filter_upwards [eventually_le_atBot (0 : ℝ)] with u hu using (Xinv_growth P u).2 hu

theorem Vtilde_neg (y : ℝ) : Vtilde P (-y) = Vtilde P y := by
  simp [Vtilde, stV, argV]

theorem Vtilde_quadratic {y : ℝ} (hy : |y| ≤ 1 / 2 - wV P) :
    Vtilde P y = P.eq_ * y ^ 2 / 2 := by
  simp [Vtilde, stV_eq_zero P hy]

theorem Vtilde_half : Vtilde P (1 / 2) = P.eq_ / 8 + 2 * P.h := by
  have hc := (one_sub_cV_sq_pos P).ne'
  have ha : argV P (1 / 2) = 1 := by
    unfold argV
    field_simp
    ring
  norm_num [Vtilde, stV, ha, Real.smoothTransition.one_of_one_le (le_refl (1 : ℝ))]
  ring

theorem Vtilde_half_gt : P.h < Vtilde P (1 / 2) := by
  rw [Vtilde_half P]
  linarith [P.h_pos, P.eq_pos]

theorem SigmaV_neg (y : ℝ) : SigmaV P (-y) = -SigmaV P y := by
  simp [SigmaV, sigmaV, stV, argV]

theorem Ytilde_odd (v : ℝ) : Ytilde P (-v) = -Ytilde P v := by
  apply (SigmaV_strictMono P).injective
  rw [SigmaV_Ytilde, SigmaV_neg, SigmaV_Ytilde]

theorem muV_lt : muV P < P.eq_ / 4 := by
  linarith [muV_le P, P.eq_pos]

theorem Ytilde_deriv_even (v : ℝ) : deriv (Ytilde P) (-v) = deriv (Ytilde P) v := by
  have h1 := (((Ytilde_smooth P).differentiable (by simp) (-v)).hasDerivAt).comp v
    (hasDerivAt_neg v)
  have h2 := (((Ytilde_smooth P).differentiable (by simp) v).hasDerivAt).neg
  have he : (fun x => Ytilde P (-x)) = fun x => -Ytilde P x := funext (Ytilde_odd P)
  change HasDerivAt (fun x => Ytilde P (-x)) _ v at h1
  rw [he] at h1
  have h := h1.unique h2
  nlinarith

end Inner

namespace Qhat
open _root_.Complex
open scoped Real
variable (P : Params)

theorem Clam_hasFDerivAt_zero (w : ℂ) : HasFDerivAt (Clam P 0) (DC0 P) w := by
  rw [show Clam P 0 = fun z => bpt P + DC0 P z from funext (Clam_zero_eq P)]
  exact (DC0 P).hasFDerivAt.const_add (bpt P)

theorem qinner_deriv_zero (w : ℂ) : HasFDerivAt (qinner P 0) (A0 P) w := by
  rw [show qinner P 0 = fun z => bpt P + A0 P z from funext (qinner_zero P)]
  exact (A0 P).hasFDerivAt.const_add (bpt P)

theorem A0_det : LinearMap.det (A0 P : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have h := qinner_symplectic P (s := 0) ⟨le_rfl, zero_le_one⟩ (z := 0)
    (by simpa using (pdag_pos' P).le)
  rwa [(qinner_deriv_zero P 0).fderiv] at h

theorem fs_linear_near_zero {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : ‖z‖ ≤ √(j0 P) * Inner.rhoT P) : fs P s z = Lmap P z := by
  have hj : 0 < √(j0 P) := Real.sqrt_pos.mpr (Inner.j0_pos P)
  have hw : ‖z / (√(j0 P) : ℂ)‖ ≤ Inner.rhoT P := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hj.le]
    exact (div_le_iff₀ hj).mpr (by simpa only [mul_comm] using hz)
  have hx := Inner.Xtilde_linear P ((abs_re_le_norm _).trans
    (hw.trans (min_le_left _ _)))
  have hy := Inner.Ytilde_linear P ((abs_im_le_norm _).trans
    (hw.trans (min_le_right _ _)))
  have hf : Fs P s (z / (√(j0 P) : ℂ)) = Fs P 0 (z / (√(j0 P) : ℂ)) := by
    simp only [Fs, Xs, Ys, hx, hy, b0, Inner.b0, zero_mul, sub_zero, one_mul, add_zero]
    congr 1 <;> push_cast <;> ring
  rw [(fs_fixed P hs).2.2 z hz, hf, ← (fs_fixed P ⟨le_rfl, zero_le_one⟩).2.2 z hz,
    fs_eq_L_at_zero]

theorem fs_zero_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : fs P s 0 = 0 := by
  have h := fs_linear_near_zero P hs (z := 0) (by
    simpa using (mul_pos (Real.sqrt_pos.mpr (Inner.j0_pos P)) (Inner.rhoT_pos P)).le)
  simpa [Lmap] using h

theorem fs_deriv_zero {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (fs P s) (Lclm P) 0 := by
  have hr : 0 < √(j0 P) * Inner.rhoT P :=
    mul_pos (Real.sqrt_pos.mpr (Inner.j0_pos P)) (Inner.rhoT_pos P)
  have heq : fs P s =ᶠ[𝓝 (0 : ℂ)] Lclm P := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    rw [Lclm_apply]
    have hz' : ‖z‖ < √(j0 P) * Inner.rhoT P := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact fs_linear_near_zero P hs hz'.le
  exact (Lclm P).hasFDerivAt.congr_of_eventuallyEq heq

theorem qhat_common_core {D : PathData} (hD : OrdinaryPath D) {t : ℝ} {z : ℂ}
    (hz : π * ‖z‖ ^ 2 ≤ D.c ^ 2 * pon D) :
    qhat D t z = D.path t ((Real.sqrt (D.gam t))⁻¹ • z) := by
  exact (qhat_core hD
    (hz.trans (mul_le_mul_of_nonneg_right (hD.gam_ge t) (pon_pos hD).le))).2

theorem ambientFlow_openDisk {D : PathData} (hD : OrdinaryPath D) {R : ℝ}
    (hR : D.Psupp < R) (t : ℝ) : ambientFlow D t '' areaDisk R = areaDisk R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change π * ‖x‖ ^ 2 < R at hx
    change π * ‖ambientFlow D t x‖ ^ 2 < R
    by_cases hs : π * ‖x‖ ^ 2 ≤ D.Psupp
    · have hm : ambientFlow D t x ∈ closedAreaDisk D.Psupp := by
        rw [← ambientFlow_disk hD le_rfl t]
        exact ⟨x, hs, rfl⟩
      exact lt_of_le_of_lt hm hR
    · rw [ambientFlow_eq_id hD (lt_of_not_ge hs) t]
      exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := (ambientFlow_bijective hD t).surjective y
    refine ⟨x, ?_, rfl⟩
    change π * ‖x‖ ^ 2 < R
    by_contra hn
    have hs : D.Psupp < π * ‖x‖ ^ 2 := hR.trans_le (le_of_not_gt hn)
    rw [ambientFlow_eq_id hD hs t] at hy
    exact hn hy

end Qhat

namespace Strip
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

theorem x_lower_margin {K : Set ℂ} (hK : IsCompact K) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, a ≤ (psiStrip δ z).re := by
  exact hK.exists_forall_le' ((Complex.continuous_re.comp (psiStrip_smooth hδ).continuous).continuousOn)
    (fun z _ => psiStrip_x_pos hδ z)

theorem T_margin {K : Set ℂ} (hK : IsCompact K) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, a ≤ (psiStrip δ z).im ∧ (psiStrip δ z).im ≤ 1 - a := by
  have hc := Complex.continuous_im.comp (psiStrip_smooth hδ).continuous
  obtain ⟨a, ha, h⟩ := hK.exists_forall_le' (hc.min (continuous_const.sub hc)).continuousOn
    (fun z _ => lt_min (psiStrip_mem hδ z).2.1 (sub_pos.mpr (psiStrip_mem hδ z).2.2))
  refine ⟨a, ha, fun z hz => ?_⟩
  have he := (le_min_iff.mp (h z hz))
  change a ≤ (psiStrip δ z).im ∧ a ≤ 1 - (psiStrip δ z).im at he
  exact ⟨he.1, by linarith [he.2]⟩

namespace Cubic

omit hδ in
theorem layerMap_compact (P : Branch2.VCubic) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k)
    {K : Set E4} (hK : IsCompact K) (hKsrc : K ⊆ srcBall P i) :
    IsCompact (layerMap P i '' K) :=
  hK.image_of_continuousOn (fun _ hx =>
    (layerMap_smooth P hi1 hik (hKsrc hx)).continuousAt.continuousWithinAt)

end Cubic

omit hδ in
theorem Rst_nonneg {b x : ℝ} (hb : 0 < b) (hx : 0 < x) : 0 ≤ Rst b x := by
  obtain ⟨u, _, hu⟩ := (Xst_bijOn hb).surjOn (Set.mem_Ioi.mpr hx)
  rw [← hu, Rst_Xst hb]
  exact sq_nonneg u

omit hδ in
theorem Rst_eq_zero_iff {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    Rst b x = 0 ↔ x = b / 2 := by
  obtain ⟨u, _, hu⟩ := (Xst_bijOn hb).surjOn (Set.mem_Ioi.mpr hx)
  rw [← hu, Rst_Xst hb]
  constructor
  · intro h
    rw [sq_eq_zero_iff] at h
    simp [h, Xst]
  · intro h
    have h0 : Xst b 0 = b / 2 := by simp [Xst]
    have : u = 0 := (Xst_strictMono hb).injective (h.trans h0.symm)
    simp [this]

omit hδ in
theorem Vst_eq_zero_iff {b T : ℝ} (hb : 0 < b) (hT0 : 0 < T) (hT1 : T < 1) :
    Vst b T = 0 ↔ T = 1 / 2 := by
  obtain ⟨v, _, hv⟩ := (Yst_bijOn hb).surjOn (Set.mem_Ioo.mpr ⟨hT0, hT1⟩)
  rw [← hv, Vst_Yst hb]
  constructor
  · intro h
    rw [sq_eq_zero_iff] at h
    simp [h, Yst]
  · intro h
    have h0 : Yst b 0 = 1 / 2 := by simp [Yst]
    have : v = 0 := (Yst_strictMono hb).injective (h.trans h0.symm)
    simp [this]

omit hδ in
theorem sublevel_empty {b c : ℝ} (hb : 0 < b) (hc : c < 0) :
    {x : ℝ | 0 < x ∧ Rst b x ≤ c} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, h⟩
  exact (not_le_of_gt hc) ((Rst_nonneg hb hx).trans h)

omit hδ in
theorem width_sublevel {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    Xst b (Real.sqrt c) - Xst b (-Real.sqrt c) = Real.sqrt (c * (c + 2 * b)) := by
  rw [Xst_sub_neg hb, Real.sq_sqrt hc, Real.sqrt_mul hc]

omit hδ in
theorem integral_Vst (b : ℝ) :
    (∫ T in (0 : ℝ)..1, Vst b T) = b * (Real.pi / 2 - 1) := by
  let w : ℝ → ℝ := fun x => (Real.sqrt (1 - x ^ 2))⁻¹
  have hi : (∫ x in (-1 : ℝ)..1, w x) = Real.pi := by
    have h := Polynomial.Chebyshev.integral_measureT_eq_integral_cos (f := fun _ : ℝ => (1 : ℝ))
    rw [Polynomial.Chebyshev.integral_measureT] at h
    simpa [w] using h
  have hs (T : ℝ) : Real.sqrt (1 - (2 * T - 1) ^ 2) = 2 * Real.sqrt (T * (1 - T)) := by
    rw [show 1 - (2 * T - 1) ^ 2 = 4 * (T * (1 - T)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hj : IntervalIntegrable (fun T => w (2 * T - 1)) MeasureTheory.volume 0 1 := by
    have h := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.comp_add_right (-1)
    norm_num at h
    have h' := h.comp_mul_left (c := 2)
    simpa [w, sub_eq_add_neg] using h'
  have hi' : (∫ T in (0 : ℝ)..1, w (2 * T - 1)) = Real.pi / 2 := by
    have h := intervalIntegral.integral_comp_mul_sub (a := (0 : ℝ)) (b := 1) w
      (c := 2) (by norm_num) 1
    calc
      _ = (2 : ℝ)⁻¹ * ∫ x in (-1 : ℝ)..1, w x := by
        simpa only [mul_zero, mul_one, zero_sub, smul_eq_mul,
          show (2 : ℝ) - 1 = 1 by norm_num] using h
      _ = Real.pi / 2 := by rw [hi]; ring
  have he : Vst b = fun T => b * (w (2 * T - 1) - 1) := by
    funext T
    simp only [Vst, w, hs T, one_div]
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hj intervalIntegrable_const,
    hi']
  norm_num

end Strip

namespace Return

theorem ballChart_gauge (Z : C3) {c : ℂ} (hc : starRingEnd ℂ c * c = 1) :
    ballChart (c • Z) = ballChart Z := by
  have hn : ‖c‖ = 1 := by
    have h := congrArg (norm : ℂ → ℝ) hc
    simp only [norm_mul, Complex.norm_conj, norm_one] at h
    nlinarith [norm_nonneg c]
  have he (j : Fin 3) :
      starRingEnd ℂ (c * Z 0) / (‖c * Z 0‖ : ℂ) * (c * Z j) =
        starRingEnd ℂ (Z 0) / (‖Z 0‖ : ℂ) * Z j := by
    rw [norm_mul, hn, one_mul, map_mul]
    calc
      _ = (starRingEnd ℂ c * c) * (starRingEnd ℂ (Z 0) / (‖Z 0‖ : ℂ) * Z j) := by ring
      _ = _ := by rw [hc, one_mul]
  apply Prod.ext
  · simpa only [ballChart, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun z : ℂ => z / (Real.sqrt Real.pi : ℂ)) (he 1)
  · simpa only [ballChart, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun z : ℂ => z / (Real.sqrt Real.pi : ℂ)) (he 2)

theorem returnFlow_smooth {dn : ℝ} (hdn3 : dn ≤ 1 / 3) :
    ContDiff ℝ ∞ (fun p : ℝ × C3 => returnFlow dn p.1 p.2) :=
  (returnVF_csField hdn3).flow_smooth

theorem returnFlowInv_returnFlow {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    returnFlowInv dn s (returnFlow dn s Z) = Z :=
  (returnVF_csField hdn3).flowInv_flow s Z

theorem returnFlow_gaugeEquiv {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) {c : ℂ}
    (hc : starRingEnd ℂ c * c = 1) : returnFlow dn s (c • Z) = c • returnFlow dn s Z :=
  (returnVF_csField hdn3).flow_map (L := LinearMap.toContinuousLinearMap (gaugeC3 c))
    (fun t y => returnVF_gauge dn t y hc) s Z

theorem returnFlow_equivariant {dn : ℝ} (hdn3 : dn ≤ 1 / 3) (s : ℝ) (Z : C3) :
    returnFlow dn s (cubeRoot Z) = cubeRoot (returnFlow dn s Z) :=
  (returnVF_csField hdn3).flow_map (L := LinearMap.toContinuousLinearMap cubeRootC3)
    (fun t y => returnVF_cubeRoot dn t y) s Z

end Return
end SymplecticPacking
