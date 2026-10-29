import SymplecticPacking.HighDim.Comparator.PlanarNormalization
import SymplecticPacking.HighDim.Comparator.PlanarBarrierBounds

/-!
# Uniform coordinate bounds and endpoint barrier margins
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
    (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
include hξ hL hne hb hbM

lemma XU_barrier {u : ℝ} (hu : u ^ 2 ≤ D.Ebar) :
    D.dP < D.vstar y + D.XU y u ∧ D.vstar y + D.XU y u < 1 - D.dP := by
  let P := D.vstar y + D.XU y u
  have hm := D.XU_mem y hξ hL hne hb u
  have hP : P ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [P]; linarith [hm.1], by dsimp [P]; linarith [hm.2]⟩
  have hmin := D.vstar_minimum y hξ hL hne hb (v := 1 / 2) (by constructor <;> norm_num)
  have hosc := D.U0_oscillation y hξ hne hbM (u := P) (v := 1 / 2) ⟨hP.1.le, hP.2.le⟩
    (by constructor <;> norm_num)
  have hclose := D.ftU_close y hξ hL hne hb (D.XU y u)
  rw [D.ftU_XU y hξ hL hne hb] at hclose
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have henergy : D.kappa / P + D.kappa / (1 - P) - 2 * D.M - 4 * D.kappa ≤ D.Ebar + D.tol := by
    have hmin' : D.U y (D.vstar y) ≤ D.U0 y (1 / 2) + 4 * D.kappa := by
      have hhalf : D.U y (1 / 2) = D.U0 y (1 / 2) + 4 * D.kappa := by
        simp only [U]
        norm_num
        ring
      rwa [hhalf] at hmin
    have hg : D.U y P - D.U y (D.vstar y) ≤ D.Ebar + D.tol := by
      change |u ^ 2 - (D.U y P - D.U y (D.vstar y))| ≤ D.tol at hclose
      linarith [(abs_le.mp hclose).1]
    unfold U at hg hmin'
    have hh := (abs_le.mp hosc).1
    simp only [one_div] at hg hmin'
    have hid : D.kappa * (P⁻¹ + (1 - P)⁻¹) = D.kappa / P + D.kappa / (1 - P) := by ring
    rw [hid] at hg
    linarith
  have hh := PlanarGen.radial_barrier_margin (kappa_pos hξ hL) hP.1 hP.2 henergy
  refine ⟨hh.1, ?_⟩
  change P < 1 - D.dP
  have hh2 : D.dP < 1 - P := hh.2
  linarith

lemma XV_barrier {v : ℝ} (hv : v ^ 2 ≤ D.Ebar) : |D.XV v| < 1 / 2 - D.dTh := by
  have hV := D.wellV_hyp y hξ hL hne hb
  have hm : D.XV v ∈ Ioo (-(1 / 2)) (1 / 2) := by
    simpa only [XV, Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using
      Branch2.Planar.Well.X_mem hV v
  have hclose := Branch2.Planar.Well.ft_close hV (D.XV v)
  have hft : D.wellV.ft (D.XV v) = v ^ 2 := Branch2.Planar.Well.ft_X hV v
  rw [hft] at hclose
  have hg : D.V (D.XV v) ≤ D.Ebar + D.tol := by
    have hclose' : |v ^ 2 - (D.V (D.XV v) - D.V 0)| ≤ D.tol := by
      simpa only [Branch2.Planar.Well.g, wellV, zero_add] using hclose
    have hzero : D.V 0 = 0 := by simp [V]
    rw [hzero, sub_zero] at hclose'
    linarith [(abs_le.mp hclose').1]
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have ht : 0 < D.tol := by unfold tol; positivity
  have hn := nu_pos hξ hL
  have hθ : (D.XV v) ^ 2 < 1 / 4 := by nlinarith [hm.1, hm.2]
  have hd : 0 < 1 / 4 - (D.XV v) ^ 2 := by linarith
  unfold V at hg
  have hmul := (div_le_iff₀ hd).mp hg
  let A := D.Ebar + D.tol + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hAn : 0 < A + D.nu := add_pos hA hn
  have hq : (A / (A + D.nu)) * (A + D.nu) = A := div_mul_cancel₀ A hAn.ne'
  have hsq : 4 * (D.XV v) ^ 2 < A / (A + D.nu) := by
    by_contra hc
    have hh := mul_le_mul_of_nonneg_right (not_lt.mp hc) hAn.le
    dsimp [A] at hh hq
    nlinarith
  have hsqrt : 0 ≤ Real.sqrt (A / (A + D.nu)) := Real.sqrt_nonneg _
  have hroot := Real.sq_sqrt (div_pos hA hAn).le
  have hθabs : |D.XV v| < Real.sqrt (A / (A + D.nu)) / 2 := by
    nlinarith [sq_abs (D.XV v), abs_nonneg (D.XV v)]
  unfold dTh
  change |D.XV v| < 1 / 2 - (1 - Real.sqrt (A / (A + D.nu))) / 2
  linarith

omit hξ hL hne hb hbM in
lemma abs_mix_le {s a b A B : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |(1 - s) * a + s * b| ≤ A + B := by
  calc
    _ ≤ |(1 - s) * a| + |s * b| := abs_add_le _ _
    _ = (1 - s) * |a| + s * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg hs.1,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
    _ ≤ |a| + |b| := by
      nlinarith [mul_nonneg hs.1 (abs_nonneg a),
        mul_nonneg (sub_nonneg.mpr hs.2) (abs_nonneg b)]
    _ ≤ A + B := add_le_add ha hb

lemma a0_le_amax_from_pieces : D.a0 y ≤ D.amax := by
  have ha := D.alphaMin_pos_of_pieces y hξ hL hne hb
  have hbound := D.alphaU_bounds y hξ hL hne hb
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left two_pos.le ha hbound.1)

lemma abs_XU_le_one (u : ℝ) : |D.XU y u| ≤ 1 := by
  have hm := D.XU_mem y hξ hL hne hb u
  have hp := (D.vstar_spec y hξ hL hne hb).1
  exact abs_le.mpr ⟨by linarith [hm.1, hp.2], by linarith [hm.2, hp.1]⟩

lemma abs_XV_le_half (v : ℝ) : |D.XV v| ≤ 1 / 2 := by
  have hm : D.XV v ∈ Ioo (-(1 / 2)) (1 / 2) := by
    simpa only [XV, Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using
      Branch2.Planar.Well.X_mem (D.wellV_hyp y hξ hL hne hb) v
  exact abs_le.mpr ⟨hm.1.le, hm.2.le⟩

lemma Fs_coordinate_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {w : ℂ}
    (hw : ‖w‖ ^ 2 ≤ D.Ebar) : |(D.Fs y s w).re| ≤ D.Xbar ∧ |(D.Fs y s w).im| ≤ D.Ybar := by
  have hnorm : ‖w‖ ≤ Real.sqrt D.Ebar := by
    rw [← Real.sqrt_sq (norm_nonneg w)]
    exact Real.sqrt_le_sqrt hw
  have hre := (Complex.abs_re_le_norm w).trans hnorm
  have him := (Complex.abs_im_le_norm w).trans hnorm
  have ha := D.a0_pos_from_pieces y hξ hL hne hb
  have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
  have hlinU : |D.a0 y * w.re| ≤ D.amax * Real.sqrt D.Ebar := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul (D.a0_le_amax_from_pieces y hξ hL hne hb hbM) hre (abs_nonneg _) (Real.sqrt_nonneg _)
  have hlinV : |D.b0 * w.im| ≤ D.b0 * Real.sqrt D.Ebar := by
    rw [abs_mul, abs_of_pos hb0]
    exact mul_le_mul_of_nonneg_left him hb0.le
  have hhU := abs_mix_le hs hlinU (D.abs_XU_le_one y hξ hL hne hb hbM w.re)
  have hhV := abs_mix_le hs hlinV (D.abs_XV_le_half y hξ hL hne hb hbM w.im)
  simpa only [Fs, Xs, Ys, ofReal_re, add_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, zero_mul, zero_add, mul_one, Xbar, Ybar,
    mul_assoc] using And.intro hhU hhV

/-- The normalized coordinates obey the prescribed uniform bounds. -/
theorem fs_coordinate_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    |(D.fs y s z).re| ≤ D.Xbar ∧ |(D.fs y s z).im| ≤ D.Ybar := by
  exact D.Fs_coordinate_bounds y hξ hL hne hb hbM hs
    (D.normalizer_energy y hξ hL hne hb hbM hs hz).le

lemma morse_coordinate_sums {w : ℂ} (hw : ‖w‖ ^ 2 ≤ D.Ebar) :
    |D.a0 y * w.re| + |D.XU y w.re| ≤ D.Xbar ∧
      |D.b0 * w.im| + |D.XV w.im| ≤ D.Ybar := by
  have hnorm : ‖w‖ ≤ Real.sqrt D.Ebar := by
    rw [← Real.sqrt_sq (norm_nonneg w)]
    exact Real.sqrt_le_sqrt hw
  have ha := D.a0_pos_from_pieces y hξ hL hne hb
  have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
  have hu : |D.a0 y * w.re| ≤ D.amax * Real.sqrt D.Ebar := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul (D.a0_le_amax_from_pieces y hξ hL hne hb hbM)
      ((Complex.abs_re_le_norm w).trans hnorm) (abs_nonneg _) (Real.sqrt_nonneg _)
  have hv : |D.b0 * w.im| ≤ D.b0 * Real.sqrt D.Ebar := by
    rw [abs_mul, abs_of_pos hb0]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm w).trans hnorm) hb0.le
  exact ⟨add_le_add hu (D.abs_XU_le_one y hξ hL hne hb hbM _),
    add_le_add hv (D.abs_XV_le_half y hξ hL hne hb hbM _)⟩

lemma Xbar_pos : 0 < D.Xbar := by unfold Xbar amax; positivity
lemma Ybar_pos : 0 < D.Ybar := by
  have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
  unfold Ybar
  positivity

lemma late_Fs_margins {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hlate : 1 - D.ds ≤ s) {w : ℂ}
    (hw : ‖w‖ ^ 2 ≤ D.Ebar) :
    D.dP / 2 < D.vstar y + (D.Fs y s w).re ∧
      D.vstar y + (D.Fs y s w).re < 1 - D.dP / 2 ∧
      |(D.Fs y s w).im| < 1 / 2 - D.dTh / 2 := by
  have hsum := D.morse_coordinate_sums y hξ hL hne hb hbM hw
  have hdiffX : |D.Xs y s w.re - D.XU y w.re| ≤ D.dP / 2 := by
    rw [show D.Xs y s w.re - D.XU y w.re = (1 - s) * (D.a0 y * w.re - D.XU y w.re) by unfold Xs; ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hh := mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans hsum.1) (sub_nonneg.mpr hs.2)
    have hds : D.ds * (2 * D.Xbar) ≤ D.dP := by
      exact (le_div_iff₀ (by have := D.Xbar_pos y hξ hL hne hb hbM; positivity)).mp
        ((min_le_right _ _).trans (min_le_left _ _))
    have hscale := mul_le_mul_of_nonneg_right (show 1 - s ≤ D.ds by linarith)
      (D.Xbar_pos y hξ hL hne hb hbM).le
    linarith
  have hdiffY : |D.Ys s w.im - D.XV w.im| ≤ D.dTh / 2 := by
    rw [show D.Ys s w.im - D.XV w.im = (1 - s) * (D.b0 * w.im - D.XV w.im) by unfold Ys; ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hh := mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans hsum.2) (sub_nonneg.mpr hs.2)
    have hds : D.ds * (2 * D.Ybar) ≤ D.dTh := by
      exact (le_div_iff₀ (by have := D.Ybar_pos y hξ hL hne hb hbM; positivity)).mp
        ((min_le_right _ _).trans (min_le_right _ _))
    have hscale := mul_le_mul_of_nonneg_right (show 1 - s ≤ D.ds by linarith)
      (D.Ybar_pos y hξ hL hne hb hbM).le
    linarith
  have hU := D.XU_barrier y hξ hL hne hb hbM ((Qhat.re_sq_le_normSq w).trans hw)
  have hV := D.XV_barrier y hξ hL hne hb hbM ((Qhat.im_sq_le_normSq w).trans hw)
  have hθ : |D.Ys s w.im| ≤ |D.Ys s w.im - D.XV w.im| + |D.XV w.im| := by
    calc
      _ = |D.Ys s w.im - D.XV w.im + D.XV w.im| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  simp only [Fs, ofReal_re, add_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, zero_mul, zero_add, mul_one]
  exact ⟨by linarith [(abs_le.mp hdiffX).1], by linarith [(abs_le.mp hdiffX).2], by linarith⟩

end SymplecticPacking.HighDim.PlanarGen.Input
