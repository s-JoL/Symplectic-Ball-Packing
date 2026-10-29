import SymplecticPacking.HighDim.Comparator.PlanarInnerFamily
import SymplecticPacking.HighDim.Comparator.PlanarSliceBounds

/-!
# The modified-well area bridge for the endpoint comparison
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
include hξ hL hne hb

lemma ftV_close (θ : ℝ) : |D.wellV.ft θ - D.V θ| ≤ D.tol := by
  have hh := Branch2.Planar.Well.ft_close (D.wellV_hyp y hξ hL hne hb) θ
  simpa only [Branch2.Planar.Well.g, wellV, zero_add, V, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_div, sub_zero] using hh

lemma ftU_nonneg {x : ℝ} (hx : x ∈ Ioo (-(D.vstar y)) (1 - D.vstar y)) : 0 ≤ D.ftU y x := by
  rw [← D.modifiedWell_ft y hξ hL hne hb]
  apply Branch2.Planar.Well.ft_nonneg (D.modifiedWell_hyp y hξ hL hne hb)
  simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, modifiedWell, sub_zero] using hx

/-- Every modified sublevel point is the image of the corresponding energy disc. -/
lemma modified_sublevel_in_image {E : ℝ} (hE : 0 ≤ E) {z : ℂ}
    (hx : z.re ∈ Ioo (-(D.vstar y)) (1 - D.vstar y))
    (hθ : z.im ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (he : D.ftU y z.re + D.wellV.ft z.im ≤ E) :
    z ∈ AreaGate.productMap (D.XU y) D.XV '' Metric.closedBall 0 √E := by
  have hW := D.modifiedWell_hyp y hξ hL hne hb
  have hV := D.wellV_hyp y hξ hL hne hb
  have hsu : D.SigU y z.re ^ 2 = D.ftU y z.re := by
    rw [← D.modifiedWell_Sig y hξ hL hne hb, ← D.modifiedWell_ft y hξ hL hne hb]
    exact Branch2.Planar.Well.Sig_sq hW (by
      simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, modifiedWell, sub_zero] using hx)
  have hsv : D.wellV.Sig z.im ^ 2 = D.wellV.ft z.im :=
    Branch2.Planar.Well.Sig_sq hV (by
      simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using hθ)
  let w : ℂ := (D.SigU y z.re : ℂ) + (D.wellV.Sig z.im : ℂ) * I
  have hnorm : ‖w‖ ^ 2 ≤ E := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    dsimp [w]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    nlinarith [hsu, hsv]
  refine ⟨w, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (by rwa [Real.sq_sqrt hE])
  · apply Complex.ext
    · simpa [AreaGate.productMap, w] using D.XU_SigU y hξ hL hne hb hx
    · simpa [AreaGate.productMap, w, XV] using Branch2.Planar.Well.X_Sig hV (by
        simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using hθ)

/-- The original and modified energy sums differ by at most twice the prescribed tolerance. -/
lemma modified_energy_close (P θ : ℝ) :
    |D.ftU y (P - D.vstar y) + D.wellV.ft θ -
      (D.U y P - D.U y (D.vstar y) + D.V θ)| ≤ 2 * D.tol := by
  have hu := D.ftU_close y hξ hL hne hb (P - D.vstar y)
  have hv := D.ftV_close y hξ hL hne hb θ
  have heq : D.ftU y (P - D.vstar y) + D.wellV.ft θ -
      (D.U y P - D.U y (D.vstar y) + D.V θ) =
      (D.ftU y (P - D.vstar y) - D.gU y (P - D.vstar y)) + (D.wellV.ft θ - D.V θ) := by
    unfold gU
    simp only [add_sub_cancel]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- Area at the comparison level strictly exceeds the source capacity. -/
theorem core_area {I : ℝ} (hI0 : 0 ≤ I) (hI : I ≤ 1 - 4 * D.eta) :
    I < Inner.Acal (D.Js y) 1
      (Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) + 2 * D.sig - D.U y (D.vstar y) + 2 * D.tol) := by
  let T := D.scalarInput y
  have hT := D.scalarInput_hyp y hξ hL hne hb
  have hη : 0 < D.eta := eta_pos hξ hL
  have hη1 : D.eta ≤ 1 / 32 := D.eta_le
  have hb0 : 0 < D.beta := by unfold beta; positivity
  have hb1 : D.beta < 1 / 2 := by unfold beta; linarith
  have hsig : 0 < D.sig := by unfold sig; positivity
  have hTη : T.eta = D.eta := rfl
  have hTβ : T.betaY = D.beta := by
    change T.eta / (8 * 1) = D.eta / 8
    rw [hTη, mul_one]
  have hTs : T.sigma = D.sig := rfl
  have hJ : I + 3 * D.eta ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨α, hα, hF⟩ := Branch2.Cmp.rearr_sublevel hT.F_cont hT.F_convex hJ
  change α ∈ Icc 0 (1 - (I + 3 * D.eta)) at hα
  let a := max α D.eta
  have haα : α ≤ a := le_max_left _ _
  have haη : D.eta ≤ a := le_max_right _ _
  have hau : a ≤ α + 2 * D.eta := max_le (by linarith) (by linarith [hα.1])
  have hah : a + (I + D.eta) ≤ 1 - D.eta := by
    rcases le_total α D.eta with h | h
    · rw [show a = D.eta from max_eq_right h]
      linarith
    · rw [show a = α from max_eq_left h]
      linarith [hα.2]
  let E := Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) + 2 * D.sig - D.U y (D.vstar y) + 2 * D.tol
  have hmod {P θ : ℝ} (hP : P ∈ Icc a (a + (I + D.eta))) (hθ : |θ| ≤ 1 / 2 - D.beta) :
      D.ftU y (P - D.vstar y) + D.wellV.ft θ ≤ E := by
    have hU := hT.U_le_F (P := P) (show P ∈ Icc T.eta (T.h - T.eta) from
      ⟨by rw [hTη]; linarith [hP.1], by change P ≤ 1 - T.eta; rw [hTη]; linarith [hP.2]⟩)
    have hV := hT.V_le (y := θ) (by rwa [hTβ])
    have hFx := hF P (show P ∈ Icc α (α + (I + 3 * D.eta)) from
      ⟨by linarith [hP.1], by linarith [hP.2]⟩)
    have hcl := (abs_le.mp (D.modified_energy_close y hξ hL hne hb P θ)).2
    rw [scalarInput_U] at hU
    rw [scalarInput_V] at hV
    change D.U y P ≤ D.U0 y P + 0 + T.sigma / 4 at hU
    change D.U0 y P ≤ Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) at hFx
    rw [hTs] at hU hV
    dsimp [E]
    linarith
  have hE : 0 ≤ E := by
    have hx : a - D.vstar y ∈ Ioo (-(D.vstar y)) (1 - D.vstar y) :=
      ⟨by linarith, by linarith [hah]⟩
    have hh := hmod (P := a) (θ := 0) ⟨le_rfl, by linarith⟩ (by rw [abs_zero]; linarith)
    have hz : D.wellV.ft 0 = 0 := Branch2.Planar.Well.ft_zero (D.wellV_hyp y hξ hL hne hb)
    rw [hz, add_zero] at hh
    exact (D.ftU_nonneg y hξ hL hne hb hx).trans hh
  have hrect : AreaGate.rectangle (a - D.vstar y) (a + (I + D.eta) - D.vstar y)
      (-(1 / 2 - D.beta)) (1 / 2 - D.beta) ⊆
      AreaGate.productMap (D.XU y) D.XV '' Metric.closedBall 0 √E := by
    intro z hz
    change z.re ∈ Icc (a - D.vstar y) (a + (I + D.eta) - D.vstar y) ∧
      z.im ∈ Icc (-(1 / 2 - D.beta)) (1 / 2 - D.beta) at hz
    apply D.modified_sublevel_in_image y hξ hL hne hb hE
    · constructor <;> linarith [hz.1.1, hz.1.2, hah]
    · constructor <;> linarith [hz.2.1, hz.2.2]
    · have hh := hmod (P := z.re + D.vstar y) (θ := z.im)
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩ (abs_le.mpr hz.2)
      simpa only [add_sub_cancel_right] using hh
  have harea := AreaGate.rectangle_le_acal (D.XU_smooth y hξ hL hne hb)
    (D.XV_smooth y hξ hL hne hb) (D.XU_deriv_pos y hξ hL hne hb)
    (Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb))
    (by linarith : a - D.vstar y ≤ a + (I + D.eta) - D.vstar y)
    (by linarith : -(1 / 2 - D.beta) ≤ 1 / 2 - D.beta) hE hrect
  have hlt : I < (I + D.eta) * (1 - 2 * D.beta) := by
    have hβ : 2 * D.beta = D.eta / 4 := by unfold beta; ring
    have hh := mul_le_mul_of_nonneg_left (show I + D.eta ≤ 1 by linarith) (by linarith : 0 ≤ 2 * D.beta)
    nlinarith
  apply hlt.trans_le
  rw [show a + (I + D.eta) - D.vstar y - (a - D.vstar y) = I + D.eta by ring,
    show 1 / 2 - D.beta - -(1 / 2 - D.beta) = 1 - 2 * D.beta by ring] at harea
  simpa only [Js, sub_self, zero_mul, one_mul, zero_add, Inner.Acal, Inner.Jbar, E] using harea

variable (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
include hbM

/-- Endpoint error for the smoothed profile; no properness of the bounded Morse coordinates is assumed. -/
theorem core_comparison {z : ℂ} (hz : Real.pi * ‖z‖ ^ 2 ≤ 1 - 8 * D.eta) :
    D.U0 y (Real.pi * ‖D.qin y 1 z‖ ^ 2) <
      Branch2.Cmp.rearr 1 (D.U0 y) (Real.pi * ‖z‖ ^ 2) + 23 * D.xi / 64 := by
  let I := Real.pi * ‖z‖ ^ 2
  have hI0 : 0 ≤ I := by dsimp [I]; positivity
  have hη := eta_pos hξ hL
  have hη1 : D.eta ≤ 1 / 32 := D.eta_le
  have hsrc : I < D.pdag := by unfold pdag; linarith
  have hs : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  let w := Inner.TrotInv (D.Js y) 1 (Inner.Darea (D.Js y) 1 z)
  let P := D.vstar y + D.XU y w.re
  let θ := D.XV w.im
  let E := Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) + 2 * D.sig - D.U y (D.vstar y) + 2 * D.tol
  have hroot : Inner.Acal (D.Js y) 1 (‖w‖ ^ 2) = I :=
    D.normalizer_area y hξ hL hne hb hbM hs hsrc
  have harea := D.core_area y hξ hL hne hb hI0 (by linarith : I ≤ 1 - 4 * D.eta)
  have hE : ‖w‖ ^ 2 < E := by
    apply (DensityExtension.acal_strictMono (D.Js_slice_continuous y hξ hL hne hb 1)
      (D.Js_pos y hξ hL hne hb hs)).lt_iff_lt.mp
    rw [hroot]
    exact harea
  have hX := D.XU_mem y hξ hL hne hb w.re
  have hP : P ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [P]; linarith [hX.1], by dsimp [P]; linarith [hX.2]⟩
  have hθ : θ ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [θ, XV, Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, wellV, sub_zero] using
      Branch2.Planar.Well.X_mem (D.wellV_hyp y hξ hL hne hb) w.im
  have hV0 : 0 ≤ D.V θ := by
    have hden : 0 < 1 / 4 - θ ^ 2 := by nlinarith [hθ.1, hθ.2]
    unfold V
    have hn := nu_pos hξ hL
    positivity
  have hU0 : D.U0 y P ≤ D.U y P := by
    unfold U
    have hk := kappa_pos hξ hL
    have hP0 := hP.1
    have hP1 : 0 < 1 - P := sub_pos.mpr hP.2
    have hh : 0 ≤ D.kappa * (1 / P + 1 / (1 - P)) := by positivity
    linarith
  have hclose := (abs_le.mp (D.modified_energy_close y hξ hL hne hb P θ)).1
  have hsum : D.ftU y (P - D.vstar y) + D.wellV.ft θ = ‖w‖ ^ 2 := by
    dsimp [P, θ]
    rw [add_sub_cancel_left, D.ftU_XU y hξ hL hne hb]
    have hv : D.wellV.ft (D.XV w.im) = w.im ^ 2 :=
      Branch2.Planar.Well.ft_X (D.wellV_hyp y hξ hL hne hb) w.im
    rw [hv, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsum] at hclose
  have hrec : D.U0 y P < Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) + 2 * D.sig + 4 * D.tol := by
    dsimp [E] at hE
    linarith
  have hT := D.scalarInput_hyp y hξ hL hne hb
  have hJ : I + 3 * D.eta ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hIcc : I ∈ Icc (0 : ℝ) 1 := ⟨hI0, by linarith⟩
  have hlip := Branch2.Cmp.rearr_lipschitz hT.F_cont hL hT.F_lip (I + 3 * D.eta) hJ I hIcc
  have hLη : D.L * D.eta ≤ D.xi / 64 := hT.L_mul_eta
  change |Branch2.Cmp.rearr 1 (D.U0 y) (I + 3 * D.eta) - Branch2.Cmp.rearr 1 (D.U0 y) I| ≤
    D.L * |I + 3 * D.eta - I| at hlip
  rw [show I + 3 * D.eta - I = 3 * D.eta by ring, abs_of_pos (by positivity : 0 < 3 * D.eta)] at hlip
  have hmoment : Real.pi * ‖D.qin y 1 z‖ ^ 2 = P := by
    rw [D.qin_one y hξ hL hne hb hbM hsrc]
    have hFs : (D.fs y 1 z).re = D.XU y w.re := by simp [fs, Fs, Xs, Ys, w]
    rw [Branch2.Planar.chart_moment (by rw [hFs]; exact hP.1.le), hFs]
  rw [hmoment]
  dsimp [sig, tol] at hrec
  linarith [(abs_le.mp hlip).2]

end SymplecticPacking.HighDim.PlanarGen.Input
