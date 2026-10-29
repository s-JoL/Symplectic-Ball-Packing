import SymplecticPacking.HighDim.Comparator.PlanarSliceBounds
import SymplecticPacking.HighDim.Comparator.PlanarMorseInverse

/-!
# Joint smoothness of the prescribed Morse data
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Filter Topology
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m q : ℕ} (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    {ell : Moments m → ℝ} (hell : ContDiff ℝ ∞ ell) (Lν : Fin q → Moments m → ℝ)
    {R η₀ ξ : ℝ} (hR : 0 ≤ R) (hξ : 0 < ξ)

local notation "D" => sliceInput Δ F j ell Lν R η₀ ξ
include hF hell hR hξ

lemma slice_critical_spec (y : Moments m) :
    (D).vstar y ∈ Ioo (0 : ℝ) 1 ∧ deriv ((D).U y) ((D).vstar y) = 0 :=
  (D).vstar_spec_basic y hξ (sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ)
    (sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y)

lemma slice_alphaU_pos (y : Moments m) : 0 < (D).alphaU y :=
  (D).U_second_pos_basic y hξ (sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ)
    (sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y)
    (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1

/-- Joint smoothness of the quadratic coefficient of the radial well. -/
theorem sliceInput_alphaU_smooth : ContDiff ℝ ∞ (D).alphaU := by
  have hv := sliceInput_vstar_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hu := sliceInput_U0_joint_smooth Δ hF j hell Lν R η₀ ξ
  have hd := joint_partial_deriv (f := (D).U0) hu
  have hdd := joint_partial_deriv (f := fun y v => deriv ((D).U0 y) v) hd
  have h0 := hdd.comp (contDiff_id.prodMk hv)
  have h1 : ContDiff ℝ ∞ (fun y => ((D).vstar y ^ 3)⁻¹) :=
    (hv.pow 3).inv (fun y => pow_ne_zero 3 (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1.1.ne')
  have h2 : ContDiff ℝ ∞ (fun y => ((1 - (D).vstar y) ^ 3)⁻¹) :=
    ((contDiff_const.sub hv).pow 3).inv (fun y => pow_ne_zero 3
      (sub_pos.mpr (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1.2).ne')
  have hs : ContDiff ℝ ∞ (fun y => deriv (deriv ((D).U0 y)) ((D).vstar y) +
      2 * (D).kappa * (((D).vstar y ^ 3)⁻¹ + ((1 - (D).vstar y) ^ 3)⁻¹)) :=
    h0.add (contDiff_const.mul (h1.add h2))
  convert hs using 1
  funext y
  exact (D).U_second_formula_basic y hξ (sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ)
    (sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y)
    (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1

lemma slice_U_joint {y : Moments m} {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (D).U p.1 p.2) (y, v) := by
  have h0 := (sliceInput_U0_joint_smooth Δ hF j hell Lν R η₀ ξ).contDiffAt (x := (y, v))
  have h1 : ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => 1 / p.2) (y, v) :=
    contDiffAt_const.div contDiffAt_snd hv.1.ne'
  have h2 : ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => 1 / (1 - p.2)) (y, v) :=
    contDiffAt_const.div (contDiffAt_const.sub contDiffAt_snd) (sub_pos.mpr hv.2).ne'
  exact h0.add (contDiffAt_const.mul (h1.add h2))

lemma slice_gU_joint {y : Moments m} {x : ℝ} (hx : (D).vstar y + x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (D).gU p.1 p.2) (y, x) := by
  have hv := sliceInput_vstar_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have h1 := (slice_U_joint (η₀ := η₀) Δ hF j hell Lν hR hξ hx).comp (y, x)
    (contDiffAt_fst.prodMk ((hv.contDiffAt.comp _ contDiffAt_fst).add contDiffAt_snd))
  have h2 := (slice_U_joint (η₀ := η₀) Δ hF j hell Lν hR hξ (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1).comp (y, x)
    (contDiffAt_fst.prodMk (hv.contDiffAt.comp _ contDiffAt_fst))
  exact h1.sub h2

lemma slice_ftU_joint {y : Moments m} {x : ℝ} (hx : (D).vstar y + x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (D).ftU p.1 p.2) (y, x) := by
  have hg := slice_gU_joint (η₀ := η₀) Δ hF j hell Lν hR hξ hx
  have hα := (sliceInput_alphaU_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).contDiffAt.comp (y, x) contDiffAt_fst
  have hψ := Inner.psiR_contDiff.contDiffAt.comp (y, x) (contDiffAt_snd.div_const (D).epsU)
  exact hg.add (hψ.mul (((hα.mul (contDiffAt_snd.pow 2)).div_const 2).sub hg))

lemma slice_thetaU_joint : ContDiff ℝ ∞ (fun p : Moments m × ℝ => (D).thetaU p.1 p.2) := by
  have hv := sliceInput_vstar_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hs : ContDiff ℝ ∞ (fun t : ℝ => t / Real.sqrt (1 + t ^ 2)) := by
    apply contDiff_id.div
    · exact (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun t => by positivity)
    · intro t
      exact (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + t ^ 2)).ne'
  exact ((contDiff_const.sub (contDiff_const.mul (hv.comp contDiff_fst))).div_const 2).add
    (contDiff_const.mul (hs.comp contDiff_snd))

lemma slice_ftU_pos {y : Moments m} {x : ℝ}
    (hb : ∀ p ∈ (D).pieces y, |p.2| ≤ (D).L) (hx : (D).vstar y + x ∈ Ioo (0 : ℝ) 1) (hx0 : x ≠ 0) :
    0 < (D).ftU y x := by
  have hL := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  have hW := (D).modifiedWell_hyp y hξ hL hn hb
  have hm : x ∈ Ioo ((D).modifiedWell y).lo ((D).modifiedWell y).hi := by
    change x ∈ Ioo (-((D).vstar y) - 0) (1 - (D).vstar y - 0)
    constructor <;> linarith [hx.1, hx.2]
  have hp := Branch2.Planar.Well.ft_pos hW hm hx0
  rwa [(D).modifiedWell_ft y hξ hL hn hb] at hp

lemma slice_SigU_linear_basic {y : Moments m} {x : ℝ} (he : 0 < (D).epsU) (hx : |x| ≤ (D).epsU) :
    (D).SigU y x = Real.sqrt ((D).alphaU y / 2) * x := by
  have hψ := Inner.psiR_eq_one (t := x / (D).epsU)
    (by rw [abs_div, abs_of_pos he, div_le_one he]; exact hx)
  have hft : (D).ftU y x = (D).alphaU y * x ^ 2 / 2 := by
    unfold Input.ftU Input.gcU
    rw [hψ]
    ring
  have ha := slice_alphaU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  change Real.sign x * Real.sqrt ((D).ftU y x) = _
  rw [hft, show (D).alphaU y * x ^ 2 / 2 = (D).alphaU y / 2 * x ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- The signed Morse chart is smooth jointly with the moment parameters, including at its zero. -/
theorem slice_SigU_joint {y : Moments m} {x : ℝ}
    (hb : ∀ p ∈ (D).pieces y, |p.2| ≤ (D).L) (hx : (D).vstar y + x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (D).SigU p.1 p.2) (y, x) := by
  have hL := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  by_cases hx0 : x = 0
  · subst x
    have he := (D).epsU_pos y hξ hL hn hb
    have hα := sliceInput_alphaU_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
    have hs : ContDiff ℝ ∞ (fun p : Moments m × ℝ => Real.sqrt ((D).alphaU p.1 / 2) * p.2) :=
      (((hα.comp contDiff_fst).div_const 2).sqrt
        (fun p => (div_pos (slice_alphaU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ p.1) two_pos).ne')).mul contDiff_snd
    apply hs.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(continuous_abs.comp continuous_snd).continuousAt.preimage_mem_nhds
      (gt_mem_nhds (show |(0 : ℝ)| < (D).epsU by simpa using he))] with p hp
    exact slice_SigU_linear_basic (η₀ := η₀) Δ hF j hell Lν hR hξ he hp.le
  · have hft := slice_ftU_joint (η₀ := η₀) Δ hF j hell Lν hR hξ hx
    have hp := slice_ftU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ hb hx hx0
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · apply (hft.sqrt hp.ne').neg.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (gt_mem_nhds hxneg)] with p hp'
      simp only [Input.SigU, Real.sign_of_neg hp', neg_one_mul]
    · apply (hft.sqrt hp.ne').congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (lt_mem_nhds hxpos)] with p hp'
      simp only [Input.SigU, Real.sign_of_pos hp', one_mul]

lemma slice_G_joint {y : Moments m} (hb : ∀ p ∈ (D).pieces y, |p.2| ≤ (D).L) (t : ℝ) :
    ContDiffAt ℝ ∞ (fun p : Moments m × ℝ => (D).SigU p.1 ((D).thetaU p.1 p.2)) (y, t) := by
  have hL := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  have hm := Branch2.Planar.Well.theta_mem ((D).modifiedWell_hyp y hξ hL hn hb) t
  rw [(D).modifiedWell_theta y hξ hL hn hb] at hm
  change (D).thetaU y t ∈ Ioo (-((D).vstar y) - 0) (1 - (D).vstar y - 0) at hm
  have hs := slice_SigU_joint (η₀ := η₀) Δ hF j hell Lν hR hξ hb
    (show (D).vstar y + (D).thetaU y t ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hm.1, hm.2])
  exact hs.comp (y, t) (contDiffAt_fst.prodMk (slice_thetaU_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).contDiffAt)

/-- Joint smoothness of the signed inverse on any open parameter region satisfying
the verified finite slope inequalities. -/
theorem slice_XU_joint_on {U : Set (Moments m)} (hU : IsOpen U)
    (hb : ∀ y ∈ U, ∀ p ∈ (D).pieces y, |p.2| ≤ (D).L) :
    ContDiffOn ℝ ∞ (fun p : Moments m × ℝ => (D).XU p.1 p.2) (U ×ˢ univ) := by
  let G : Moments m → ℝ → ℝ := fun y t => (D).SigU y ((D).thetaU y t)
  have hL := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn : ∀ y, (D).pieces y ≠ [] := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ
  have hW : ∀ y ∈ U, ((D).modifiedWell y).Hyp :=
    fun y hy => (D).modifiedWell_hyp y hξ hL (hn y) (hb y hy)
  have hG : ∀ y ∈ U, ((D).modifiedWell y).G = G y :=
    fun y hy => (D).modifiedWell_G y hξ hL (hn y) (hb y hy)
  have hs : ContDiffOn ℝ ∞ (fun p : Moments m × ℝ => Inner.invR (G p.1) p.2) (U ×ˢ univ) := by
    apply invR_joint_smooth hU
    · intro y hy t
      exact slice_G_joint (η₀ := η₀) Δ hF j hell Lν hR hξ (hb y hy) t
    · intro y hy
      rw [← hG y hy]
      exact (Branch2.Planar.Well.G_strictMono (hW y hy)).injective
    · intro y hy
      rw [← hG y hy]
      exact Inner.surjective_of_proper (Branch2.Planar.Well.G_contDiff (hW y hy)).continuous
        (Branch2.Planar.Well.G_top (hW y hy)) (Branch2.Planar.Well.G_bot (hW y hy))
    · intro y hy t
      rw [← hG y hy]
      exact (Branch2.Planar.Well.G_deriv_pos (hW y hy) t).ne'
  have ht := (slice_thetaU_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).contDiffOn.comp
    (contDiffOn_fst.prodMk hs) (fun _ _ => mem_univ _)
  exact ht

end SymplecticPacking.HighDim.PlanarGen
