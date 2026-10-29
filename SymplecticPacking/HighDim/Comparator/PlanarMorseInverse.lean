import SymplecticPacking.HighDim.Comparator.PlanarModification

/-!
# The signed Morse inverse for the prescribed uniform modification

We apply the generic well theorem to the already modified potential with a
smaller auxiliary tolerance. The auxiliary second modification is identically
zero, since its support lies inside the original exactly quadratic interval.
Thus its inverse is exactly `Input.XU`, with no change to the construction.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.Input

open Set Filter Topology
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)

/-- An auxiliary well whose modification will vanish identically. -/
def modifiedWell : Branch2.Planar.Well :=
  ⟨D.ftU y, -(D.vstar y), 1 - D.vstar y, 0, D.alphaU y * D.epsU ^ 2 / 4⟩

variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
include hξ hL hne hb

lemma ftU_quadratic_germ : D.ftU y =ᶠ[𝓝 0] fun x => D.alphaU y * x ^ 2 / 2 := by
  have he := D.epsU_pos y hξ hL hne hb
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
    (show |(0 : ℝ)| < D.epsU by simpa using he)] with x hx
  exact D.ftU_eq_quad y hξ hL hne hb hx.le

lemma ftU_second_zero : deriv (deriv (D.ftU y)) 0 = D.alphaU y := by
  rw [(D.ftU_quadratic_germ y hξ hL hne hb).deriv.deriv_eq]
  have he : deriv (fun x : ℝ => D.alphaU y * x ^ 2 / 2) = fun x => D.alphaU y * x := by
    funext x
    have hh := (((hasDerivAt_id x).pow 2).const_mul (D.alphaU y)).div_const 2
    change HasDerivAt (fun t : ℝ => D.alphaU y * t ^ 2 / 2) _ x at hh
    rw [hh.deriv]
    simp
    ring
  rw [he]
  simp

lemma ftU_proper :
    Tendsto (D.ftU y) (𝓝[>] (-(D.vstar y))) atTop ∧
    Tendsto (D.ftU y) (𝓝[<] (1 - D.vstar y)) atTop := by
  have hu := (D.scalarInput_hyp y hξ hL hne hb).U_proper
  rw [scalarInput_U] at hu
  have hl : Tendsto (fun x => D.vstar y + x) (𝓝[>] (-(D.vstar y))) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hh := (show Continuous (fun x : ℝ => D.vstar y + x) from
        continuous_const.add continuous_id).tendsto (-(D.vstar y))
      simpa using hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < D.vstar y + x
      change -(D.vstar y) < x at hx
      linarith
  have hr : Tendsto (fun x => D.vstar y + x) (𝓝[<] (1 - D.vstar y)) (𝓝[<] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hh := (show Continuous (fun x : ℝ => D.vstar y + x) from
        continuous_const.add continuous_id).tendsto (1 - D.vstar y)
      simpa using hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change D.vstar y + x < 1
      change x < 1 - D.vstar y at hx
      linarith
  have hbound : ∀ x, D.gU y x - D.tol ≤ D.ftU y x := fun x => by
    have hh := (abs_le.mp (D.ftU_close y hξ hL hne hb x)).1
    linarith
  constructor
  · apply tendsto_atTop_mono hbound
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ (hu.1.comp hl))
  · apply tendsto_atTop_mono hbound
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ (hu.2.comp hr))

lemma modifiedWell_hyp : (D.modifiedWell y).Hyp where
  A_lt := by have hh := (D.vstar_spec y hξ hL hne hb).1.1; change -(D.vstar y) < 0; linarith
  lt_B := by have hh := (D.vstar_spec y hξ hL hne hb).1.2; change 0 < 1 - D.vstar y; linarith
  δ_pos := by
    have he := D.epsU_pos y hξ hL hne hb
    have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1
    change 0 < D.alphaU y * D.epsU ^ 2 / 4
    positivity
  smooth := D.ftU_contDiffOn y hξ hL hne hb
  crit := by
    change deriv (D.ftU y) 0 = 0
    rw [(D.ftU_quadratic_germ y hξ hL hne hb).deriv_eq]
    simp
  sign := by
    intro x hx hx0
    change 0 < (x - 0) * deriv (D.ftU y) x
    rw [sub_zero]
    exact D.ftU_mono y hξ hL hne hb hx hx0
  second := by
    change 0 < deriv (deriv (D.ftU y)) 0
    rw [D.ftU_second_zero y hξ hL hne hb]
    exact (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1
  top := (D.ftU_proper y hξ hL hne hb).2
  bot := (D.ftU_proper y hξ hL hne hb).1

lemma modifiedWell_alpha : (D.modifiedWell y).alpha = D.alphaU y :=
  D.ftU_second_zero y hξ hL hne hb

lemma modifiedWell_g (x : ℝ) : (D.modifiedWell y).g x = D.ftU y x := by
  change D.ftU y (0 + x) - D.ftU y 0 = D.ftU y x
  rw [zero_add, D.ftU_zero y hξ hL hne hb, sub_zero]

lemma modifiedWell_eps : (D.modifiedWell y).eps ≤ D.epsU / 2 := by
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1
  have he := D.epsU_pos y hξ hL hne hb
  have heq : (D.modifiedWell y).δ / D.alphaU y = (D.epsU / 2) ^ 2 := by
    change (D.alphaU y * D.epsU ^ 2 / 4) / D.alphaU y = _
    field_simp
    <;> ring
  calc (D.modifiedWell y).eps ≤ Real.sqrt ((D.modifiedWell y).δ / (D.modifiedWell y).alpha) :=
      min_le_right _ _
    _ = D.epsU / 2 := by rw [D.modifiedWell_alpha y hξ hL hne hb, heq, Real.sqrt_sq (half_pos he).le]

/-- The auxiliary second modification is exactly the originally prescribed one. -/
lemma modifiedWell_ft (x : ℝ) : (D.modifiedWell y).ft x = D.ftU y x := by
  let W := D.modifiedWell y
  have hW := D.modifiedWell_hyp y hξ hL hne hb
  rcases le_or_gt (2 * W.eps) |x| with hx | hx
  · exact (Branch2.Planar.Well.ft_eq_far hW hx).trans (D.modifiedWell_g y hξ hL hne hb x)
  · have hxr : |x| ≤ W.r0 := by
      have hh := Branch2.Planar.Well.eps_le_r0 hW
      have hp := Branch2.Planar.Well.r0_pos hW
      linarith
    have hxe : |x| ≤ D.epsU := by
      have hh := D.modifiedWell_eps y hξ hL hne hb
      change W.eps ≤ D.epsU / 2 at hh
      linarith
    change W.g x + Inner.psiR (x / W.eps) * (W.alpha * x ^ 2 / 2 - W.gg x) = _
    rw [Branch2.Planar.Well.gg_eq hW hxr, D.modifiedWell_g y hξ hL hne hb,
      D.modifiedWell_alpha y hξ hL hne hb, D.ftU_eq_quad y hξ hL hne hb hxe]
    ring

lemma modifiedWell_Sig : (D.modifiedWell y).Sig = D.SigU y := by
  funext x
  change Real.sign x * Real.sqrt ((D.modifiedWell y).ft x) = Real.sign x * Real.sqrt (D.ftU y x)
  rw [D.modifiedWell_ft y hξ hL hne hb]

lemma modifiedWell_theta : (D.modifiedWell y).theta = D.thetaU y := by
  funext t
  unfold Branch2.Planar.Well.theta Branch2.Planar.Well.lo Branch2.Planar.Well.hi modifiedWell thetaU
  ring

lemma modifiedWell_G : (D.modifiedWell y).G = fun t => D.SigU y (D.thetaU y t) := by
  unfold Branch2.Planar.Well.G
  rw [D.modifiedWell_Sig y hξ hL hne hb, D.modifiedWell_theta y hξ hL hne hb]

lemma modifiedWell_X : (D.modifiedWell y).X = D.XU y := by
  unfold Branch2.Planar.Well.X XU
  rw [D.modifiedWell_theta y hξ hL hne hb]
  have hG : (D.modifiedWell y).G = fun t => D.SigU y (D.thetaU y t) := by
    unfold Branch2.Planar.Well.G
    rw [D.modifiedWell_Sig y hξ hL hne hb, D.modifiedWell_theta y hξ hL hne hb]
  rw [hG]

theorem XU_smooth : ContDiff ℝ ∞ (D.XU y) := by
  rw [← D.modifiedWell_X y hξ hL hne hb]
  exact Branch2.Planar.Well.X_smooth (D.modifiedWell_hyp y hξ hL hne hb)

theorem XU_deriv_pos (u : ℝ) : 0 < deriv (D.XU y) u := by
  rw [← D.modifiedWell_X y hξ hL hne hb]
  exact Branch2.Planar.Well.X_deriv_pos (D.modifiedWell_hyp y hξ hL hne hb) u

theorem XU_mem (u : ℝ) : D.XU y u ∈ Ioo (-(D.vstar y)) (1 - D.vstar y) := by
  rw [← D.modifiedWell_X y hξ hL hne hb]
  simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, modifiedWell, sub_zero] using
    Branch2.Planar.Well.X_mem (D.modifiedWell_hyp y hξ hL hne hb) u

theorem ftU_XU (u : ℝ) : D.ftU y (D.XU y u) = u ^ 2 := by
  rw [← D.modifiedWell_X y hξ hL hne hb, ← D.modifiedWell_ft y hξ hL hne hb]
  exact Branch2.Planar.Well.ft_X (D.modifiedWell_hyp y hξ hL hne hb) u

theorem XU_SigU {x : ℝ} (hx : x ∈ Ioo (-(D.vstar y)) (1 - D.vstar y)) :
    D.XU y (D.SigU y x) = x := by
  rw [← D.modifiedWell_X y hξ hL hne hb, ← D.modifiedWell_Sig y hξ hL hne hb]
  apply Branch2.Planar.Well.X_Sig (D.modifiedWell_hyp y hξ hL hne hb)
  simpa only [Branch2.Planar.Well.lo, Branch2.Planar.Well.hi, modifiedWell, sub_zero] using hx

theorem SigU_linear {x : ℝ} (hx : |x| ≤ D.epsU) :
    D.SigU y x = Real.sqrt (D.alphaU y / 2) * x := by
  unfold SigU
  rw [D.ftU_eq_quad y hξ hL hne hb hx,
    show D.alphaU y * x ^ 2 / 2 = D.alphaU y / 2 * x ^ 2 by ring,
    Real.sqrt_mul (by
      have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1
      positivity), Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- The inverse is linear on the original uniform quadratic interval. -/
theorem XU_linear {u : ℝ} (hu : |u| ≤ Real.sqrt (D.alphaU y / 2) * D.epsU) :
    D.XU y u = u / Real.sqrt (D.alphaU y / 2) := by
  have ha := (D.alphaMin_pos_of_pieces y hξ hL hne hb).trans_le (D.alphaU_bounds y hξ hL hne hb).1
  have hl : 0 < Real.sqrt (D.alphaU y / 2) := Real.sqrt_pos.mpr (by positivity)
  have hx : |u / Real.sqrt (D.alphaU y / 2)| ≤ D.epsU := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]
    linarith
  have hr := D.vstar_uniform_bounds y hξ hL hne hb
  have he := D.epsU_le_r0 y hξ hL hne hb
  have hp := r0_pos hξ hL
  have hx' := abs_le.mp hx
  have hm : u / Real.sqrt (D.alphaU y / 2) ∈ Ioo (-(D.vstar y)) (1 - D.vstar y) := by
    constructor <;> linarith [hr.1, hr.2]
  have hh := D.XU_SigU y hξ hL hne hb hm
  rw [D.SigU_linear y hξ hL hne hb hx] at hh
  have hid : Real.sqrt (D.alphaU y / 2) * (u / Real.sqrt (D.alphaU y / 2)) = u := by field_simp
  rwa [hid] at hh

end SymplecticPacking.HighDim.PlanarGen.Input
