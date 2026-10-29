import OAI.Geometry.BallPacking.Annuli.QuadricNormalizedCycle
import SymplecticPacking.BranchSmall.HandleChartCertificates

/-!
# The annular dual form on the affine quadric curve

The fixed width `ε=1/8` defines the radial transition on the native annular sheet.
The closed annulus of width `1/4` lies in that sheet by an elementary rational
bound on the displayed quadratic branch expression. The resulting one-form is
smooth, compactly supported, closed, and has period one.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set Function Manifold
open scoped ContDiff Manifold Topology
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

variable (m : ℕ)

/-! ### The explicit annulus width -/

theorem planeClosedAnnulus_mono {ε ε' : ℝ} (h : ε' ≤ ε) :
    planeClosedAnnulus ε' ⊆ planeClosedAnnulus ε := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The fixed rational half-width of the annular differential. -/
def explicitAnnulusWidth (_m : ℕ) : ℝ := 1 / 8

theorem explicitAnnulusWidth_pos : 0 < explicitAnnulusWidth m := by
  norm_num [explicitAnnulusWidth]

theorem explicitAnnulusWidth_le : explicitAnnulusWidth m ≤ 1 / 8 := by
  norm_num [explicitAnnulusWidth]

theorem explicitAnnulusWidth_lt : explicitAnnulusWidth m < 1 / 2 := by
  norm_num [explicitAnnulusWidth]

theorem explicitAnnulusWidth_lt_one : explicitAnnulusWidth m < 1 := by
  norm_num [explicitAnnulusWidth]

theorem explicitAnnulusWidth_subset :
    planeClosedAnnulus (explicitAnnulusWidth m) ⊆ (annulusDiffeomorph m).source := by
  intro z hz
  rw [annulusDiffeomorph_source]
  exact annulus_quarter_native m
    (planeClosedAnnulus_mono (show explicitAnnulusWidth m ≤ 1 / 4 by norm_num [explicitAnnulusWidth]) hz)

/-! ### The explicit dual form -/

local notation "εm" => explicitAnnulusWidth m

/-- **The explicit compactly supported dual form** `β_m`. -/
def explicitDualForm : ManifoldOneForm RealModel (Surface m) :=
  handlePushforwardOneForm (annulusDiffeomorph m)
    (manifoldScalarDifferential (planeRadialStep εm))

theorem explicitDualForm_smooth : SmoothOneFormFamily (fun _ : ℝ => explicitDualForm m) := by
  apply handlePushforwardOneForm_smooth (annulusDiffeomorph m)
    (planeClosedAnnulus_compact εm) (explicitAnnulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (explicitAnnulusWidth_pos m)
      (explicitAnnulusWidth_lt_one m)

theorem explicitDualForm_compact : HasCompactSupport (explicitDualForm m) := by
  exact handlePushforwardOneForm_compact (annulusDiffeomorph m)
    (planeClosedAnnulus_compact εm) (explicitAnnulusWidth_subset m)
    (planeRadialDifferential_zero (explicitAnnulusWidth_pos m)
      (explicitAnnulusWidth_lt_one m))

theorem explicitDualForm_closed (x : Surface m) :
    manifoldExteriorOneForm (explicitDualForm m) x = 0 := by
  apply handlePushforwardOneForm_closed (annulusDiffeomorph m)
    (planeClosedAnnulus_compact εm) (explicitAnnulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (explicitAnnulusWidth_pos m)
      (explicitAnnulusWidth_lt_one m)
  · exact manifoldScalarDifferential_closed (planeRadialStep_smooth _).contMDiff

theorem explicitDualForm_support : tsupport (explicitDualForm m) ⊆
    (annulusDiffeomorph m) '' planeClosedAnnulus εm :=
  handlePushforwardOneForm_tsupport (annulusDiffeomorph m)
    (planeClosedAnnulus_compact εm) (explicitAnnulusWidth_subset m)
    (planeRadialDifferential_zero (explicitAnnulusWidth_pos m)
      (explicitAnnulusWidth_lt_one m))

/-! ### Period one along the transverse cycle -/

/-- The radial step along the transverse cycle. -/
def xTransverseStep (θ : ℝ) : ℝ := planeRadialStep εm (transverseRealCoordinate m θ)

/-- The dual form along the transverse cycle. -/
def xDualAlongCycle (θ : ℝ) : ℝ := curveOneForm (explicitDualForm m) (transverseCycle m) θ

theorem xTransverseStep_smooth : ContDiff ℝ ∞ (xTransverseStep m) :=
  (planeRadialStep_smooth _).comp (transverseRealCoordinate_smooth m)

theorem xDualAlongCycle_smooth : ContDiff ℝ ∞ (xDualAlongCycle m) :=
  curveOneForm_smooth (explicitDualForm_smooth m) (transverseCycle_smooth m)

theorem xDualAlongCycle_zero {θ : ℝ} (hθ : Real.cos θ ≤ 0) : xDualAlongCycle m θ = 0 := by
  have ht : transverseCycle m θ ∉ (annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target, transverseCycle_branch_iff]
    exact not_lt.mpr hθ
  change (extendManifoldOneForm (annulusDiffeomorph m).target _ (transverseCycle m θ)) _ = 0
  rw [extendManifoldOneForm_outside ht]
  rfl

theorem xDualAlongCycle_deriv {θ : ℝ} (hθ : 0 < Real.cos θ) :
    xDualAlongCycle m θ = deriv (xTransverseStep m) θ := by
  have ht : transverseCycle m θ ∈ (annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target, transverseCycle_branch_iff]
    exact hθ
  exact curveOneForm_pushforward_scalar (annulusDiffeomorph m)
    (planeRadialStep_smooth _).contMDiff (transverseCycle_smooth m) ht

theorem xTransverseStep_lower : xTransverseStep m (-(Real.pi / 2)) = 0 := by
  apply planeRadialStep_zero (explicitAnnulusWidth_pos m) (explicitAnnulusWidth_lt_one m)
  change ‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖ ≤ _
  rw [ContinuousLinearEquiv.symm_apply_apply, transverseCycle_coord_norm]
  linarith [transverseRadius_lower, explicitAnnulusWidth_lt m]

theorem xTransverseStep_upper : xTransverseStep m (Real.pi / 2) = 1 := by
  apply planeRadialStep_one (explicitAnnulusWidth_pos m)
  change _ ≤ ‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖
  rw [ContinuousLinearEquiv.symm_apply_apply, transverseCycle_coord_norm]
  linarith [transverseRadius_upper, explicitAnnulusWidth_lt m]

theorem xDualAlongCycle_integral_first :
    ∫ θ in -(Real.pi / 2)..Real.pi / 2, xDualAlongCycle m θ = 1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)
    (xTransverseStep_smooth m).continuous.continuousOn
    (fun θ hθ => ?_)
    ((xDualAlongCycle_smooth m).continuous.intervalIntegrable _ _)
  · simpa only [xTransverseStep_lower, xTransverseStep_upper, sub_zero] using he
  · rw [xDualAlongCycle_deriv m (Real.cos_pos_of_mem_Ioo hθ)]
    exact ((xTransverseStep_smooth m).differentiable (by simp) θ).hasDerivAt

theorem xDualAlongCycle_integral_second :
    ∫ θ in Real.pi / 2..Real.pi + Real.pi / 2, xDualAlongCycle m θ = 0 := by
  calc
    _ = ∫ θ in Real.pi / 2..Real.pi + Real.pi / 2, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi + Real.pi / 2)] at hθ
      exact xDualAlongCycle_zero m (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2)
    _ = 0 := by simp

theorem explicitDualForm_period :
    ∫ θ in -(Real.pi / 2)..Real.pi + Real.pi / 2,
      curveOneForm (explicitDualForm m) (transverseCycle m) θ = 1 := by
  have hi := (xDualAlongCycle_smooth m).continuous
  change ∫ θ in -(Real.pi / 2)..Real.pi + Real.pi / 2, xDualAlongCycle m θ = 1
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi / 2)
    (hi.intervalIntegrable _ _) (hi.intervalIntegrable _ _),
    xDualAlongCycle_integral_first, xDualAlongCycle_integral_second, add_zero]

/-- The pullback of `β_m` to the transverse cylinder. -/
def xCylinderDualForm : ℝ → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (fun _ : ℝ => explicitDualForm m) (transverseCylinder m)

theorem xCylinderDualForm_B (p t : ℝ) :
    cylinderFormB (xCylinderDualForm m) (p, (0, t)) =
      curveOneForm (explicitDualForm m) (fun s => transverseCylinder m (0, circleTurn s)) t := by
  rw [cylinderFormB_curve]
  exact curveOneForm_parameter_pullback (fun _ : ℝ => explicitDualForm m)
    ((transverseCylinder m).mdifferentiableAt (by simp) (transverseCylinder_core m _))
    ((cylinderCover_smooth.comp ((contDiff_const.prodMk contDiff_id).contMDiff)).mdifferentiableAt
      (by simp))

/-- **Period one**: `∮ β_m = 1` around the core circle of the transverse cylinder. -/
theorem xCylinderDualForm_period (p : ℝ) :
    cylinderFormPeriod 0 (xCylinderDualForm m) p = 1 := by
  unfold cylinderFormPeriod annularMean
  simp_rw [xCylinderDualForm_B]
  have he : (fun s => transverseCylinder m (0, circleTurn s)) =
      (fun s => transverseCycle m (2 * Real.pi * s + 0)) := by
    funext s
    rw [add_zero]
    exact transverseCylinder_core_cycle m s
  rw [he]
  simp_rw [curveOneForm_affine (transverseCycle_smooth m), add_zero]
  rw [intervalIntegral.integral_const_mul]
  change (2 * Real.pi) • (∫ t in (0 : ℝ)..1,
    curveOneForm (explicitDualForm m) (transverseCycle m) (2 * Real.pi * t)) = 1
  rw [intervalIntegral.smul_integral_comp_mul_left]
  simp only [mul_zero, mul_one]
  have hp := curveOneForm_period_integral (α := explicitDualForm m)
    (transverseCycle_smooth m) (transverseCycle_periodic m) 0 (-(Real.pi / 2))
  rw [zero_add, show -(Real.pi / 2) + 2 * Real.pi = Real.pi + Real.pi / 2 by ring] at hp
  rw [hp]
  exact explicitDualForm_period m

end SymplecticPacking.BranchSmall
