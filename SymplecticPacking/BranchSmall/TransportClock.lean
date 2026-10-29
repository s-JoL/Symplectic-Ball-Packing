import SymplecticPacking.BranchSmall.TransportPositive
import SymplecticPacking.BranchSmall.QuadricReflections

/-!
# A positive clock for horizontal transport

The logarithmic clock separates the singular central parameter from the complete
positive-time vector field. Its speed cancels the graph-coordinate factor `1/t`.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Return (CSField flow)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

variable {q : ℕ}

def transportClock (δ s : ℝ) : ℝ := Real.exp ((1 - s) * Real.log δ)

theorem transportClock_pos (δ s : ℝ) : 0 < transportClock δ s := Real.exp_pos _

theorem transportClock_contDiff (δ : ℝ) : ContDiff ℝ ∞ (transportClock δ) :=
  ((contDiff_const.sub contDiff_id).mul contDiff_const).exp

def transportClockInverse (δ t : ℝ) : ℝ :=
  (Real.log t - Real.log δ) / (-Real.log δ)

theorem transportClockInverse_mem {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ht : t ∈ Icc δ (1 : ℝ)) : transportClockInverse δ t ∈ Icc (0 : ℝ) 1 := by
  have hlog := Real.log_neg hδ0 hδ1
  have ht0 := hδ0.trans_le ht.1
  have hlo := Real.log_le_log hδ0 ht.1
  have hhi := Real.log_le_log ht0 ht.2
  rw [Real.log_one] at hhi
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (neg_nonneg.mpr hlog.le)
  · rw [transportClockInverse, div_le_iff₀ (neg_pos.mpr hlog)]
    linarith

theorem transportClock_inverse {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    transportClock δ (transportClockInverse δ t) = t := by
  have hlog : Real.log δ ≠ 0 := (Real.log_neg hδ0 hδ1).ne
  have he : (1 - transportClockInverse δ t) * Real.log δ = Real.log t := by
    unfold transportClockInverse
    field_simp [hlog]
    ring
  rw [transportClock, he, Real.exp_log ht]

theorem transportClockInverse_self {δ : ℝ} : transportClockInverse δ δ = 0 := by
  simp only [transportClockInverse, sub_self, zero_div]

theorem transportClockInverse_hasDerivAt {δ t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (transportClockInverse δ) (t⁻¹ / (-Real.log δ)) t :=
  ((Real.hasDerivAt_log ht).sub_const (Real.log δ)).div_const (-Real.log δ)

/-- The horizontal base field after changing to logarithmic time. -/
def logarithmicTransport (a : Fin q → ℂ) (b δ : ℝ) (s : ℝ) (z : Affine q) : Affine q :=
  (Real.log δ * radialCoefficient (graphTube a (transportClock δ s) z)) •
    normalReturnField a b (transportClock δ s) z

theorem logarithmicTransport_contDiff (a : Fin q → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (δ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine q => logarithmicTransport a b δ p.1 p.2) := by
  have hT := transportClock_contDiff δ
  have hT0 := fun s => (transportClock_pos δ s).ne'
  exact (contDiff_const.mul (radialCoefficient_contDiff.comp
      (graphTube_parameter_contDiff a hT hT0))).smul
    (normalReturnField_parameter_contDiff a hT hT0 hb0 hb)

theorem logarithmicTransport_linearGrowth (a : Fin q → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (δ : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : Affine q,
      ‖logarithmicTransport a b δ s z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨C, hC⟩ := normalReturnField_parameter_linearGrowth a (transportClock_contDiff δ)
    (fun s => (transportClock_pos δ s).ne') hb0 hb
  have hC0 : 0 ≤ C := by
    have hh := hC 0 ⟨le_rfl, zero_le_one⟩ 0
    simpa only [norm_zero, add_zero, mul_one] using (norm_nonneg _).trans hh
  refine ⟨2 * |Real.log δ| * C, ?_⟩
  intro s hs z
  have hr0 := radialCoefficient_nonneg (graphTube a (transportClock δ s) z)
  have hr2 := radialCoefficient_le_two (graphTube a (transportClock δ s) z)
  rw [logarithmicTransport, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0]
  calc
    |Real.log δ| * radialCoefficient (graphTube a (transportClock δ s) z) *
        ‖normalReturnField a b (transportClock δ s) z‖ ≤
        |Real.log δ| * 2 * (C * (1 + ‖z‖)) := by gcongr; exact hC s hs z
    _ = (2 * |Real.log δ| * C) * (1 + ‖z‖) := by ring

theorem logarithmicTransport_control (a : Fin q → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (δ : ℝ) (z : Affine q) :
    LocalControl (logarithmicTransport a b δ) z := by
  obtain ⟨C, hC⟩ := logarithmicTransport_linearGrowth a hb0 hb δ
  exact localControl_of_linearGrowth isOpen_univ (fun _ _ => mem_univ _)
    (logarithmicTransport_contDiff a hb0 hb δ).contDiffOn hC z

theorem logarithmicTransport_reflection (a : Fin q → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (δ s : ℝ) (i : Option (Fin q)) (z : Affine q) :
    logarithmicTransport a b δ s (affineReflection i z) =
      affineReflection i (logarithmicTransport a b δ s z) := by
  have hr : radialCoefficient (graphTube a (transportClock δ s) (affineReflection i z)) =
      radialCoefficient (graphTube a (transportClock δ s) z) := by
    simp only [radialCoefficient, graphTube, affineReflection_nsq, affineReflection_equations]
  simp only [logarithmicTransport, hr, normalReturnField_reflection a _ hb0 hb, map_smul]

end SymplecticPacking.BranchSmall.VT
