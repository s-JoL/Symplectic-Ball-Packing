import SymplecticPacking.HighDim.Handle.QuadricBoxCode
import OAI.Geometry.BallPacking.Surfaces.QuadricInfinityDiffeomorph

/-!
# Inclusion certificates for quadric coordinate boxes

Finite scalar certificates place explicit boxes inside the compact base.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter
open scoped Topology
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian

theorem projection_strict_subset_interior {m : ℕ} (a : Fin m → ℂ) (R : ℝ) :
    {x : locus a | ‖x.val.1‖ < R} ⊆ interior (projectionDomain a R) := by
  have ho : IsOpen {x : locus a | ‖x.val.1‖ < R} :=
    isOpen_lt (by fun_prop) continuous_const
  apply ho.subset_interior_iff.mpr
  intro x hx
  change ‖x.val.1‖ < R at hx
  exact hx.le

theorem ordinaryRawBox_inside {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) (r : ℝ) (hr : 0 < r)
    (hm : ∀ j, (2*r)*(2*‖c.val.1‖+2*r) < ‖c.val.2 j‖^2) {R : ℝ}
    (hR : ‖c.val.1‖+2*r < R) :
    (ordinaryRawBox c hc r hr hm).compactCarrier ⊆ interior (projectionDomain a R) := by
  rintro x ⟨z, hz, rfl⟩
  apply projection_strict_subset_interior
  let B := ordinaryRawBox c hc r hr hm
  have ht : z ∈ B.chart.target := B.closed_subset hz
  have hcoord : Complex.equivRealProdCLM ((B.chart.symm z).val.1) = z := B.chart.right_inv ht
  have hd := realProd_closedBall_to_complex hz
  rw [← hcoord, ContinuousLinearEquiv.symm_apply_apply] at hd
  have hn : ‖(B.chart.symm z).val.1-c.val.1‖ ≤ 2*r := by
    simpa only [ordinaryRawBox, ContinuousLinearEquiv.symm_apply_apply,
      Metric.mem_closedBall, dist_eq_norm] using hd
  change ‖(B.chart.symm z).val.1‖ < R
  calc
    ‖(B.chart.symm z).val.1‖ = ‖((B.chart.symm z).val.1-c.val.1)+c.val.1‖ := by congr 1; ring
    _ ≤ ‖(B.chart.symm z).val.1-c.val.1‖+‖c.val.1‖ := norm_add_le _ _
    _ ≤ 2*r+‖c.val.1‖ := by linarith [hn]
    _ < R := by linarith

theorem branchRawBox_inside {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) (hci : c.val.2 i = 0) (r : ℝ) (hr : 0 < r)
    (hm₀ : (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.1‖^2)
    (hm : ∀ j, j≠i → (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.2 j‖^2)
    {R : ℝ} (hR : 0 < R) (hRi : ‖a i‖+4*r^2 < R^2) :
    (branchRawBox c i hc r hr hm₀ hm).compactCarrier ⊆ interior (projectionDomain a R) := by
  rintro x ⟨z, hz, rfl⟩
  apply projection_strict_subset_interior
  let B := branchRawBox c i hc r hr hm₀ hm
  have ht : z ∈ B.chart.target := B.closed_subset hz
  have hcoord : Complex.equivRealProdCLM ((B.chart.symm z).val.2 i) = z := B.chart.right_inv ht
  have hd := realProd_closedBall_to_complex hz
  rw [← hcoord, ContinuousLinearEquiv.symm_apply_apply] at hd
  have hn : ‖(B.chart.symm z).val.2 i‖ ≤ 2*r := by
    simpa only [branchRawBox, ContinuousLinearEquiv.symm_apply_apply, hci,
      Metric.mem_closedBall, dist_zero_right] using hd
  have he : (B.chart.symm z).val.1^2 = a i+((B.chart.symm z).val.2 i)^2 := by
    have hh := mem_locus.mp (B.chart.symm z).property i
    linear_combination -hh
  have hnorm : ‖(B.chart.symm z).val.1‖^2 ≤ ‖a i‖+‖(B.chart.symm z).val.2 i‖^2 := by
    rw [← norm_pow, he]
    exact (norm_add_le _ _).trans_eq (by rw [norm_pow])
  have hsq : ‖(B.chart.symm z).val.2 i‖^2 ≤ (2*r)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  change ‖(B.chart.symm z).val.1‖ < R
  nlinarith [norm_nonneg ((B.chart.symm z).val.1)]

namespace QuadricBoxCode
variable {m : ℕ} (a : Fin m → ℂ)

def Inside (R : ℝ) : QuadricBoxCode m → Prop
  | .ordinary q _ r => ‖rationalComplex q‖+2*(r:ℝ) < R
  | .branch i _ _ r => ‖a i‖+4*(r:ℝ)^2 < R^2

variable [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]

end QuadricBoxCode
end SymplecticPacking.HighDim.ToricPackingStages
