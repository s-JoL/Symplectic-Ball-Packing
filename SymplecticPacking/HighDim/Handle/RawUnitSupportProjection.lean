import SymplecticPacking.HighDim.Handle.QuadricRawBoxes
import SymplecticPacking.HighDim.Handle.RawAmbientUnitMass

/-!
# Projection bound for the raw unit bump support

A raw ordinary bump stays in the explicitly bounded projection core.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
variable {m : ℕ} {a : Fin m → ℂ}

theorem unitSupport_projection_subset (B : RawAmbientBox (Affine m) (locus a))
    (hcoord : ∀ x : locus a, B.box.chart x=Complex.equivRealProdCLM x.val.1)
    {R : ℝ} (hR : ‖Complex.equivRealProdCLM.symm B.box.point‖+B.box.radius≤R) :
    B.unitSupport⊆projectionDomain a R := by
  rintro x ⟨z,hz,rfl⟩
  have hzt : z∈B.box.chart.target := B.box.closed_subset
    (Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos]) hz)
  have he : (B.box.chart.symm z).val.1=Complex.equivRealProdCLM.symm z := by
    have h := hcoord (B.box.chart.symm z)
    rw [B.box.chart.right_inv hzt] at h
    exact (congrArg Complex.equivRealProdCLM.symm h).symm
  have hd := Metric.mem_closedBall.mp (realProd_closedBall_to_complex hz)
  change ‖(B.box.chart.symm z).val.1‖≤R
  rw [he]
  have ht := norm_le_norm_add_const_of_dist_le hd
  linarith
end SymplecticPacking.HighDim.ToricPackingStages
