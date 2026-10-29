import SymplecticPacking.BranchSmall.HandleChartCertificates

/-!
# The width of the transverse handle cylinder

Fixed width `1/4` for the explicit transverse handle cylinder.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall
open Set
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

/-- A fixed rational half-width; its doubled closed band stays in the native sheet. -/
def explicitCylinderWidth (_m : ℕ) : ℝ := 1 / 4

theorem explicitCylinderWidth_pos (m : ℕ) : 0 < explicitCylinderWidth m := by
  norm_num [explicitCylinderWidth]

theorem explicitCylinderWidth_le_one (m : ℕ) : explicitCylinderWidth m ≤ 1 / 2 := by
  norm_num [explicitCylinderWidth]

theorem explicitCylinderWidth_double_subset {m : ℕ} {b : ℝ}
    (hb : b < 2 * explicitCylinderWidth m) :
    Icc (-b) b ×ˢ (univ : Set Circle) ⊆ (transverseCylinder m).source := by
  intro q hq
  rw [transverseCylinder_source]
  apply cylinder_half_native m q
  have hb' : b < 1 / 2 := by
    norm_num only [explicitCylinderWidth] at hb
    exact hb
  exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩

theorem explicitCylinderWidth_subset (m : ℕ) :
    Icc (-explicitCylinderWidth m) (explicitCylinderWidth m) ×ˢ (univ : Set Circle) ⊆
      (transverseCylinder m).source :=
  explicitCylinderWidth_double_subset (by linarith [explicitCylinderWidth_pos m])

/-- Source of the restricted transverse chart for widths below the explicit width
(analogue of the library's `restrictedTransverseCylinder_source`). -/
theorem restrictedTransverseCylinder_source_explicit {m : ℕ} {a : ℝ}
    (ha : a ≤ explicitCylinderWidth m) :
    (restrictedTransverseCylinder m a).source = Ioo (-a) a ×ˢ univ := by
  apply inter_eq_right.mpr
  intro z hz
  exact explicitCylinderWidth_subset m ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩

end SymplecticPacking.BranchSmall
