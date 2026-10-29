import SymplecticPacking.BranchSmall.TransportControl
import SymplecticPacking.BranchSmall.HomogeneousGrowth

/-!
# Transport away from the central parameter

For `T ≠ 0` the vertical block of the constraint is invertible, so the 
horizontal transport field is smooth on the entire affine total space.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

variable {q : ℕ}

theorem transportConstraint_surjective_of_time_ne {T : ℝ} (hT : T ≠ 0) (y : Tot q) :
    Function.Surjective (transportConstraint T y) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  intro u
  refine ⟨(0, -((T : ℂ)⁻¹ • u)), ?_⟩
  simp only [transportConstraint_apply, map_zero, smul_neg, sub_neg_eq_add, smul_smul,
    mul_inv_cancel₀ hTc, one_smul, zero_add]

theorem transportSystem_invertible_of_time_ne {b T : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hT : T ≠ 0) (y : Tot q) :
    (horizontalSystem (bundleForm b y) (transportConstraint T y)).IsInvertible :=
  horizontalSystem_isInvertible (transportConstraint_surjective_of_time_ne hT y)
    (transport_kernel_nondegenerate hb0 hb T y)

theorem transport_existsUnique_of_time_ne {b T : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hT : T ≠ 0) (y : Tot q) :
    ∃! v : Tot q, jacobian y.1 v.1 - (T : ℂ) • v.2 = y.2 ∧
      ∀ k : Tot q, jacobian y.1 k.1 - (T : ℂ) • k.2 = 0 → bundleForm b y v k = 0 := by
  let v := symplecticHorizontalLift (bundleForm b y) (transportConstraint T y) y.2
  have hi := transportSystem_invertible_of_time_ne hb0 hb hT y
  have hv : transportConstraint T y v = y.2 := symplecticHorizontalLift_projects hi _
  have hvo : ∀ k, transportConstraint T y k = 0 → bundleForm b y v k = 0 :=
    fun k hk => symplecticHorizontalLift_orthogonal hi y.2 hk
  refine ⟨v, ⟨by simpa only [transportConstraint_apply] using hv,
    fun k hk => hvo k (by simpa only [transportConstraint_apply] using hk)⟩, ?_⟩
  intro w hw
  have hw' : transportConstraint T y w = y.2 := by simpa only [transportConstraint_apply] using hw.1
  apply sub_eq_zero.mp
  apply transport_kernel_nondegenerate hb0 hb T y (w - v)
  · rw [map_sub, hw', hv, sub_self]
  · intro k hk
    rw [map_sub, sub_apply, hw.2 k (by simpa only [transportConstraint_apply] using hk), hvo k hk, sub_self]

theorem transportField_spec_of_time_ne (a : Fin q → ℂ) {b T : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hT : T ≠ 0) (y : Tot q) :
    jacobian y.1 (transportField a b T y).1 - (T : ℂ) • (transportField a b T y).2 = y.2 ∧
      ∀ k : Tot q, jacobian y.1 k.1 - (T : ℂ) • k.2 = 0 →
        bundleForm b y (transportField a b T y) k = 0 := by
  have h := transport_existsUnique_of_time_ne hb0 hb hT y
  unfold transportField
  rw [dif_pos h]
  exact SymplecticPacking.Explicit.the_spec h

end SymplecticPacking.BranchSmall.VT
