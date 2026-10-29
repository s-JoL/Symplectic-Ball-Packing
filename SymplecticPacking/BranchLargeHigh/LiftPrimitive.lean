import SymplecticPacking.BranchSmall.VectorTransfer
import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus

/-!
# The ball-chart Liouville primitive

The scalar `lamAmb` is the continuous linear primitive of the standard form.
The radial ball chart pulls this primitive back exactly to the affine FS primitive.
-/

noncomputable section
namespace SymplecticPacking.BranchLargeHigh.Two

open OAI.PackingSufficiencySupport (Ambient standardForm)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open ContinuousLinearMap
open scoped ContDiff

/-- The ball-chart Liouville form in complex coordinates. -/
def lamAmb {n : ℕ} (ξ v : Ambient n) : ℝ :=
  (∑ i, ((starRingEnd ℂ) (ξ i) * v i).im) / 2

def ambientPrimitive (m : ℕ) : Ambient (m + 1) → Ambient (m + 1) →L[ℝ] ℝ :=
  linearLiouville (successorStandardForm m)

theorem ambientPrimitive_apply (m : ℕ) (z v : Ambient (m + 1)) :
    ambientPrimitive m z v = lamAmb z v := by
  change (1 / 2 : ℝ) * successorStandardForm m z v = _
  rw [successorStandardForm_apply]
  have hsum : (∑ j, ((starRingEnd ℂ) (z j) * v j).im) = standardForm z v := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [lamAmb, hsum]
  ring

theorem ambientPrimitive_contDiff (m : ℕ) : ContDiff ℝ ∞ (ambientPrimitive m) :=
  linearLiouville_smooth _

theorem ambientPrimitive_exterior (m : ℕ) (z : Ambient (m + 1)) :
    euclideanExteriorOneForm (ambientPrimitive m) z = successorStandardForm m := by
  rw [ambientPrimitive, ← manifoldExteriorOneForm_model]
  apply linearLiouville_exterior
  intro v w
  simp only [successorStandardForm_apply, standardForm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem affineRadialTarget_primitive (m : ℕ) (z v : Affine m) :
    ambientPrimitive m (affineRadialTarget m (1 / Real.pi) z)
      (fderiv ℝ (affineRadialTarget m (1 / Real.pi)) z v) = ambientFSPrimitive (1 / Real.pi) z v := by
  have hd := (optionPhaseAmbient m).hasFDerivAt.comp z
    (((fsBallMap_smooth (1 / Real.pi)).differentiable (by simp) (affinePhaseEquiv m z)).hasFDerivAt.comp z
      (affinePhaseEquiv m).hasFDerivAt)
  change HasFDerivAt (affineRadialTarget m (1 / Real.pi)) _ z at hd
  rw [hd.fderiv]
  change (1 / 2 : ℝ) * successorStandardForm m
    (optionPhaseAmbient m (fsBallMap (1 / Real.pi) (affinePhaseEquiv m z)))
    (optionPhaseAmbient m (fderiv ℝ (fsBallMap (1 / Real.pi)) (affinePhaseEquiv m z)
      (affinePhaseEquiv m v))) = _
  rw [successorStandardForm_apply, optionPhaseAmbient_form]
  change standardLiouville (fsBallMap (1 / Real.pi) (affinePhaseEquiv m z))
    (fderiv ℝ (fsBallMap (1 / Real.pi)) (affinePhaseEquiv m z) (affinePhaseEquiv m v)) = _
  rw [fsBallMap_primitive (one_div_pos.mpr Real.pi_pos).le, affinePhaseEquiv_apply, affinePhaseEquiv_apply]
  rfl

end SymplecticPacking.BranchLargeHigh.Two
