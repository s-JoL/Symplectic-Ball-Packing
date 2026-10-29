import SymplecticPacking.General.Ham.Linear.Polar
import SymplecticPacking.General.Ham.Linear.Angle

/-!
# An explicit path in `Sp(2n)` from `1` to any symplectic matrix

For `M ∈ Sp(2n)` with decomposition `M = U · Dg(P, P⁻¹) · Up(S)` (`Polar.lean`), angle
`θ = goodAngle U` (`Angle.lean`) and `X = cayleyOf (rot θ · U)` (`Unitary.lean`):

  `spPath M σ = rot(-σθ) · cayley X σ · Dg(P_σ, P_σ⁻¹) · Up(σ S)`,  `P_σ = posPath P σ`.

Every factor is symplectic for every `σ ∈ ℝ` and has smooth entries; at `σ = 0` all factors are
`1`, and at `σ = 1` the product is `rot(-θ) · rot θ · U · Dg(P, P⁻¹) · Up(S) = M`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix
open scoped ContDiff

variable {n : ℕ}

/-- **The explicit path in `Sp(2n)`.** -/
def spPath (M : Mat n) (σ : ℝ) : Mat n :=
  rot (-(σ * goodAngle (polarU M))) * cayley (cayleyOf (rot (goodAngle (polarU M)) * polarU M)) σ *
    Dg (posPath (polarP M) σ) (posPath (polarP M) σ)⁻¹ * Up (σ • polarS M)

theorem spPath_zero (M : Mat n) : spPath M 0 = 1 := by
  simp [spPath, rot_zero, cayley_zero, posPath_zero, Dg_one, Up_zero]

theorem spPath_one {M : Mat n} (hM : M ∈ Sp n) : spPath M 1 = M := by
  have hU := polarU_isUnitaryType hM
  have hV : IsUnitaryType (rot (goodAngle (polarU M)) * polarU M) :=
    (rot_isUnitaryType _).mul hU
  have hdet := goodAngle_spec hU
  simp only [spPath, one_mul, one_smul, posPath_one]
  rw [cayley_cayleyOf_one hV hdet, ← Matrix.mul_assoc, rot_mul_rot, neg_add_cancel, rot_zero,
    Matrix.one_mul]
  exact (polar_decomp hM).symm

theorem spPath_mem {M : Mat n} (hM : M ∈ Sp n) (σ : ℝ) : spPath M σ ∈ Sp n := by
  have hU := polarU_isUnitaryType hM
  have hV : IsUnitaryType (rot (goodAngle (polarU M)) * polarU M) :=
    (rot_isUnitaryType _).mul hU
  have hdet := goodAngle_spec hU
  have hPσ := posPath_posDef (polarP_posDef hM) σ
  unfold spPath
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_
  · exact (rot_isUnitaryType _).mem_Sp
  · exact (cayley_isUnitaryType (cayleyOf_skew hV hdet) (cayleyOf_comm_J hV hdet) σ).mem_Sp
  · apply Dg_mem
    rw [posPath_transpose (polarP_transpose hM)]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hPσ.det_pos.ne')
  · exact Up_mem (by rw [transpose_smul, polarS_transpose hM])

theorem smoothEntries_spPath {M : Mat n} (hM : M ∈ Sp n) : SmoothEntries (spPath M) := by
  have hU := polarU_isUnitaryType hM
  have hV : IsUnitaryType (rot (goodAngle (polarU M)) * polarU M) :=
    (rot_isUnitaryType _).mul hU
  have hdet := goodAngle_spec hU
  have hrot : SmoothEntries fun σ : ℝ => rot (n := n) (-(σ * goodAngle (polarU M))) := by
    have h := smoothEntries_rot (n := n) (-goodAngle (polarU M))
    simp only [mul_neg] at h
    exact h
  unfold spPath
  refine ((hrot.mul (smoothEntries_cayley (cayleyOf_skew hV hdet))).mul ?_).mul ?_
  · unfold Dg
    exact SmoothEntries.fromBlocks' (smoothEntries_posPath _) (SmoothEntries.const 0)
      (SmoothEntries.const 0) (SmoothEntries.inv (smoothEntries_posPath _)
        (fun σ => (posPath_posDef (polarP_posDef hM) σ).det_pos.ne'))
  · unfold Up
    exact SmoothEntries.fromBlocks' (SmoothEntries.const 1)
      (SmoothEntries.smul contDiff_id (SmoothEntries.const _)) (SmoothEntries.const 0)
      (SmoothEntries.const 1)

end SymplecticPacking.General.Ham.Linear
