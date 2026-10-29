import SymplecticPacking.HighDim.Handle.QuadricOrdinaryGrid

/-!
# Rational grid parameters for the quadric

Fully rational mesh parameters for the separated integer-parameter models.
-/

namespace SymplecticPacking.HighDim.ToricPackingStages

def quadricGridThreshold : ℚ := 1/64
def quadricGridRadius (R : ℚ) : ℚ := 1/(262144*(R+1))
def quadricGridMesh (R : ℚ) : ℚ := quadricGridRadius R/32
def quadricGridSize (R : ℚ) : ℕ := ⌈R/quadricGridMesh R⌉₊+2

theorem quadricGridRadius_pos {R : ℚ} (hR : 0 ≤ R) : 0 < quadricGridRadius R := by
  unfold quadricGridRadius
  positivity

theorem quadricGridRadius_bound {R : ℚ} (hR : 0 ≤ R) : quadricGridRadius R ≤ 1/262144 := by
  have hd : 0 < 262144*(R+1) := by positivity
  unfold quadricGridRadius
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem quadricGridRadius_mul {R : ℚ} (hR : 0 ≤ R) :
    quadricGridRadius R*(R+1) = 1/262144 := by
  have hn : R+1 ≠ 0 := by linarith
  unfold quadricGridRadius
  field_simp
  <;> ring

theorem quadricGrid_budget {R : ℚ} (hR : 0 ≤ R) :
    2*quadricGridRadius R*(2*(R+1)+2*quadricGridRadius R) < quadricGridThreshold^2/2 := by
  have hr := quadricGridRadius_pos hR
  have hb := quadricGridRadius_bound hR
  have hm := quadricGridRadius_mul hR
  have hs := pow_le_pow_left₀ hr.le hb 2
  unfold quadricGridThreshold
  nlinarith

theorem quadricGrid_small {R : ℚ} (hR : 0 ≤ R) :
    4*quadricGridRadius R*(2*R+4*quadricGridRadius R) < quadricGridThreshold^2 := by
  have hr := quadricGridRadius_pos hR
  have hb := quadricGridRadius_bound hR
  have hm := quadricGridRadius_mul hR
  have hs := pow_le_pow_left₀ hr.le hb 2
  unfold quadricGridThreshold
  nlinarith

theorem quadricGridMesh_pos {R : ℚ} (hR : 0 ≤ R) : 0 < quadricGridMesh R := by
  exact div_pos (quadricGridRadius_pos hR) (by norm_num)

theorem quadricGridSize_bound {R : ℚ} (hR : 0 ≤ R) :
    R+quadricGridMesh R < (quadricGridSize R:ℚ)*quadricGridMesh R := by
  have hh := quadricGridMesh_pos hR
  have hc : R/quadricGridMesh R ≤ (⌈R/quadricGridMesh R⌉₊:ℚ) := Nat.le_ceil _
  have hc' := (div_le_iff₀ hh).mp hc
  unfold quadricGridSize
  push_cast
  nlinarith

#check_explicit quadricGridSize
end SymplecticPacking.HighDim.ToricPackingStages
