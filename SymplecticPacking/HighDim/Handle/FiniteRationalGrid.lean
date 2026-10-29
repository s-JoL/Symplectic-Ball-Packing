import SymplecticPacking.HighDim.Handle.QuadricBranchBoxCover

/-!
# A finite rational grid

A predetermined finite rational grid, with a proved approximation radius.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function

def rationalGridCoordinate (N : ℕ) (h : ℚ) (i : Fin (2*N+1)) : ℚ :=
  ((i.val : ℚ)-N)*h

def rationalGridPoint (N : ℕ) (h : ℚ) (i : Fin (2*N+1) × Fin (2*N+1)) : ℚ × ℚ :=
  (rationalGridCoordinate N h i.1, rationalGridCoordinate N h i.2)

theorem rationalGridCoordinate_cover (N : ℕ) (h : ℚ) (hh : 0 < (h : ℝ))
    {R t : ℝ} (hN : R+h < (N : ℝ)*h) (ht : |t| ≤ R) :
    ∃ i : Fin (2*N+1), |(rationalGridCoordinate N h i : ℝ)-t| < h := by
  let z : ℤ := ⌊t/(h:ℝ)⌋
  have hzlow : (z : ℝ)*(h:ℝ) ≤ t := (le_div_iff₀ hh).mp (Int.floor_le _)
  have hzhigh : t < ((z:ℝ)+1)*(h:ℝ) := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)
  have hzN₁ : -(N : ℝ) < z := by
    have hneg : -R ≤ t := (abs_le.mp ht).1
    nlinarith
  have hzN₂ : (z : ℝ) < N := by
    have hpos : t ≤ R := (abs_le.mp ht).2
    nlinarith
  have hzN₁' : -(N : ℤ) ≤ z := by exact_mod_cast hzN₁.le
  have hzN₂' : z ≤ (N : ℤ) := by exact_mod_cast hzN₂.le
  have hnat : 0 ≤ z+(N : ℤ) := by omega
  let i : Fin (2*N+1) := ⟨(z+(N:ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ)-(N : ℤ) = z := by dsimp [i]; omega
  have hie : (i.val : ℝ)-(N : ℝ) = z := by exact_mod_cast hi
  refine ⟨i, ?_⟩
  have hcoord : (rationalGridCoordinate N h i : ℝ) = (z:ℝ)*(h:ℝ) := by
    simp only [rationalGridCoordinate, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, hie]
  rw [hcoord]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem rationalGridPoint_cover (N : ℕ) (h : ℚ) (hh : 0 < (h : ℝ))
    {R : ℝ} (hN : R+h < (N : ℝ)*h) (x : ℂ) (hx : ‖x‖ ≤ R) :
    ∃ i : Fin (2*N+1) × Fin (2*N+1),
      ‖rationalComplex (rationalGridPoint N h i)-x‖ < 2*(h:ℝ) := by
  obtain ⟨i, hi⟩ := rationalGridCoordinate_cover N h hh hN ((Complex.abs_re_le_norm x).trans hx)
  obtain ⟨j, hj⟩ := rationalGridCoordinate_cover N h hh hN ((Complex.abs_im_le_norm x).trans hx)
  refine ⟨(i,j), ?_⟩
  have hre : |(rationalComplex (rationalGridPoint N h (i,j))-x).re| < (h:ℝ) := hi
  have him : |(rationalComplex (rationalGridPoint N h (i,j))-x).im| < (h:ℝ) := hj
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by linarith)

#check_explicit rationalGridPoint
end SymplecticPacking.HighDim.ToricPackingStages
