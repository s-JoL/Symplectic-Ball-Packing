import SymplecticPacking.HighDim.Handle.QuadricBoxInside
import OAI.Geometry.BallPacking.SurfaceArea.QuadricSmoothExhaustion

/-!
# Boundary collar cutoff for the quadric

A fixed boundary collar cutoff, expressed in the projection coordinate.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology

def quadricBoundaryCutoff {m : ℕ} {a : Fin m → ℂ} (A B : ℝ) (x : locus a) : ℝ :=
  Real.smoothTransition ((Complex.normSq x.val.1-A^2)/(B^2-A^2))

theorem quadricBoundaryCutoff_nonneg {m : ℕ} {a : Fin m → ℂ} (A B : ℝ) (x : locus a) :
    0 ≤ quadricBoundaryCutoff A B x := Real.smoothTransition.nonneg _

theorem quadricBoundaryCutoff_le_one {m : ℕ} {a : Fin m → ℂ} (A B : ℝ) (x : locus a) :
    quadricBoundaryCutoff A B x ≤ 1 := Real.smoothTransition.le_one _

theorem quadricBoundaryCutoff_zero {m : ℕ} {a : Fin m → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) (x : locus a) (hx : ‖x.val.1‖ ≤ A) :
    quadricBoundaryCutoff A B x = 0 := by
  have hden : 0 < B^2-A^2 := by nlinarith
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hden.le
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg x.val.1]

theorem quadricBoundaryCutoff_one {m : ℕ} {a : Fin m → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) (x : locus a) (hx : B ≤ ‖x.val.1‖) :
    quadricBoundaryCutoff A B x = 1 := by
  have hden : 0 < B^2-A^2 := by nlinarith
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div hden).mpr
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg x.val.1]

section Smooth
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]

theorem quadricBoundaryCutoff_smooth (A B : ℝ) :
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ) ∞ (quadricBoundaryCutoff (a := a) A B) := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hp : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (fun x : locus a => x.val.1) :=
    ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).contDiff.restrict_scalars ℝ).contMDiff.comp
      (real_inclusion_contMDiff a)
  exact Real.smoothTransition.contDiff.contMDiff.comp
    (((hn.contMDiff.comp hp).sub contMDiff_const).div_const _)

end Smooth

#check_explicit quadricBoundaryCutoff
end SymplecticPacking.HighDim.ToricPackingStages
