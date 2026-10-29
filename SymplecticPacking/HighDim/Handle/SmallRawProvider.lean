import SymplecticPacking.HighDim.Handle.QuadricScalarProvider
import SymplecticPacking.BranchSmall.Model

/-!
# The native normalization provider for the small-ball model

The small-ball input supplies every native normalization hypothesis.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
open SymplecticPacking.BranchSmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
variable {k : ℕ}

def smallRawModel (m : ℕ) (ρ : Fin k → ℝ) : RawToricModel (Affine (m+2)) (Surface m) (m+2) 1 :=
  quadricScalarRawModel m (m+2) 1 (baseLevel m ρ) (Polytope.simplex (m+2) (hgt (m+3) ρ))
    (equalNormalCoefficient (m+2) 2) (1-2*hgt (m+3) ρ)

theorem smallRawModel_spec {m : ℕ} {ρ : Fin k → ℝ} (H : BranchSmall.Hyp (m+3) ρ) :
    RawNormalizationSpec (smallRawModel m ρ) (11*dgap (m+3) ρ/64)
      (quadricScalarOuterArea m (m+2) (baseLevel m ρ) (equalNormalCoefficient (m+2) 2)) := by
  have hd := dgap_pos H
  have hsig : sigma (m+3) ρ≤1 := by
    have hs : (0:ℝ)≤∑ i,capA (m+3) ρ i^(m+3) := Finset.sum_nonneg (fun i _ => pow_nonneg (capA_pos H i).le _)
    unfold sigma
    linarith
  have hfct : (1:ℝ)≤(m+3).factorial := by exact_mod_cast Nat.factorial_pos (m+3)
  have hd1 : dgap (m+3) ρ≤1 := (dgap_le H).trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
  have hpow : (2:ℝ)^(m+8)=64*(2:ℝ)^(m+2) := by
    rw [show m+8=(m+2)+6 by omega,pow_add]
    norm_num
    ring
  have hlev : 64*((2:ℝ)^(m+2)*(m+2+2))/dgap (m+3) ρ≤baseLevel m ρ := by
    have he : 64*((2:ℝ)^(m+2)*(m+2+2))/dgap (m+3) ρ=
        (2:ℝ)^(m+8)*(m+4)/dgap (m+3) ρ := by rw [hpow]; ring
    rw [he]
    exact Nat.le_ceil _
  apply quadricScalar_provider m (m+2) 1 (baseLevel m ρ)
    (Polytope.simplex (m+2) (hgt (m+3) ρ)) (equalNormalCoefficient (m+2) 2)
    (1-2*hgt (m+3) ρ) (dgap (m+3) ρ) (equalNormalCoefficient_smooth _ _)
    (by linarith [hgt_lt_half H]) hd hd1 hlev
  · intro p hp
    rw [Polytope.simplex_set] at hp
    exact equalNormalCoefficient_pos (by norm_num) (by linarith [hgt_lt_half H]) hp.2
  · intro p hp
    rw [Polytope.simplex_set] at hp
    exact equalNormalCoefficient_le_one (by norm_num) hp.1
  · intro p hp
    rw [Polytope.simplex_set] at hp
    have hβ : 2*dgap (m+3) ρ≤beta (m+3) ρ := by
      unfold dgap
      linarith [min_le_left (beta (m+3) ρ) (sigma (m+3) ρ/(2*(m+3).factorial))]
    have hκ : 1-2*hgt (m+3) ρ≤equalNormalCoefficient (m+2) 2 p := by
      unfold equalNormalCoefficient
      linarith [hp.2]
    have hm := mul_le_mul_of_nonneg_right hκ (show (0:ℝ)≤(2:ℝ)^(m+2) by positivity)
    have he : beta (m+3) ρ=(1-2*hgt (m+3) ρ)*(2:ℝ)^(m+2) := by
      unfold beta
      rw [show m+3-1=m+2 by omega]
      ring
    rw [he] at hβ
    exact hβ.trans hm

theorem smallRawModel_area_eq {m : ℕ} {ρ : Fin k → ℝ} (H : BranchSmall.Hyp (m+3) ρ) :
    quadricScalarOuterArea m (m+2) (baseLevel m ρ) (equalNormalCoefficient (m+2) 2)=
      (quadricModel m ρ).baseArea (quadricModel_spec H) := by
  funext p
  unfold quadricScalarOuterArea
  rw [quadricScalar_semantic]
  rfl

#check_explicit smallRawModel
end SymplecticPacking.HighDim.ToricPackingStages
