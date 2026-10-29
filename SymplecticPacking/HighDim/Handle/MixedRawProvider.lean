import SymplecticPacking.HighDim.Handle.QuadricScalarProvider
import SymplecticPacking.BranchLargeHigh.MixedModel

/-!
# Native normalization provider for the mixed-weight model

The mixed-weight input supplies every native normalization hypothesis.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
open SymplecticPacking.BranchLargeHigh
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
variable {k : ℕ}

def mixedRawLevel (q : ℕ) (a : ℝ) (r : Fin k → ℝ) : ℕ :=
  ⌈(2:ℝ)^(q+8)*(q+4)/Mixed.dgap (q+2) a r⌉₊

def mixedRawModel (q : ℕ) (a : ℝ) (r : Fin k → ℝ) : RawToricModel (Affine (q+2)) (Surface q) (q+3) 2 :=
  quadricScalarRawModel q (q+3) 2 (mixedRawLevel q a r) (Mixed.polytope (q+2) a r)
    (largeNormalCoefficient (q+2)) ((1-Mixed.h1 (q+2) a r)*(1-2*Mixed.h2 (q+2) a r))

theorem mixed_raw_dgap_le_one {q : ℕ} {a : ℝ} {r : Fin k → ℝ} (H : Mixed.Hyp q a r) :
    Mixed.dgap q a r≤1 := by
  have hδ := Mixed.delta_pos H
  have hσ : Mixed.sigma q a r≤1 := by
    have ha : 0≤a^(q+2) := pow_nonneg (by linarith [H.half_lt]) _
    have hr : (0:ℝ)≤∑ i,r i^(q+2) := Finset.sum_nonneg (fun i _ => pow_nonneg (H.r_pos i).le _)
    unfold Mixed.sigma
    linarith
  let den : ℝ := 2*(q+2).factorial*(4+2^(q+2))
  have hden : 0<den := by dsimp [den]; positivity
  have hf : (1:ℝ)≤(q+2).factorial := by exact_mod_cast Nat.factorial_pos (q+2)
  have hp : (2:ℝ)^q≤(2:ℝ)^(q+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdenlow : 2*(2:ℝ)^q≤den := by
    have h := mul_le_mul_of_nonneg_right (show (2:ℝ)≤2*(q+2).factorial by linarith)
      (show (0:ℝ)≤4+2^(q+2) by positivity)
    dsimp [den]
    nlinarith
  have hδb : Mixed.delta q a r≤Mixed.sigma q a r/den := min_le_right _ _
  have hcross := (le_div_iff₀ hden).mp hδb
  have hδsmall : Mixed.delta q a r*(2*(2:ℝ)^q)≤1 := by
    have h := mul_le_mul_of_nonneg_left hdenlow hδ.le
    nlinarith
  have hβ : Mixed.beta q a r≤1 := by
    calc
      _=(2:ℝ)^q*(1-Mixed.h1 q a r)*(2*Mixed.delta q a r) := by unfold Mixed.beta Mixed.h2; ring
      _≤(2:ℝ)^q*1*(2*Mixed.delta q a r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (show 1-Mixed.h1 q a r≤1 by linarith [Mixed.h1_pos H]) (by positivity)) (by positivity)
      _=Mixed.delta q a r*(2*(2:ℝ)^q) := by ring
      _≤1 := hδsmall
  have hd : 2*Mixed.dgap q a r≤Mixed.beta q a r := by
    unfold Mixed.dgap
    linarith [min_le_left (Mixed.beta q a r)
      ((OAI.PackingSufficiencySupport.largeModelMean q (Mixed.h1 q a r) (Mixed.h2 q a r)-
        (∑ i,r i^(q+2))/((q+2).factorial:ℝ))/2)]
  linarith

theorem mixedRawModel_spec {q : ℕ} {a : ℝ} {r : Fin k → ℝ} (H : Mixed.Hyp (q+2) a r) :
    RawNormalizationSpec (mixedRawModel q a r) (11*Mixed.dgap (q+2) a r/64)
      (quadricScalarOuterArea q (q+3) (mixedRawLevel q a r) (largeNormalCoefficient (q+2))) := by
  have hd := Mixed.dgap_pos H
  have hh1 : Mixed.h1 (q+2) a r<1 := by linarith [Mixed.h1_lt H,H.half_lt]
  have hh2 := Mixed.h2_lt_half H
  have hpow : (2:ℝ)^(q+8)=64*(2:ℝ)^(q+2) := by
    rw [show q+8=(q+2)+6 by omega,pow_add]
    norm_num
    ring
  have hlev : 64*((2:ℝ)^(q+2)*(q+2+2))/Mixed.dgap (q+2) a r≤ mixedRawLevel q a r := by
    have he : 64*((2:ℝ)^(q+2)*(q+2+2))/Mixed.dgap (q+2) a r=
        (2:ℝ)^(q+8)*(q+4)/Mixed.dgap (q+2) a r := by rw [hpow]; ring
    rw [he]
    exact Nat.le_ceil _
  apply quadricScalar_provider q (q+3) 2 (mixedRawLevel q a r) (Mixed.polytope (q+2) a r)
    (largeNormalCoefficient (q+2)) ((1-Mixed.h1 (q+2) a r)*(1-2*Mixed.h2 (q+2) a r))
    (Mixed.dgap (q+2) a r) (largeNormalCoefficient_smooth _)
    (mul_pos (by linarith) (by linarith)) hd (mixed_raw_dgap_le_one H) hlev
  · intro p hp
    exact largeNormalCoefficient_pos hh1 hh2 hp
  · intro p hp
    exact largeNormalCoefficient_le_one hp.1
  · intro p hp
    have hdβ : 2*Mixed.dgap (q+2) a r≤Mixed.beta (q+2) a r := by
      unfold Mixed.dgap
      linarith [min_le_left (Mixed.beta (q+2) a r)
        ((OAI.PackingSufficiencySupport.largeModelMean (q+2) (Mixed.h1 (q+2) a r) (Mixed.h2 (q+2) a r)-
          (∑ i,r i^(q+2+2))/((q+2+2).factorial:ℝ))/2)]
    have hb := OAI.PackingSufficiencySupport.largeModelDensity_lower (q+2) hh2.le hp
    change Mixed.beta (q+2) a r≤(2:ℝ)^(q+2)*largeNormalCoefficient (q+2) p at hb
    nlinarith

#check_explicit mixedRawModel
end SymplecticPacking.HighDim.ToricPackingStages
