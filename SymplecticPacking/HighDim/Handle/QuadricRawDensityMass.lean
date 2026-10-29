import SymplecticPacking.HighDim.Handle.QuadricModelPresentation
import SymplecticPacking.HighDim.Handle.QuadricRawDensity

/-!
# Unit mass of the quadric handle density

The handle density has unit mass for the native calibrated finite integral.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _

 theorem quadricFiniteSupportRadius_three (m ℓ : ℕ) : (3:ℝ)≤quadricFiniteSupportRadius m ℓ := by
  have hs : (2:ℚ)≤∑ j : Fin (m+2),quadricRationalParameters m j := by
    calc
      2=quadricRationalParameters m 1 := by norm_num [quadricRationalParameters]
      _≤∑ j : Fin (m+2),quadricRationalParameters m j :=
        Finset.single_le_sum (fun j _ => by unfold quadricRationalParameters; positivity) (Finset.mem_univ 1)
  have h : (3:ℚ)≤quadricFiniteSupportRadius m ℓ := by
    unfold quadricFiniteSupportRadius
    linarith [Nat.cast_nonneg (α := ℚ) ℓ]
  exact_mod_cast h

 theorem quadricRawDensity_band_core (m ℓ : ℕ) {b : ℝ}
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    (BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band b ⊆
      projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ) := by
  intro x hx
  have h3 := BranchSmall.quadricHandleData_in_projection m
    (Or.inl (subset_closure ((BranchSmall.quadricHandleData m).image_band_subset_target hbw hx)))
  exact h3.trans (quadricFiniteSupportRadius_three m ℓ)

 theorem quadricRawDensity_zero_off_core (m ℓ : ℕ) {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) (x : Surface m)
    (hx : x∉projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)) :
    QuadricRawDensity.density m b x.val=0 :=
  QuadricRawDensity.density_zero m hb x (fun h => hx (quadricRawDensity_band_core m ℓ hbw h))

 theorem quadricRawDensity_calibratedMass (m ℓ : ℕ) {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    (quadricModelRawPresentation m ℓ).calibratedMass
      (fun x : Surface m => QuadricRawDensity.density m b x.val)=1 := by
  classical
  let K := projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)
  have hK : IsCompact K := projectionDomain_compact _ _
  let Boxes := fun B : compactSurfaceBoxes hK => B.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  have hs := QuadricRawDensity.density_contMDiff m hb hbw
  have hsk := QuadricRawDensity.density_skew m b
  have hz := quadricRawDensity_zero_off_core m ℓ hb hbw
  have hmass := quadricModelRawPresentation_mass_eq m ℓ hs hsk hz
  have hi := compactSurfaceFormIntegral_eq hK (positivePlaneTransitions _) Boxes ρ hρ
    (semanticTwoForm_smooth (real_inclusion_contMDiff _) hs)
    (fun x u v => hsk x _ _)
  have hind : K.indicator (semanticTwoForm Subtype.val
      (fun x : Surface m => QuadricRawDensity.density m b x.val))=
      semanticTwoForm Subtype.val (fun x : Surface m => QuadricRawDensity.density m b x.val) := by
    funext x
    by_cases hx : x∈K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,semanticTwoForm_zero_at (Subtype.val : Surface m → Affine (m+2))
        (Ω := fun x : Surface m => QuadricRawDensity.density m b x.val) (hz x hx)]
  rw [restrictedPartitionFormMass_eq_indicator _ _ hK.measurableSet,hind] at hi
  have hu := QuadricRawDensity.density_partition_mass m hb hbw
    ((image_mono ((BranchSmall.quadricHandleData m).core_subset_band b)).trans
      (quadricRawDensity_band_core m ℓ hbw)) Boxes ρ hρ
  exact hmass.trans (hi.trans hu)

 theorem quadricRawDensity_formMass (m ℓ : ℕ) {b : ℝ} (hb : 0<b)
    (hbw : b<(BranchSmall.quadricHandleData m).width) :
    (quadricModelRawPresentation m ℓ).formMass
      (fun x : Surface m => QuadricRawDensity.density m b x.val)=
      (quadricModelRawPresentation m ℓ).massCalibration := by
  have h := quadricRawDensity_calibratedMass m ℓ hb hbw
  unfold RawSurfacePresentation.calibratedMass at h
  exact (div_eq_one_iff_eq (quadricModelRawPresentation_calibration_ne_zero m ℓ)).mp h

end SymplecticPacking.HighDim.ToricPackingStages
