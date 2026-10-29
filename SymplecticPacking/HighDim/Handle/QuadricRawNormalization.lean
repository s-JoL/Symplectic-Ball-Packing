import SymplecticPacking.HighDim.Handle.QuadricRawNormalForm
import SymplecticPacking.HighDim.Handle.QuadricRawDensityMass
import SymplecticPacking.HighDim.Handle.QuadricModelPresentationCore
import SymplecticPacking.HighDim.Handle.QuadricNativeFloor
import SymplecticPacking.HighDim.Handle.QuadricBoundaryCutoff
import SymplecticPacking.HighDim.Handle.RawCutoffNormalization
import SymplecticPacking.HighDim.Handle.RawCalibratedCorrection

/-!
# Primitive correction and annular normalizer for the quadric families

The finite primitive correction and annular normalizer for all three quadric-base families.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix

variable (m ℓ : ℕ)

def quadricNormalizationCutoff (x : Surface m) : ℝ :=
  1-quadricBoundaryCutoff (exhaustionRadius (parameters m) ℓ-2)
    (exhaustionRadius (parameters m) ℓ-1) x

 theorem quadricFiniteSupportRadius_four : (4:ℝ)≤quadricFiniteSupportRadius m ℓ := by
  have hs : (3:ℚ)≤∑ j : Fin (m+2),quadricRationalParameters m j := by
    calc
      3=∑ j∈({0,1} : Finset (Fin (m+2))),quadricRationalParameters m j := by
        norm_num [quadricRationalParameters,Fin.ext_iff]
      _≤∑ j : Fin (m+2),quadricRationalParameters m j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => by unfold quadricRationalParameters; positivity)
  have h : (4:ℚ)≤quadricFiniteSupportRadius m ℓ := by
    unfold quadricFiniteSupportRadius
    linarith [Nat.cast_nonneg (α := ℚ) ℓ]
  exact_mod_cast h

 theorem quadricNormalizationCutoff_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞
    (quadricNormalizationCutoff m ℓ) := contMDiff_const.sub (quadricBoundaryCutoff_smooth _ _)

 theorem quadricNormalizationCutoff_zero (x : Surface m)
    (hx : x∉projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)) :
    quadricNormalizationCutoff m ℓ x=0 := by
  change ¬‖x.val.1‖≤(quadricFiniteSupportRadius m ℓ:ℝ) at hx
  have hR := quadricFiniteSupportRadius_exhaustion m ℓ
  have hfour := quadricFiniteSupportRadius_four m ℓ
  have hn : exhaustionRadius (parameters m) ℓ-1≤‖x.val.1‖ := by
    have h := (lt_of_not_ge hx).le
    linarith
  unfold quadricNormalizationCutoff
  rw [quadricBoundaryCutoff_one (by linarith : 0≤exhaustionRadius (parameters m) ℓ-2)
    (by linarith : exhaustionRadius (parameters m) ℓ-2<exhaustionRadius (parameters m) ℓ-1) x hn,sub_self]

 theorem quadricNormalizationCutoff_handle (x : Surface m)
    (hx : x∈(BranchSmall.quadricHandleData m).chart.target) : quadricNormalizationCutoff m ℓ x=1 := by
  have h3 := BranchSmall.quadricHandleData_in_projection m (Or.inl (subset_closure hx))
  change ‖x.val.1‖≤3 at h3
  have hR := quadricFiniteSupportRadius_exhaustion m ℓ
  have hfour := quadricFiniteSupportRadius_four m ℓ
  unfold quadricNormalizationCutoff
  rw [quadricBoundaryCutoff_zero (by linarith : 0≤exhaustionRadius (parameters m) ℓ-2)
    (by linarith : exhaustionRadius (parameters m) ℓ-2<exhaustionRadius (parameters m) ℓ-1) x (by linarith),sub_zero]

variable {n : ℕ}
def quadricNormalizationRemoved (c : ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) :=
  rawCutoffRemoved (quadricNormalizationCutoff m ℓ) c (quadricReferenceForm m) Ω

def quadricNormalizationMass (c : ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
    (p : Moments n) : ℝ :=
  (quadricModelRawPresentation m ℓ).calibratedMass (quadricNormalizationRemoved m ℓ c Ω p)

def quadricRedistributedPrimitive (c : ℝ)
    (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
    (p : Moments n) : Surface m → Affine (m+2) →L[ℝ] ℝ :=
  Γ p+(quadricModelRawPresentation m ℓ).calibratedCorrection
    (fun x : Surface m => QuadricRawDensity.density m (1/16) x.val) (quadricNormalizationRemoved m ℓ c Ω p)

def quadricNormalizedPrimitive (c : ℝ)
    (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) :=
  QuadricRawAnnular.normalize m (1/16) (quadricRedistributedPrimitive m ℓ c Γ Ω)
    (QuadricRawAnnular.normalModel m (1/16) c (quadricNormalizationMass m ℓ c Ω))

 theorem quadricNormalization_width : (1:ℝ)/16<(BranchSmall.quadricHandleData m).width := by
  change 1/16<BranchSmall.explicitCylinderWidth m/2
  norm_num [BranchSmall.explicitCylinderWidth]

variable (c : ℝ)
  {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
  (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Ω q.1 q.2))

include hΩ in
 theorem quadricNormalizationRemoved_smooth :
    ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
      𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : Moments n × Surface m => quadricNormalizationRemoved m ℓ c Ω q.1 q.2) :=
  rawCutoffRemoved_smooth (quadricNormalizationCutoff_smooth m ℓ) c (quadricReferenceForm_smooth m) hΩ

 theorem quadricNormalizationRemoved_zero (p : Moments n) (x : Surface m)
    (hx : x∉projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ)) :
    quadricNormalizationRemoved m ℓ c Ω p x=0 :=
  rawCutoffRemoved_zero c _ _ (quadricNormalizationCutoff_zero m ℓ x hx) p

include hΩ in
 theorem quadricNormalizationMass_smooth : ContDiff ℝ ∞ (quadricNormalizationMass m ℓ c Ω) :=
  (quadricModelRawPresentation m ℓ).calibratedMass_family_smooth
    (quadricModelRawPresentation_geometry m ℓ) (quadricNormalizationRemoved_smooth m ℓ c hΩ)
    (projectionDomain_compact _ _) (quadricNormalizationRemoved_zero m ℓ c)

include hΩ in
 theorem quadricRedistributedPrimitive_smooth
    {Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
      𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Γ q.1 q.2)) :
    ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
      𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : Moments n × Surface m => quadricRedistributedPrimitive m ℓ c Γ Ω q.1 q.2) :=
  hΓ.add ((quadricModelRawPresentation m ℓ).calibratedCorrection_family_smooth
    (quadricModelRawPresentation_geometry m ℓ)
    (QuadricRawDensity.density_contMDiff m (by norm_num) (quadricNormalization_width m))
    (quadricNormalizationRemoved_smooth m ℓ c hΩ) (projectionDomain_compact _ _) (projectionDomain_compact _ _)
    (quadricRawDensity_zero_off_core m ℓ (by norm_num) (quadricNormalization_width m))
    (quadricNormalizationRemoved_zero m ℓ c))

#check_explicit quadricNormalizedPrimitive
end SymplecticPacking.HighDim.ToricPackingStages
