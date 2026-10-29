import SymplecticPacking.HighDim.Handle.QuadricFiniteMass
import SymplecticPacking.HighDim.Handle.QuadricModelTightFiniteAtlas

/-!
# The raw presentation of the quadric model

The finite raw presentation at the literal integer parameters of every quadric branch.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

variable {q : ℕ}

def transportQuadricPresentation {a b : Fin q → ℂ} (hab : a=b) {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r))) :
    RawSurfacePresentation (Affine q) (locus b) (interior (projectionDomain b s)) := by
  subst b
  subst s
  exact D

theorem transportQuadricPresentation_geometry {a b : Fin q → ℂ} (hab : a=b) {r s : ℝ} (hrs : r=s)
    [Fact (Injective a)] [Fact (∀ j,a j≠0)] [Fact (Injective b)] [Fact (∀ j,b j≠0)]
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : D.Geometry) : (transportQuadricPresentation hab hrs D).Geometry := by
  subst b
  subst s
  exact hD

theorem transportQuadricPresentation_calibration {a b : Fin q → ℂ} (hab : a=b)
    {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : D.massCalibration≠0) : (transportQuadricPresentation hab hrs D).massCalibration≠0 := by
  subst b
  subst s
  exact hD

section TransportMass
variable {a b : Fin q → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]
  [Fact (Injective b)] [Fact (∀ j,b j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a
local instance : SigmaCompactSpace (locus b) := curveSigmaCompact b

theorem transportQuadricPresentation_mass_eq (hab : a=b) {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r))) (t : ℝ)
    (hD : ∀ Ω : locus a → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine q →L[ℝ] Affine q →L[ℝ] ℝ) ∞ Ω →
      (∀ x u v,Ω x u v = -Ω x v u) → (∀ x,x∉projectionDomain a t → Ω x=0) →
      D.calibratedMass Ω=compactSurfaceFormIntegral (projectionDomain_compact a t)
        (semanticTwoForm Subtype.val Ω)) :
    ∀ Ω : locus b → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine q →L[ℝ] Affine q →L[ℝ] ℝ) ∞ Ω →
      (∀ x u v,Ω x u v = -Ω x v u) → (∀ x,x∉projectionDomain b t → Ω x=0) →
      (transportQuadricPresentation hab hrs D).calibratedMass Ω=
        compactSurfaceFormIntegral (projectionDomain_compact b t) (semanticTwoForm Subtype.val Ω) := by
  subst b
  subst s
  exact hD
end TransportMass

def quadricModelRawPresentation (m ℓ : ℕ) :
    RawSurfacePresentation (Affine (m+2)) (Surface m)
      (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ))) :=
  transportQuadricPresentation (quadricRationalParameters_cast m)
    (quadricFiniteSupportRadius_exhaustion m ℓ)
    (quadricFinitePresentation (quadricRationalParameters m) (quadricFiniteSupportRadius_pos m ℓ)
      (quadricRationalParameters_sep₀ m) (quadricRationalParameters_sep m)
      (quadricFiniteSupportRadius_branch_core m ℓ))

theorem quadricModelRawPresentation_geometry (m ℓ : ℕ) : (quadricModelRawPresentation m ℓ).Geometry :=
  transportQuadricPresentation_geometry _ _ _
    (quadricFinitePresentation_geometry (quadricRationalParameters m)
      (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
      (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ))

theorem quadricFiniteSupportRadius_one (m ℓ : ℕ) : (1:ℚ)≤quadricFiniteSupportRadius m ℓ := by
  unfold quadricFiniteSupportRadius quadricRationalParameters
  have hs : (0:ℚ)≤∑ j : Fin (m+2),((j.val:ℚ)+1) := Finset.sum_nonneg (fun _ _ => by positivity)
  linarith [Nat.cast_nonneg (α := ℚ) ℓ]

theorem quadricModelRawPresentation_calibration_ne_zero (m ℓ : ℕ) :
    (quadricModelRawPresentation m ℓ).massCalibration≠0 :=
  transportQuadricPresentation_calibration _ _ _
    (quadricFinitePresentation_calibration_ne_zero (quadricRationalParameters m)
      (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
      (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ)
      (quadricFiniteSupportRadius_one m ℓ))

local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _

theorem quadricModelRawPresentation_mass_eq (m ℓ : ℕ)
    {Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (hz : ∀ x,x∉projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ) → Ω x=0) :
    (quadricModelRawPresentation m ℓ).calibratedMass Ω=
      compactSurfaceFormIntegral (projectionDomain_compact (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ))
        (semanticTwoForm Subtype.val Ω) := by
  apply transportQuadricPresentation_mass_eq (quadricRationalParameters_cast m)
    (quadricFiniteSupportRadius_exhaustion m ℓ) _ _ _ Ω hΩ hsk hz
  intro Ξ hΞ hsΞ hzΞ
  exact quadricFinitePresentation_calibratedMass_eq (quadricRationalParameters m)
    (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
    (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ)
    (quadricFiniteSupportRadius_one m ℓ) hΞ hsΞ hzΞ

#check_explicit quadricModelRawPresentation
end SymplecticPacking.HighDim.ToricPackingStages
