import SymplecticPacking.HighDim.Handle.QuadricModelPresentation
import SymplecticPacking.HighDim.Handle.QuadricRawCoefficientPositivity

/-!
# Orientation of the quadric presentation frames

Native finite presentation frames preserve the canonical complex orientation.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {q : ℕ} (a : Fin q → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j,(a j:ℂ)≠0)]
variable {R : ℚ} (hR : 0<R)
  (hsep₀ : ∀ i,1≤‖(a i:ℂ)‖)
  (hsep : ∀ i j,j≠i → 1≤‖(a i:ℂ)-(a j:ℂ)‖)
  (hbranch : ∀ i,‖(a i:ℂ)‖<(R:ℝ)^2)

theorem quadricFinitePresentation_coefficient_positive
    {Ω : locus (fun j => (a j:ℂ)) → Affine q →L[ℝ] Affine q →L[ℝ] ℝ}
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (hpos : ∀ x,0<chartTwoForm (semanticTwoForm Subtype.val Ω) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    (i : Fin ((quadricFinitePresentation a hR hsep₀ hsep hbranch).size+1))
    (z : Plane) (hz : z∈((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.target) :
    0<Ω (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.symm z)
      (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).frame z (1,0))
      (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).frame z (0,1)) := by
  let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch i.val)
  have hC : C.chart=rawQuadricRealChart C.centre C.tag C.regular := by
    rcases C with ⟨c,tag,hc⟩
    cases tag <;> rfl
  apply quadricRaw_coefficient_positive
    (quadricPresentationBox a hR hsep₀ hsep hbranch i) C.centre C.tag C.regular
    ((quadricTightRootChart_chart a hR.le hsep₀ hsep
      (quadricTreeAt a hR hsep₀ hsep hbranch i.val)).trans hC) rfl
    (quadricPresentationBox_smooth a hR hsep₀ hsep hbranch i) hsk z hz
  exact hpos _

theorem quadricFinitePresentation_coefficient_positive_at
    {Ω : locus (fun j => (a j:ℂ)) → Affine q →L[ℝ] Affine q →L[ℝ] ℝ}
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (i : Fin ((quadricFinitePresentation a hR hsep₀ hsep hbranch).size+1))
    (z : Plane) (hz : z∈((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.target)
    (hpos : 0<chartTwoForm (semanticTwoForm Subtype.val Ω)
      (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.symm z)
      (extChartAt 𝓘(ℝ,Plane) (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.symm z)
        (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.symm z)) (1,0) (0,1)) :
    0<Ω (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).box.chart.symm z)
      (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).frame z (1,0))
      (((quadricFinitePresentation a hR hsep₀ hsep hbranch).boxes i).frame z (0,1)) := by
  let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch i.val)
  have hC : C.chart=rawQuadricRealChart C.centre C.tag C.regular := by
    rcases C with ⟨c,tag,hc⟩
    cases tag <;> rfl
  apply quadricRaw_coefficient_positive
    (quadricPresentationBox a hR hsep₀ hsep hbranch i) C.centre C.tag C.regular
    ((quadricTightRootChart_chart a hR.le hsep₀ hsep
      (quadricTreeAt a hR hsep₀ hsep hbranch i.val)).trans hC) rfl
    (quadricPresentationBox_smooth a hR hsep₀ hsep hbranch i) hsk z hz
  exact hpos

variable {b : Fin q → ℂ} [Fact (Injective b)] [Fact (∀ j,b j≠0)]
theorem transportQuadricPresentation_coefficient_positive
    (hab : (fun j => (a j:ℂ))=b) {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus (fun j => (a j:ℂ)))
      (interior (projectionDomain (fun j => (a j:ℂ)) r)))
    (hD : ∀ Ω : locus (fun j => (a j:ℂ)) → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      (∀ x u v,Ω x u v = -Ω x v u) →
      (∀ x,0<chartTwoForm (semanticTwoForm Subtype.val Ω) x
        (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)) →
      ∀ (i : Fin (D.size+1)) (z : Plane),z∈(D.boxes i).box.chart.target →
        0<Ω ((D.boxes i).box.chart.symm z) ((D.boxes i).frame z (1,0)) ((D.boxes i).frame z (0,1))) :
    ∀ Ω : locus b → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      (∀ x u v,Ω x u v = -Ω x v u) →
      (∀ x,0<chartTwoForm (semanticTwoForm Subtype.val Ω) x
        (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)) →
      ∀ (i : Fin ((transportQuadricPresentation hab hrs D).size+1)) (z : Plane),
        z∈((transportQuadricPresentation hab hrs D).boxes i).box.chart.target →
        0<Ω (((transportQuadricPresentation hab hrs D).boxes i).box.chart.symm z)
          (((transportQuadricPresentation hab hrs D).boxes i).frame z (1,0))
          (((transportQuadricPresentation hab hrs D).boxes i).frame z (0,1)) := by
  subst b
  subst s
  exact hD

theorem transportQuadricPresentation_positive_at (hab : (fun j => (a j:ℂ))=b)
    {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus (fun j => (a j:ℂ)))
      (interior (projectionDomain (fun j => (a j:ℂ)) r)))
    (hD : ∀ Ω : locus (fun j => (a j:ℂ)) → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      (∀ x u v,Ω x u v = -Ω x v u) →
      ∀ (i : Fin (D.size+1)) (z : Plane),z∈(D.boxes i).box.chart.target →
        0<chartTwoForm (semanticTwoForm Subtype.val Ω) ((D.boxes i).box.chart.symm z)
          (extChartAt 𝓘(ℝ,Plane) ((D.boxes i).box.chart.symm z) ((D.boxes i).box.chart.symm z)) (1,0) (0,1) →
        0<Ω ((D.boxes i).box.chart.symm z) ((D.boxes i).frame z (1,0)) ((D.boxes i).frame z (0,1))) :
    ∀ Ω : locus b → Affine q →L[ℝ] Affine q →L[ℝ] ℝ,
      (∀ x u v,Ω x u v = -Ω x v u) →
      ∀ (i : Fin ((transportQuadricPresentation hab hrs D).size+1)) (z : Plane),
        z∈((transportQuadricPresentation hab hrs D).boxes i).box.chart.target →
        0<chartTwoForm (semanticTwoForm Subtype.val Ω)
          (((transportQuadricPresentation hab hrs D).boxes i).box.chart.symm z)
          (extChartAt 𝓘(ℝ,Plane) (((transportQuadricPresentation hab hrs D).boxes i).box.chart.symm z)
            (((transportQuadricPresentation hab hrs D).boxes i).box.chart.symm z)) (1,0) (0,1) →
        0<Ω (((transportQuadricPresentation hab hrs D).boxes i).box.chart.symm z)
          (((transportQuadricPresentation hab hrs D).boxes i).frame z (1,0))
          (((transportQuadricPresentation hab hrs D).boxes i).frame z (0,1)) := by
  subst b
  subst s
  exact hD

theorem quadricModelRawPresentation_coefficient_positive (m ℓ : ℕ)
    {Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (hpos : ∀ x,0<chartTwoForm (semanticTwoForm Subtype.val Ω) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    (i : Fin ((quadricModelRawPresentation m ℓ).size+1))
    (z : Plane) (hz : z∈((quadricModelRawPresentation m ℓ).boxes i).box.chart.target) :
    0<Ω (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (1,0))
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (0,1)) := by
  apply transportQuadricPresentation_coefficient_positive (quadricRationalParameters m)
    (quadricRationalParameters_cast m) (quadricFiniteSupportRadius_exhaustion m ℓ) _ _ Ω hsk hpos i z hz
  intro Ξ hs hp j y hy
  exact quadricFinitePresentation_coefficient_positive (quadricRationalParameters m)
    (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
    (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ) hs hp j y hy

theorem quadricModelRawPresentation_coefficient_positive_at (m ℓ : ℕ)
    {Ω : Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ}
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (i : Fin ((quadricModelRawPresentation m ℓ).size+1))
    (z : Plane) (hz : z∈((quadricModelRawPresentation m ℓ).boxes i).box.chart.target)
    (hpos : 0<chartTwoForm (semanticTwoForm Subtype.val Ω)
      (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)
      (extChartAt 𝓘(ℝ,Plane) (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)
        (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)) (1,0) (0,1)) :
    0<Ω (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (1,0))
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (0,1)) := by
  apply transportQuadricPresentation_positive_at (quadricRationalParameters m)
    (quadricRationalParameters_cast m) (quadricFiniteSupportRadius_exhaustion m ℓ) _ _ Ω hsk i z hz hpos
  intro Ξ hs j y hy hp
  exact quadricFinitePresentation_coefficient_positive_at (quadricRationalParameters m)
    (quadricFiniteSupportRadius_pos m ℓ) (quadricRationalParameters_sep₀ m)
    (quadricRationalParameters_sep m) (quadricFiniteSupportRadius_branch_core m ℓ) hs j y hy hp

end SymplecticPacking.HighDim.ToricPackingStages
