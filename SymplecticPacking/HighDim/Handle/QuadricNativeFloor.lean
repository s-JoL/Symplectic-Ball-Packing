import SymplecticPacking.HighDim.Handle.QuadricPresentationPositive
import SymplecticPacking.HighDim.Handle.RawDensityFloor
import SymplecticPacking.BranchSmall.QuadricRawForms

/-!
# Native coefficient floor of the quadric

A native coefficient floor over the finite quadric presentation.
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

def quadricReferenceForm (m : ℕ) (x : Surface m) : Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ :=
  BranchSmall.RawQuadric.ambientFSForm (1/Real.pi) x.val

theorem quadricReferenceForm_semantic (m : ℕ) :
    semanticTwoForm (Subtype.val : Surface m → Affine (m+2)) (quadricReferenceForm m)=
      curveFSForm (parameters m) (1/Real.pi) := by
  funext x
  exact (BranchSmall.RawQuadric.curveFSForm_eq_raw (parameters m) (1/Real.pi) x).symm

theorem quadricReferenceForm_smooth (m : ℕ) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (quadricReferenceForm m) :=
  BranchSmall.RawQuadric.ambientFSForm_restriction_contMDiff (parameters m) (1/Real.pi)

theorem quadricReferenceForm_coefficient_positive (m ℓ : ℕ)
    (i : Fin ((quadricModelRawPresentation m ℓ).size+1)) (z : Plane)
    (hz : z∈((quadricModelRawPresentation m ℓ).boxes i).box.chart.target) :
    0<quadricReferenceForm m (((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z)
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (1,0))
      (((quadricModelRawPresentation m ℓ).boxes i).frame z (0,1)) := by
  apply quadricModelRawPresentation_coefficient_positive m ℓ (Ω := quadricReferenceForm m)
    (fun x u v => BranchSmall.RawQuadric.ambientFSForm_skew (1/Real.pi) x.val u v) _ i z hz
  intro x
  rw [quadricReferenceForm_semantic]
  exact curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) x (mem_extChartAt_target x)

variable {m n q : ℕ} (ℓ : ℕ) (Δ : Polytope n q)
  (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
  (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
    𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun q : Moments n × Surface m => Ω q.1 q.2))

include hΩ
theorem quadricNativeFloor_continuous
    (i : Fin ((quadricModelRawPresentation m ℓ).size+1)) :
    ContinuousOn ((quadricModelRawPresentation m ℓ).rawFrameDensity Ω (quadricReferenceForm m) i)
      ((quadricModelRawPresentation m ℓ).rawFrameDomain Δ i) :=
  (quadricModelRawPresentation m ℓ).rawFrameDensity_continuousOn Δ
    (quadricModelRawPresentation_geometry m ℓ) hΩ (quadricReferenceForm_smooth m) i
    (fun z hz => (quadricReferenceForm_coefficient_positive m ℓ i z hz).ne')

def quadricNativeFloor (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty) : ℝ :=
  (quadricModelRawPresentation m ℓ).rawDensityFloor Δ Ω (quadricReferenceForm m) hΔc hΔn
    (quadricNativeFloor_continuous ℓ Δ Ω hΩ)

theorem quadricNativeFloor_pos (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
    (hsk : ∀ p x u v,Ω p x u v = -Ω p x v u)
    (hp : ∀ p∈Δ.set,∀ x∈projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ),
      0<chartTwoForm (semanticTwoForm Subtype.val (Ω p)) x
        (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)) :
    0<quadricNativeFloor ℓ Δ Ω hΩ hΔc hΔn := by
  apply (quadricModelRawPresentation m ℓ).rawDensityFloor_pos Δ Ω (quadricReferenceForm m)
    hΔc hΔn (quadricNativeFloor_continuous ℓ Δ Ω hΩ)
  intro i z hz
  have ht := ((quadricModelRawPresentation m ℓ).boxes i).box.closed_subset hz.2
  have hi : ((quadricModelRawPresentation m ℓ).boxes i).box.chart.symm z.2∈
      projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) :=
    interior_subset ((quadricModelRawPresentation m ℓ).inside i ⟨z.2,hz.2,rfl⟩)
  exact div_pos (quadricModelRawPresentation_coefficient_positive_at m ℓ (hsk z.1) i z.2 ht
    (hp z.1 hz.1 _ hi)) (quadricReferenceForm_coefficient_positive m ℓ i z.2 ht)

#check_explicit quadricNativeFloor
end SymplecticPacking.HighDim.ToricPackingStages
