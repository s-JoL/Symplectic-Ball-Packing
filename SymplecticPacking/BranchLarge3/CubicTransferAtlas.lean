import SymplecticPacking.HighDim.Handle.QuadricModelPresentation
import SymplecticPacking.BranchLarge3.CubicBridge

/-!
# A finite quadric atlas of the physical source

A finite explicit quadric atlas covering the compact physical source.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold
open HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

def baseRadius (K : Set CubicPhysicalSpace) : ℝ :=
  sSup (insert 0 ((fun p : CubicPhysicalSpace => ‖p.1.val.1‖) '' K))

def atlasLevel (K : Set CubicPhysicalSpace) : ℕ := ⌈baseRadius K⌉₊+1

def atlas (K : Set CubicPhysicalSpace) :
    RawSurfacePresentation (Affine 2) BaseCurve
      (interior (projectionDomain (parameters 0) (exhaustionRadius (parameters 0) (atlasLevel K)))) :=
  quadricModelRawPresentation 0 (atlasLevel K)

theorem baseRadius_bound {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    {p : CubicPhysicalSpace} (hp : p∈K) : ‖p.1.val.1‖≤baseRadius K := by
  have hc : Continuous (fun p : CubicPhysicalSpace => ‖p.1.val.1‖) :=
    ((continuous_subtype_val.comp continuous_fst).fst).norm
  exact le_csSup ((hK.image hc).insert 0).bddAbove (mem_insert_of_mem 0 ⟨p,hp,rfl⟩)

theorem atlas_radius_bound {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    {p : CubicPhysicalSpace} (hp : p∈K) :
    ‖p.1.val.1‖≤(quadricFiniteSupportRadius 0 (atlasLevel K):ℝ) := by
  have hceil := Nat.le_ceil (baseRadius K)
  have hbound := baseRadius_bound hK hp
  change ‖p.1.val.1‖≤(1+∑ j : Fin (0+2),quadricRationalParameters 0 j+atlasLevel K:ℚ)
  push_cast
  have hsum : (0:ℝ)≤∑ j : Fin (0+2),(quadricRationalParameters 0 j:ℝ) :=
    Finset.sum_nonneg fun j hj => by
      dsimp [quadricRationalParameters]
      positivity
  unfold atlasLevel
  push_cast
  linarith

theorem transport_inclusion {q : ℕ} {a b : Fin q → ℂ} (hab : a=b) {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : D.inclusion=Subtype.val) :
    (transportQuadricPresentation hab hrs D).inclusion = Subtype.val := by
  subst b
  subst s
  exact hD

theorem atlas_inclusion (K : Set CubicPhysicalSpace) :
    (atlas K).inclusion=(Subtype.val : BaseCurve → Affine 2) := by
  exact transport_inclusion (quadricRationalParameters_cast 0)
    (quadricFiniteSupportRadius_exhaustion 0 (atlasLevel K)) _ rfl

theorem transport_cover {q : ℕ} {a b : Fin q → ℂ} (hab : a=b) {r s R : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : projectionDomain a R ⊆ ⋃ i,(D.boxes i).box.inner) :
    projectionDomain b R ⊆ ⋃ i,((transportQuadricPresentation hab hrs D).boxes i).box.inner := by
  subst b
  subst s
  exact hD

theorem atlas_cover {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    {p : CubicPhysicalSpace} (hp : p∈K) : ∃ i,p.1∈((atlas K).boxes i).box.inner := by
  have hc := transport_cover (quadricRationalParameters_cast 0)
    (quadricFiniteSupportRadius_exhaustion 0 (atlasLevel K)) _
    (quadricFinitePresentation_cover (quadricRationalParameters 0)
      (quadricFiniteSupportRadius_pos 0 (atlasLevel K))
      (quadricRationalParameters_sep₀ 0) (quadricRationalParameters_sep 0)
      (quadricFiniteSupportRadius_branch_core 0 (atlasLevel K)))
  exact mem_iUnion.mp (hc (atlas_radius_bound hK hp))

theorem atlas_geometry (K : Set CubicPhysicalSpace) : (atlas K).Geometry :=
  quadricModelRawPresentation_geometry 0 (atlasLevel K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem inclusion_mfderiv_injective (x : BaseCurve) :
    Injective (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) x) := by
  let l : Affine 2 →L[ℝ] RealModel := Complex.equivRealProdCLM.toContinuousLinearMap.comp
    ((curveCoordinate (normalChartAt (parameters 0) x).coordinate).restrictScalars ℝ)
  have he : (extChartAt 𝓘(ℝ,RealModel) x : BaseCurve → RealModel) =
      l ∘ (Subtype.val : BaseCurve → Affine 2) := by
    funext y
    rfl
  have hl : ContMDiff 𝓘(ℝ,Affine 2) 𝓘(ℝ,RealModel) ∞ l := l.contDiff.contMDiff
  have hd := mfderiv_comp x (hl.mdifferentiable (by simp) x.val)
    ((real_inclusion_contMDiff (parameters 0)).mdifferentiable (by simp) x)
  rw [←he,mfderiv_eq_fderiv,l.fderiv] at hd
  have hi := isInvertible_mfderiv_extChartAt (I:=𝓘(ℝ,RealModel)) (mem_extChartAt_source x)
  obtain ⟨e,he⟩ := hi
  intro u v huv
  apply e.injective
  change e.toContinuousLinearMap u = e.toContinuousLinearMap v
  rw [he,hd]
  exact congrArg l huv

#check_explicit atlasLevel
#check_explicit atlas
end SymplecticPacking.BranchLarge3.RawTransfer
