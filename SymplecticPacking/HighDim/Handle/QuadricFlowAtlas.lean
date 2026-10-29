import SymplecticPacking.HighDim.Handle.NativeModelAgreement
import SymplecticPacking.HighDim.Handle.QuadricModelPresentation
import SymplecticPacking.HighDim.Handle.QuadricRawGlobalCover
import SymplecticPacking.HighDim.Handle.QuadricRawModelSpec

/-!
# The flow atlas of the quadric model

A larger native finite atlas covers the entire closed packing region.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def quadricFlowAtlas (m ℓ : ℕ) := quadricModelRawPresentation m (ℓ+2)

theorem quadricRawHandle_cover_ambient (m : ℕ) :
    (Subtype.val : Surface m → Affine (m+2)) ∘ (quadricRawHandle m).cover=
      (quadricRawHandle m).ambientCover := by
  funext y
  exact (QuadricRawDual.transverseCover_eq m y).symm

theorem transport_raw_inclusion {q : ℕ} {a b : Fin q → ℂ} (hab : a=b)
    {r s : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : D.inclusion=Subtype.val) :
    (transportQuadricPresentation hab hrs D).inclusion=Subtype.val := by
  subst b
  subst s
  exact hD

theorem quadricFlowAtlas_inclusion (m ℓ : ℕ) :
    (quadricFlowAtlas m ℓ).inclusion=(Subtype.val : Surface m → Affine (m+2)) :=
  transport_raw_inclusion (quadricRationalParameters_cast m)
    (quadricFiniteSupportRadius_exhaustion m (ℓ+2)) _ rfl

theorem quadric_inclusion_immersion (m : ℕ) (x : Surface m) :
    Injective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) := by
  let l : Affine (m+2) →L[ℝ] Plane := Complex.equivRealProdCLM.toContinuousLinearMap.comp
    ((curveCoordinate (normalChartAt (parameters m) x).coordinate).restrictScalars ℝ)
  have he : (extChartAt 𝓘(ℝ,Plane) x : Surface m → Plane)=l ∘ Subtype.val := by
    funext y
    rfl
  have hl : ContMDiff 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Plane) ∞ l := l.contDiff.contMDiff
  have hd := mfderiv_comp x (hl.mdifferentiable (by simp) x.val)
    ((real_inclusion_contMDiff (parameters m)).mdifferentiable (by simp) x)
  rw [←he,mfderiv_eq_fderiv,l.fderiv] at hd
  obtain ⟨e,he⟩ := isInvertible_mfderiv_extChartAt (I:=𝓘(ℝ,Plane)) (mem_extChartAt_source x)
  intro u v huv
  apply e.injective
  change e.toContinuousLinearMap u=e.toContinuousLinearMap v
  rw [he,hd]
  exact congrArg l huv

theorem transport_raw_cover {q : ℕ} {a b : Fin q → ℂ} (hab : a=b)
    {r s R : ℝ} (hrs : r=s)
    (D : RawSurfacePresentation (Affine q) (locus a) (interior (projectionDomain a r)))
    (hD : projectionDomain a R⊆⋃ i,(D.boxes i).box.inner) :
    projectionDomain b R⊆⋃ i,((transportQuadricPresentation hab hrs D).boxes i).box.inner := by
  subst b
  subst s
  exact hD

theorem quadricFlowAtlas_cover (m ℓ : ℕ) {x : Surface m}
    (hx : x∈projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)) :
    ∃ i,x∈((quadricFlowAtlas m ℓ).boxes i).box.inner := by
  have hc := transport_raw_cover (quadricRationalParameters_cast m)
    (quadricFiniteSupportRadius_exhaustion m (ℓ+2)) _
    (quadricFinitePresentation_cover (quadricRationalParameters m)
      (quadricFiniteSupportRadius_pos m (ℓ+2))
      (quadricRationalParameters_sep₀ m) (quadricRationalParameters_sep m)
      (quadricFiniteSupportRadius_branch_core m (ℓ+2)))
  apply mem_iUnion.mp (hc ?_)
  change ‖x.val.1‖≤_ at hx ⊢
  have he := quadricFiniteSupportRadius_exhaustion m ℓ
  have hr : (quadricFiniteSupportRadius m (ℓ+2):ℝ)=
      (quadricFiniteSupportRadius m ℓ:ℝ)+2 := by
    simp only [quadricFiniteSupportRadius]
    push_cast
    ring
  linarith

local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _

theorem quadricFlowAtlas_spec {m n q : ℕ} (ℓ : ℕ)
    (T : RawToricModel (Affine (m+2)) (Surface m) n q)
    (hι : T.presentation.inclusion=Subtype.val)
    (hb : T.base=projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)) :
    RawFlowAtlasSpec T (quadricFlowAtlas m ℓ) where
  inclusion_eq := (quadricFlowAtlas_inclusion m ℓ).trans hι.symm
  inclusion_smooth := by
    rw [quadricFlowAtlas_inclusion]
    exact real_inclusion_contMDiff _
  immersion := by
    rw [quadricFlowAtlas_inclusion]
    exact quadric_inclusion_immersion m
  regularity := by
    change AmbientRegularity (K:=Plane × Fibre n)
      (fun x : Surface m × Fibre n => ((quadricFlowAtlas m ℓ).inclusion x.1,x.2))
    rw [quadricFlowAtlas_inclusion]
    apply productAmbientRegularity_of_rawCover
    intro x
    obtain ⟨B,hB,hs,hi,hx⟩ := quadric_raw_global_cover (parameters m) x
    exact ⟨B,hB,hs,hx⟩
  box_smooth := (quadricModelRawPresentation_geometry m (ℓ+2)).box_smooth
  box_inverse := (quadricModelRawPresentation_geometry m (ℓ+2)).box_inverse
  base_cover := by
    intro x hx
    exact quadricFlowAtlas_cover m ℓ (hb ▸ hx)

#check_explicit quadricFlowAtlas
end SymplecticPacking.HighDim.ToricPackingStages
