import SymplecticPacking.HighDim.Handle.RawNormalizationSpec
import SymplecticPacking.HighDim.Handle.RawNormalPrimitiveQuadric

/-!
# Specification of the quadric normalization

The finite quadric normalizer satisfies the complete common proof interface.
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

variable (m n q ℓ : ℕ) (Δ : Polytope n q)
  (Γ : Moments n → Surface m → Affine (m+2) →L[ℝ] ℝ)
  (Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ)
  (floor reserve : ℝ) (outer : Moments n → ℝ)
local notation "T" => quadricRawModelOf m n q ℓ Δ Γ Ω floor

theorem quadricRawModelOf_referencePrimitive :
    semanticOneForm (Subtype.val : Surface m → Affine (m+2)) ((T).referencePrimitive)=
      curveFSPrimitive (parameters m) (1/Real.pi) := by
  funext x
  exact (BranchSmall.RawQuadric.curveFSPrimitive_eq_raw (parameters m) (1/Real.pi) x).symm

 theorem quadricRawModelOf_normalizationSpec
    (hΓ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun z : Moments n × Surface m => Γ z.1 z.2))
    (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
      𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (fun z : Moments n × Surface m => Ω z.1 z.2))
    (hsk : ∀ p x u v,Ω p x u v = -Ω p x v u)
    (hdΓ : ∀ p,RawIsPrimitive (Subtype.val : Surface m → Affine (m+2)) (Ω p) (Γ p))
    (hf : 0<floor) (hr : 0<reserve)
    (hpos : ∀ p∈Δ.set,∀ b y,y∈(extChartAt 𝓘(ℝ,Plane) b).target →
      (extChartAt 𝓘(ℝ,Plane) b).symm y∈projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) →
      0<chartTwoForm (semanticTwoForm Subtype.val (Ω p)) b y (1,0) (0,1))
    (hbudget : ∀ p∈Δ.set,outer p-reserve/16≤quadricNormalizationMass m ℓ ((T).backgroundCoefficient reserve) Ω p)
    (houter : ∀ p∈Δ.set,reserve/16≤outer p) : RawNormalizationSpec T reserve outer := by
  let c := (T).backgroundCoefficient reserve
  have hi : (T).presentation.inclusion=Subtype.val := quadricModelRawPresentation_inclusion m ℓ
  have hdual : semanticOneForm (Subtype.val : Surface m → Affine (m+2)) (T).handle.dual=
      (BranchSmall.quadricHandleData m).dual := quadricRawHandle_dual m
  have hn := quadricRawModelOf_normalPrimitive m n q ℓ Δ Γ Ω floor reserve
  have hmass : (T).handleMass reserve=quadricNormalizationMass m ℓ c Ω := rfl
  have hc : 0<c := (T).backgroundCoefficient_pos hr (by change 0<(2:ℝ)^(m+2); positivity) hf
  have hH (p) (hp : p∈Δ.set) : 0≤quadricNormalizationMass m ℓ c Ω p := by
    linarith [hbudget p hp,houter p hp]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hc,?_,?_,?_,?_⟩
  · rw [hn]
    exact quadricNormalizedPrimitive_smooth m ℓ c hΓ hΩ hsk hdΓ
  · intro p
    rw [hi,hn]
    exact quadricNormalizedPrimitive_exterior m ℓ c hΓ hΩ hsk hdΓ p
  · intro p x hx
    have href : semanticTwoForm (Subtype.val : Surface m → Affine (m+2)) (T).referenceForm=
        curveFSForm (parameters m) (1/Real.pi) := quadricReferenceForm_semantic m
    have hη : semanticTwoForm (Subtype.val : Surface m → Affine (m+2)) (T).handleDensity=
        (BranchSmall.quadricHandleData m).density (1/16) :=
      QuadricRawDensity.density_semantic m (b := (1:ℝ)/16) (by norm_num) (quadricNormalization_width m)
    have hxt : x∈(BranchSmall.quadricHandleData m).chart.target := by
      change x∈(quadricRawHandle m).target at hx
      rwa [quadricRawHandle_target] at hx
    rw [hi,hn,href,hη,hmass]
    exact quadricNormalizedPrimitive_annular_exterior m ℓ c hΓ hΩ hsk hdΓ p x hxt
  · refine ⟨quadricNormalizedSupport m ℓ,quadricNormalizedSupport_compact m ℓ,quadricNormalizedSupport_inside m ℓ,?_⟩
    intro p x hx
    rw [hi,hn]
    exact quadricNormalizedPrimitive_off_support m ℓ c hΓ hΩ hsk hdΓ p x hx
  · intro p hp b y hy hx
    rw [hi,hn]
    exact quadricNormalizedPrimitive_positive m ℓ c hΓ hΩ hsk hdΓ hc p (hH p hp) b y hy
      (hpos p hp b y hy hx)
  · exact (ambientFSPrimitive_smooth (1/Real.pi)).contMDiff.comp (real_inclusion_contMDiff (parameters m))
  · rw [hi,quadricRawModelOf_referencePrimitive]
    exact (curveFSPrimitive_exterior (parameters m) (1/Real.pi)).trans (quadricReferenceForm_semantic m).symm
  · refine ⟨annularNormalizeRegion (BranchSmall.quadricHandleData m) (1/16),
      annularNormalizeRegion_open _ _,?_,?_,?_⟩
    · exact annularNormalizeRegion_band _ (quadricNormalization_width m)
    · intro x hx
      change x∈(quadricRawHandle m).target
      rw [quadricRawHandle_target]
      exact hx.1
    · intro p x hx
      rw [hi,hn,quadricRawModelOf_referencePrimitive,hdual,
        quadricNormalizedPrimitive_on_handle m ℓ c hΓ hΩ hsk hdΓ p x hx]
      have hinv := congrArg (fun f : Surface m → HandleCylinder => (f x).1) (quadricRawHandle_inverse m)
      change _+(_*_) • _ = _+(intervalClock (-(1/16)) (1/16) ((quadricRawHandle m).inverse x).1*_ ) • _
      rw [hinv]
      rfl
  · rw [hmass]
    exact quadricNormalizationMass_smooth m ℓ c hΩ
  · intro p hp
    rw [hmass]
    exact hH p hp
  · intro p hp
    rw [hmass]
    exact hbudget p hp

end SymplecticPacking.HighDim.ToricPackingStages
