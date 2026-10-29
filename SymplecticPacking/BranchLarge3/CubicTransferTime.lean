import SymplecticPacking.BranchLarge3.CubicTransferPrimitiveSpec
import SymplecticPacking.BranchLarge3.ExactSafetyRegularity
import SymplecticPacking.HighDim.Handle.RawFullProductFlowSpec

/-!
# The cubic transfer flow and its guard time

The native complete cubic transfer flow and its finite-guard time.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold
open HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

theorem cutField_core_eq {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Γ : ℝ → ManifoldOneForm E M)
    (χ : ℝ × M → ℝ) (p : ℝ × M) (hc : χ p=1) :
    cutField χ (fun s => manifoldExteriorOneForm (Γ s)) (manifoldTimePrimitive Γ) p =
      ExactCore.mfield Γ p := by
  rw [cutField,hc,one_smul]
  rfl

def nativeFlow (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (p : ℝ × CubicPhysicalSpace) : CubicPhysicalSpace :=
  (atlas K).fullMoserFlow (primitiveNative A B D S L K) (cutoff A B D S L K) p.1 p.2

def trajectoryGuards (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (i : Fin 9) (p : ℝ × CubicPhysicalSpace) : ℝ :=
  guards A B D S L K (p.1,nativeFlow A B D S L K p) i

/-- The finite-guard time uses only compact continuous scalar extrema, after the native
compact field and its complete flow have already been defined. -/
def safeTime (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : ℝ :=
  ExactSafety.time (trajectoryGuards A B D S L K) K
    (famEps A B D S (1/(L*Real.pi)) (compactBase A B D S L K) (compactFibre A B D S L K))

theorem nativeFlow_spec {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible) :
    0<gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K ∧
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicPhysicalModel) ∞
      (nativeFlow A B D S L K) (Ioo (-2:ℝ) 2 ×ˢ univ) ∧
    (∀ x,nativeFlow A B D S L K (0,x)=x) ∧
    ∀ x t,t∈Ioo (-2:ℝ) 2 →
      HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,CubicPhysicalModel)
        (fun s => nativeFlow A B D S L K (s,x)) t
        (((1:ℝ →L[ℝ] ℝ).smulRight (cutField (cutoff A B D S L K)
          (fun s => manifoldExteriorOneForm (semanticPrimitive A B D S L K s))
          (manifoldTimePrimitive (semanticPrimitive A B D S L K))
          (t,nativeFlow A B D S L K (t,x)))) : ℝ →L[ℝ] CubicPhysicalModel) := by
  have hι : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) ∞ (atlas K).inclusion := by
    rw [atlas_inclusion]
    exact real_inclusion_contMDiff (parameters 0)
  have hinj : ∀ x,Injective (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (atlas K).inclusion x) := by
    rw [atlas_inclusion]
    exact inclusion_mfderiv_injective
  have hregular : AmbientRegularity (K:=CubicPhysicalModel)
      ((atlas K).productInclusion (V:=PlanePhase (Fin 2))) := by
    change AmbientRegularity (K:=CubicPhysicalModel)
      (fun x : CubicPhysicalSpace => ((atlas K).inclusion x.1,x.2))
    rw [atlas_inclusion]
    apply productAmbientRegularity_of_rawCover
    intro x
    obtain ⟨B,hιB,hB,hs,hx⟩ := quadric_raw_global_cover (parameters 0) x
    exact ⟨B,hιB,hB,hx⟩
  have hα := semanticPrimitive_smooth hA hAB D S L hK hΞ
  have hg := gramSum_actual_smooth hA hAB D S L K
  have hpos : ∀ x∈K,0<gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) (0,x) := by
    intro x hx
    exact gramSum_pos_of_cover _ _ hι (atlas_geometry K).box_smooth _ hα
      (atlas_cover hK hx) (hinv0 x hx)
  have hμ := gramLevel_pos (atlas K) physicalBasis hK hg.continuous hpos
  let G : Set (ℝ × CubicPhysicalSpace) :=
    {p | 0<gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p}
  have hG : IsOpen G := isOpen_lt continuous_const hg.continuous
  have hGinv : ∀ p∈G,(manifoldExteriorOneForm (semanticPrimitive A B D S L K p.1) p.2).IsInvertible :=
    fun p hp => gramSum_nondegenerate _ _ hι (atlas_geometry K).box_smooth _ hα hp
  have hχG : tsupport (cutoff A B D S L K)⊆G :=
    transferCut_tsupport_gram _ _ _ _ K hg.continuous hμ
  have hχcover : ∀ p∈tsupport (cutoff A B D S L K),
      ∃ i,p.2.1∈((atlas K).boxes i).box.chart.source := by
    intro p hp
    exact (transferCut_tsupport_good _ _ _ hι (atlas_geometry K).box_smooth _ hα K
      hg.continuous hμ hp).1
  obtain ⟨hflow,h0,hamb,hODE⟩ := (atlas K).fullMoserFlow_spec hι hinj (atlas_geometry K).box_smooth
    hregular (primitiveNative A B D S L K) hα (cutoff A B D S L K)
    (cutoff_actual_smooth hA hAB D S L K) hG hGinv hχG hχcover
    (spatialCarrier_compact (atlas K) fibreBasis K)
    (transferCut_zero_off_carrier (atlas K) physicalBasis fibreBasis (primitiveAmbient A B D S L K) K)
  exact ⟨hμ,hflow,h0,hODE⟩

theorem trajectoryGuards_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible)
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K)) :
    ∀ i,ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,ℝ) ∞
      (trajectoryGuards A B D S L K i) (Ioo (-2:ℝ) 2 ×ˢ univ) := by
  have hΦ := (nativeFlow_spec hA hAB D S L hK hΞ hinv0).2.1
  have hg := guards_smooth A B D S L K (gramSum_actual_smooth hA hAB D S L K) hΞ hF
  intro i
  exact (hg i).comp_contMDiffOn (contMDiffOn_fst.prodMk hΦ)

theorem trajectoryGuards_regular {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible)
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K))
    (hsource : K⊆sourceDomain A B D S L K)
    (htarget : MapsTo (fun x => familyTarget A B D S L K (0,x)) K cubicAffineDomain) :
    ∀ i,ContinuousOn (fun x => trajectoryGuards A B D S L K i (0,x)) K ∧
      ContinuousOn (fun p : ℝ × CubicPhysicalSpace =>
        deriv (fun s => trajectoryGuards A B D S L K i (s,p.2)) p.1) (Icc (-1) 1 ×ˢ K) ∧
      (∀ x∈K,∀ s∈Icc (-1) 1,DifferentiableAt ℝ
        (fun r => trajectoryGuards A B D S L K i (r,x)) s) ∧
      ∀ x∈K,0<trajectoryGuards A B D S L K i (0,x) := by
  obtain ⟨hμ,hΦ,h0,hODE⟩ := nativeFlow_spec hA hAB D S L hK hΞ hinv0
  have hg := guards_smooth A B D S L K (gramSum_actual_smooth hA hAB D S L K) hΞ hF
  have htraj := trajectoryGuards_smooth hA hAB D S L hK hΞ hinv0 hF
  intro i
  have he : (fun x => trajectoryGuards A B D S L K i (0,x)) =
      (fun x => guards A B D S L K (0,x) i) := by
    funext x
    exact congrArg (fun y => guards A B D S L K (0,y) i) (h0 x)
  refine ⟨?_,ExactSafety.time_derivative_continuousOn (htraj i),?_,?_⟩
  · rw [he]
    exact ((hg i).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  · intro x hx s hs
    have hp : (s,x)∈Ioo (-2:ℝ) 2 ×ˢ (univ:Set CubicPhysicalSpace) :=
      ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,mem_univ _⟩
    have hf := ((htraj i (s,x) hp).contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).comp s
      (contMDiffAt_id.prodMk contMDiffAt_const)
    exact hf.contDiffAt.differentiableAt (by simp)
  · intro x hx
    rw [show trajectoryGuards A B D S L K i (0,x)=guards A B D S L K (0,x) i from congrFun he x]
    exact guards_initial_pos A B D S L hK (gramSum_actual_smooth hA hAB D S L K).continuous
      hμ hsource htarget hx i

theorem safeTime_good {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible)
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K))
    (hsource : K⊆sourceDomain A B D S L K)
    (htarget : MapsTo (fun x => familyTarget A B D S L K (0,x)) K cubicAffineDomain) :
    0<safeTime A B D S L K ∧ ExactCore.Good (semanticPrimitive A B D S L K) K
      (sourceDomain A B D S L K)
      (famEps A B D S (1/(L*Real.pi)) (compactBase A B D S L K) (compactFibre A B D S L K))
      (familyTarget A B D S L K) cubicAffineDomain (safeTime A B D S L K) := by
  have h := trajectoryGuards_regular hA hAB D S L hK hΞ hinv0 hF hsource htarget
  obtain ⟨hμ,hΦ,h0,hODE⟩ := nativeFlow_spec hA hAB D S L hK hΞ hinv0
  have hδ : 0<famEps A B D S (1/(L*Real.pi))
      (compactBase A B D S L K) (compactFibre A B D S L K) := CubicFamily.ePar_pos _ _
  have hτ : 0<safeTime A B D S L K := ExactSafety.time_pos
    (ExactSafety.clearance_pos hK (fun i => (h i).1) (fun i => (h i).2.2.2))
    (ExactSafety.speed_pos hK (fun i => (h i).2.1)) hδ
  have hreg (s : ℝ) (hs : s∈Icc (-1:ℝ) 1) (x : CubicPhysicalSpace) (hx : x∈K)
      (hp : ∀ i,0<trajectoryGuards A B D S L K i (s,x)) :
      (s,nativeFlow A B D S L K (s,x))∈ExactCore.region (semanticPrimitive A B D S L K)
        (sourceDomain A B D S L K) (familyTarget A B D S L K) cubicAffineDomain := by
    have hι : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) ∞ (atlas K).inclusion := by
      rw [atlas_inclusion]
      exact real_inclusion_contMDiff (parameters 0)
    have hα := semanticPrimitive_smooth hA hAB D S L hK hΞ
    exact ⟨gramSum_nondegenerate _ _ hι (atlas_geometry K).box_smooth _ hα
        (guards_gram_pos A B D S L K hμ hp),
      guards_source A B D S L K hp,guards_target A B D S L K hp⟩
  refine ⟨hτ,ExactSafety.good_of_flow hK (trajectoryGuards A B D S L K)
    (nativeFlow A B D S L K) (hΦ.continuousOn.mono ?_) (fun x hx => h0 x)
    (fun i => (h i).1) (fun i => (h i).2.1) (fun i => (h i).2.2.1)
    (fun i => (h i).2.2.2) hδ hreg ?_⟩
  · rintro ⟨s,x⟩ hsx
    exact ⟨⟨by linarith [hsx.1.1],by linarith [hsx.1.2]⟩,mem_univ _⟩
  · intro s hs x hx hp
    have hsO : s∈Ioo (-2:ℝ) 2 := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hd := hODE x s hsO
    have hc := guards_cut_eq_one A B D S L K hp
    rw [cutField_core_eq _ _ _ hc] at hd
    exact hd

#check_explicit nativeFlow
#check_explicit safeTime
end SymplecticPacking.BranchLarge3.RawTransfer
