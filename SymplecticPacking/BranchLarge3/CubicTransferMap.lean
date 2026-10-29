import SymplecticPacking.BranchLarge3.CubicTransferTime

/-!
# The cubic transfer as a Moser transport

The native cubic transfer agrees locally with the exact Moser transport.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold Filter
open HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

local instance : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

theorem restrict_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) {U V : Set X} (hVU : V⊆U)
    (hf : Topology.IsEmbedding (fun x : U => f x.val)) :
    Topology.IsEmbedding (fun x : V => f x.val) :=
  hf.comp (Topology.IsEmbedding.inclusion hVU)

def transferMap (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (x : CubicPhysicalSpace) : CubicAmbient :=
  familyTarget A B D S L K (safeTime A B D S L K,
    nativeFlow A B D S L K (safeTime A B D S L K,x))

theorem guards_region {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hμ : 0<gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K)
    {p : ℝ × CubicPhysicalSpace} (hp : ∀ i,0<guards A B D S L K p i) :
    p∈ExactCore.region (semanticPrimitive A B D S L K) (sourceDomain A B D S L K)
      (familyTarget A B D S L K) cubicAffineDomain := by
  have hι : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) ∞ (atlas K).inclusion := by
    rw [atlas_inclusion]
    exact real_inclusion_contMDiff (parameters 0)
  exact ⟨gramSum_nondegenerate _ _ hι (atlas_geometry K).box_smooth _
      (semanticPrimitive_smooth hA hAB D S L hK hΞ) (guards_gram_pos A B D S L K hμ hp),
    guards_source A B D S L K hp,guards_target A B D S L K hp⟩

theorem flow_eq_near {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible)
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K)) (hU : IsOpen (sourceDomain A B D S L K))
    (hsource : K⊆sourceDomain A B D S L K)
    (htarget : MapsTo (fun x => familyTarget A B D S L K (0,x)) K cubicAffineDomain) :
    ∃ W : Set CubicPhysicalSpace,IsOpen W ∧ K⊆W ∧ ∀ x∈W,
      ExactCore.flow (semanticPrimitive A B D S L K) (sourceDomain A B D S L K)
        (familyTarget A B D S L K) cubicAffineDomain (safeTime A B D S L K) x =
      nativeFlow A B D S L K (safeTime A B D S L K,x) := by
  let τ := safeTime A B D S L K
  let δ := famEps A B D S (1/(L*Real.pi)) (compactBase A B D S L K) (compactFibre A B D S L K)
  have hδ : 0<δ := CubicFamily.ePar_pos _ _
  have hτ := (safeTime_good hA hAB D S L hK hΞ hinv0 hF hsource htarget).1
  have hb := ExactSafety.time_bounds (trajectoryGuards A B D S L K) K δ
  have hτbound : τ≤1/4 := hb.2.1
  have h := trajectoryGuards_regular hA hAB D S L hK hΞ hinv0 hF hsource htarget
  have hclear := ExactSafety.clearance_pos hK (fun i => (h i).1) (fun i => (h i).2.2.2)
  obtain ⟨hμ,hΦ,h0,hODE⟩ := nativeFlow_spec hA hAB D S L hK hΞ hinv0
  have htraj := trajectoryGuards_smooth hA hAB D S L hK hΞ hinv0 hF
  let P : Set (ℝ × CubicPhysicalSpace) := ⋂ i : Fin 9,
    (Ioo (-2:ℝ) 2 ×ˢ univ) ∩ trajectoryGuards A B D S L K i ⁻¹' Ioi 0
  have hP : IsOpen P := isOpen_iInter_of_finite fun i =>
    (htraj i).continuousOn.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_univ) isOpen_Ioi
  have hPK : Icc (-τ) (2*τ) ×ˢ K ⊆ P := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    apply mem_iInter.mpr
    intro i
    refine ⟨⟨⟨by change -2<s; linarith [hs.1],by change s<2; linarith [hs.2]⟩,mem_univ _⟩,?_⟩
    have hsa : |s|≤2*τ := by rw [abs_le]; constructor <;> linarith [hs.1,hs.2]
    have hh := ExactSafety.guard_ge_half hK (fun j => (h j).1) (fun j => (h j).2.1)
      (fun j => (h j).2.2.1) (fun j => (h j).2.2.2) hδ i hx hsa
    change 0<trajectoryGuards A B D S L K i (s,x)
    linarith
  obtain ⟨V,W,hV,hW,hCV,hKW,hVW⟩ :=
    generalized_tube_lemma isCompact_Icc hK hP hPK
  refine ⟨W,hW,hKW,?_⟩
  intro x hx
  apply ExactCore.flow_eq (s:=τ) (x:=x) (γ:=fun r => nativeFlow A B D S L K (r,x))
    (semanticPrimitive_smooth hA hAB D S L hK hΞ)
    hU hF.continuous cubicAffineDomain_isOpen hτ.le (show 0<τ/2 by positivity)
  refine ⟨h0 x,?_⟩
  intro s hs
  have hsC : s∈Icc (-τ) (2*τ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsP : (s,x)∈P := hVW ⟨hCV hsC,hx⟩
  have hp : ∀ i,0<trajectoryGuards A B D S L K i (s,x) :=
    fun i => (mem_iInter.mp hsP i).2
  have hsO : s∈Ioo (-2:ℝ) 2 := (mem_iInter.mp hsP 0).1.1
  refine ⟨guards_region hA hAB D S L hK hΞ hμ hp,?_⟩
  have hd := hODE x s hsO
  rw [cutField_core_eq _ _ _ (guards_cut_eq_one A B D S L K hp)] at hd
  exact hd

theorem transfer_spec {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hinv0 : ∀ x∈K,(manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x).IsInvertible)
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K)) (hU : IsOpen (sourceDomain A B D S L K))
    (hsource : K⊆sourceDomain A B D S L K)
    (htarget : MapsTo (fun x => familyTarget A B D S L K (0,x)) K cubicAffineDomain)
    (hemb : ∀ t∈Ioc (0:ℝ) (famEps A B D S (1/(L*Real.pi))
      (compactBase A B D S L K) (compactFibre A B D S L K)),
      Topology.IsEmbedding (fun x : sourceDomain A B D S L K => familyTarget A B D S L K (t,x.val)))
    (Ω : ℝ → ManifoldTwoForm CubicAmbient CubicAmbient)
    (hform : ∀ t∈Ioc (0:ℝ) (famEps A B D S (1/(L*Real.pi))
      (compactBase A B D S L K) (compactFibre A B D S L K)),∀ x∈sourceDomain A B D S L K,
      manifoldExteriorOneForm (semanticPrimitive A B D S L K t) x =
        (Ω t (familyTarget A B D S L K (t,x))).bilinearComp
          (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel)
            (fun y => familyTarget A B D S L K (t,y)) x)
          (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel)
            (fun y => familyTarget A B D S L K (t,y)) x)) :
    safeTime A B D S L K∈Ioc (0:ℝ) (famEps A B D S (1/(L*Real.pi))
      (compactBase A B D S L K) (compactFibre A B D S L K)) ∧
    ∃ W : Set CubicPhysicalSpace,IsOpen W ∧ K⊆W ∧
      ContMDiffOn 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ (transferMap A B D S L K) W ∧
      Topology.IsEmbedding (fun x : W => transferMap A B D S L K x.val) ∧
      MapsTo (transferMap A B D S L K) W cubicAffineDomain ∧
      ∀ x∈W,∀ v w,Ω (safeTime A B D S L K) (transferMap A B D S L K x)
        (mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) (transferMap A B D S L K) x v)
        (mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) (transferMap A B D S L K) x w) =
        manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x v w := by
  have hΓ := semanticPrimitive_smooth hA hAB D S L hK hΞ
  have hδ : 0<famEps A B D S (1/(L*Real.pi))
      (compactBase A B D S L K) (compactFibre A B D S L K) := CubicFamily.ePar_pos _ _
  obtain ⟨hτ,hgood⟩ := safeTime_good hA hAB D S L hK hΞ hinv0 hF hsource htarget
  obtain ⟨ht,W,hW,hKW,hg,he,hT,hω⟩ := ExactCore.spec_at hΓ hK hinv0 hU hsource hδ hF
    hemb cubicAffineDomain_isOpen htarget hτ hgood Ω hform
  obtain ⟨Wn,hWn,hKWn,hn⟩ := flow_eq_near hA hAB D S L hK hΞ hinv0 hF hU hsource htarget
  let W' := W∩Wn
  let old := ExactCore.map (semanticPrimitive A B D S L K) (sourceDomain A B D S L K)
    (familyTarget A B D S L K) cubicAffineDomain (safeTime A B D S L K)
  change ContMDiffOn 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ old W at hg
  change Topology.IsEmbedding (fun x : W => old x.val) at he
  change MapsTo old W cubicAffineDomain at hT
  have heq : EqOn old (transferMap A B D S L K) W' := by
    intro x hx
    exact congrArg (fun y => familyTarget A B D S L K (safeTime A B D S L K,y)) (hn x hx.2)
  have hW' : IsOpen W' := hW.inter hWn
  refine ⟨ht,W',hW',fun x hx => ⟨hKW hx,hKWn hx⟩,
    (hg.mono inter_subset_left).congr (fun x hx => (heq hx).symm),?_,?_,?_⟩
  · have hfun : (fun x : W' => transferMap A B D S L K x.val) =
        (fun x : W' => old x.val) := funext fun x => (heq x.property).symm
    rw [hfun]
    exact restrict_embedding old (show W'⊆W from inter_subset_left) he
  · intro x hx
    rw [←heq hx]
    exact hT hx.1
  · intro x hx v w
    have hnear : transferMap A B D S L K =ᶠ[𝓝 x] old := by
      filter_upwards [hW'.mem_nhds hx] with y hy
      exact (heq hy).symm
    have hd := hnear.mfderiv_eq (I:=𝓘(ℝ,CubicPhysicalModel)) (I':=𝓘(ℝ,CubicAmbient))
    have hv := congrArg (fun f => f v) hd
    have hw := congrArg (fun f => f w) hd
    change mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) (transferMap A B D S L K) x v =
      mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) old x v at hv
    change mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) (transferMap A B D S L K) x w =
      mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) old x w at hw
    have hh := hω x hx.1 v w
    change Ω (safeTime A B D S L K) (old x)
      (mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) old x v)
      (mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) old x w) =
      manifoldExteriorOneForm (semanticPrimitive A B D S L K 0) x v w at hh
    rw [←hv,←hw,heq hx] at hh
    exact hh

#check_explicit transferMap
end SymplecticPacking.BranchLarge3.RawTransfer
