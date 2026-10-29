import SymplecticPacking.HighDim.Handle.NativePackingAnalytic
import SymplecticPacking.HighDim.Handle.NativeLayerComparison
import SymplecticPacking.HighDim.Handle.NativeFlowComparison
import SymplecticPacking.HighDim.Handle.LayerPackingFormula

/-!
# Specification of the native packing formula

The native packing formula inherits the geometric packing theorem, with every
normalization and comparison estimate proved from the raw construction.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawToricModel.normalPrimitive RawToricModel.handleMass
  horizontalPath productCouplingPrimitive semanticFullOneForm

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [NormalSpace M] [SigmaCompactSpace M] {m q k : ℕ}

namespace RawModelAgreement
variable {T : RawToricModel E M m q} {S : ToricModel M m q} (h : RawModelAgreement T S)
include h

/-- The native layer maps satisfy the closed-ball embedding, containment,
and pairwise disjointness conclusions. -/
theorem native_layerMaps_spec (hS : S.Spec)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion)
    (hambient : T.presentation.inclusion ∘ T.handle.cover=T.handle.ambientCover)
    {D : ComparisonDatum m} {P : Moments m → ℝ} {gap : ℝ} (hD : D.Spec S.Δ P gap)
    (hN : RawNormalizationSpec T D.reserve (S.baseArea hS))
    {a r : Fin k → ℝ} (hr : ∀ i,0 ≤ r i) (hra : ∀ i,r i < a i)
    {τ : ℝ} (hτ : τ<1)
    (hcap : ∀ i p,(∀ j,0 ≤ p j) → ∑ j,p j ≤ a i → p∈(S.Δ.dilate τ).set) :
    (∀ i,FormNeighborhoodEmbedding (OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (fun _ => successorStandardForm m)
      (layerFormOf S (fibreIsotopy D) D.K (T.handleMass D.reserve)
        (fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive D.reserve p)) a r)
      (T.layerMaps D a r i)) ∧
    (∀ i,MapsTo (T.layerMaps D a r i) (OAI.PackingSufficiencySupport.closedBall (m+1) (r i)) (interior S.region)) ∧
    Pairwise (fun i j => Disjoint
      (T.layerMaps D a r i '' OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (T.layerMaps D a r j '' OAI.PackingSufficiencySupport.closedBall (m+1) (r j))) := by
  let Γ := fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive D.reserve p)
  have hΓ : SmoothOneFormFamily Γ := semanticOneForm_family_smooth hι hN.primitive_smooth
  obtain ⟨γ,W,hW,hBW,hWA,hγ,hdγ,hform⟩ := h.normalization_normal_form hι hN
  have hE := layerMapsOf_spec_of_normal_form S hS (fibreIsotopy D) hD.K_smooth hN.mass_smooth hΓ
    hN.background_pos (h.normalization_annular_exterior hN 0) hW hBW hWA hform
    (fibreIsotopy_preserves_both hD) hr hra
    (fun i p hp hs => layerMomentDomain_of_dilate S hS.Δ_spec hτ (hcap i p hp (hs.trans (hra i).le)))
  have he : T.layerMaps D a r=layerMapsOf S (fibreIsotopy D) D.K (T.handleMass D.reserve) Γ a r := by
    funext i
    exact h.layerMapsOf_eq hS hι hambient (fibreIsotopy D) D.K (T.handleMass D.reserve)
      (T.normalPrimitive D.reserve) a r i
  rw [he]
  exact hE
/-- Complete native assembly. Every analytic condition on the normalization and the
flow atlas is an output of the providers; the remaining hypotheses are precisely
the comparison gap and source-capacity conditions. -/
theorem native_packing_spec (hS : S.Spec) {U : Set M} {F : RawSurfacePresentation E M U}
    (hF : RawFlowAtlasSpec T F)
    (hambient : T.presentation.inclusion ∘ T.handle.cover=T.handle.ambientCover)
    {D : ComparisonDatum m} {P : Moments m → ℝ} {gap : ℝ} (hD : D.Spec S.Δ P gap)
    (hN : RawNormalizationSpec T D.reserve (S.baseArea hS))
    {a r : Fin k → ℝ} (hr : ∀ i,0 ≤ r i) (hra : ∀ i,r i < a i)
    {τ : ℝ} (hτ : τ<1)
    (hcap : ∀ i p,(∀ j,0 ≤ p j) → ∑ j,p j ≤ a i → p∈(S.Δ.dilate τ).set)
    (hP : ∀ p∈S.Δ.set,P p ≤ S.baseArea hS p-∑ i,max (a i-∑ j,p j) 0) :
    (∀ i,FormNeighborhoodEmbedding (OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (fun _ => successorStandardForm m) S.form (T.packing F D a r i)) ∧
    (∀ i,MapsTo (T.packing F D a r i) (OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (interior T.region)) ∧
    Pairwise (fun i j => Disjoint
      (T.packing F D a r i '' OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (T.packing F D a r j '' OAI.PackingSufficiencySupport.closedBall (m+1) (r j))) := by
  classical
  let rr := RawToricModel.packingSource a r
  let Γ := fun p => semanticOneForm T.presentation.inclusion (T.normalPrimitive D.reserve p)
  let H := T.handleMass D.reserve
  let Φ := fibreIsotopy D
  let Q₀ := toricInterp S.Γ Γ
  let Q₁ := handleFirstPath S.handle S.hb Φ H Γ
  let Q₂ := handleSecondPath S.handle S.hb Φ D.K H
    (fun i => smoothCap a rr i ∘ planeMoments)
    (fun i => layerClock (k+1) (-S.hb) S.hb i.castSucc)
    (layerClock (k+1) (-S.hb) S.hb (Fin.last k)) Γ
  let P₀ := T.relativePath D.reserve
  let P₁ := fun t v => T.firstHandlePath D (t,v)
  let P₂ := fun t v => T.secondHandlePath D a rr (t,v)
  let χ₀ := T.pathCutoff F P₀
  let χ₁ := T.pathCutoff F P₁
  let χ₂ := T.pathCutoff F P₂
  have hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion := hF.inclusion_eq ▸ hF.inclusion_smooth
  have htarget : TargetPrimitive S Γ := h.normalization_target hS hι hN
  have hΓ : SmoothOneFormFamily Γ := htarget.smooth
  have hregion : IsCompact T.region := h.region_eq.symm ▸ region_compact hS
  have hHr : ∀ p∈S.Δ.set,0 ≤ H p := fun p hp => hN.mass_nonneg p (h.polytope_eq.symm ▸ hp)
  have hHl : ∀ p∈S.Δ.set,S.baseArea hS p-D.reserve/16 ≤ H p :=
    fun p hp => hN.mass_lower p (h.polytope_eq.symm ▸ hp)
  have hΦ := fibreIsotopy_preserves_both hD
  have hbase := target_pos hS htarget
  obtain ⟨γ,W,hW,hBW,hWA,hγ,hdγ,hform⟩ := h.normalization_normal_form hι hN
  have hrr : ∀ i,rr i < a i := by intro i; change (3*a i+r i)/4 < a i; linarith [hra i]
  have hrr0 : ∀ i,0 ≤ rr i := by intro i; change 0 ≤ (3*a i+r i)/4; linarith [hr i,hra i]
  have hpq₀ : ∀ t v,semanticOneForm T.presentation.inclusion (P₀ t v)=Q₀ (t,v) := h.relativePath_semantic D.reserve
  have hpq₁ : ∀ t v,semanticOneForm T.presentation.inclusion (P₁ t v)=Q₁ (t,v) := fun t v => h.firstPath_semantic D (t,v)
  have hpq₂ : ∀ t v,semanticOneForm T.presentation.inclusion (P₂ t v)=Q₂ (t,v) := fun t v => h.secondPath_semantic D a rr (t,v)
  have hs₀ : SmoothOneFormFamily Q₀ :=
    (toricPrimitiveInterpolation_smooth hS.Γ_smooth hΓ).comp
      (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))
  have hi₀ : ∀ t∈Icc (0:ℝ) 1,∀ z∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q₀ t) z).IsInvertible := by
    intro t ht z hz
    have hz' : z∈S.region := h.region_eq ▸ hz
    have hqt : SmoothOneFormFamily (fun v : Fibre m => Q₀ (t,v)) := by
      simpa only [Function.comp_def,id_eq] using hs₀.comp
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : Fibre m => t)).prodMk contDiff_id)
    rw [horizontalPath,productCouplingPrimitive_exterior (Γ:=fun v => Q₀ (t,v))
      phaseArea phaseArea_skew hqt z]
    exact toricPrimitiveInterpolation_isInvertible hS.Γ_smooth hΓ ht z
      (model_pos hS _ hz'.2 _ hz'.1) (hbase _ hz'.2 _ hz'.1)
  have hs₁ : SmoothOneFormFamily Q₁ :=
    globalSurfaceFirstPrimitive_smooth S.handle hS.hb_pos hS.hb_lt Φ
      (hN.mass_smooth.comp planeMoments_smooth) (hΓ.comp planeMoments_smooth)
  have hi₁ : ∀ t∈Icc (0:ℝ) 1,∀ z∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q₁ t) z).IsInvertible := by
    intro t ht z hz
    have hz' : z∈S.region := h.region_eq ▸ hz
    have hqt : SmoothOneFormFamily (fun v : Fibre m => Q₁ (t,v)) := by
      simpa only [Function.comp_def,id_eq] using hs₁.comp
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : Fibre m => t)).prodMk contDiff_id)
    rw [horizontalPath,productCouplingPrimitive_exterior (Γ:=fun v => Q₁ (t,v))
      phaseArea phaseArea_skew hqt z]
    exact globalSurfaceFirstPath_isInvertible S.handle hS.hb_pos hS.hb_lt hS.handle_orient
      hS.Λ_smooth hS.Λ_skew hS.Λ_pos hN.background_pos hγ hdγ hΓ hN.mass_smooth hHr hbase
      hW hBW hWA hform Φ hΦ ht hz'
  have hclock := layerClocks_spec (k+1) (by linarith [hS.hb_pos] : -S.hb < S.hb)
  have hlo := fun (s : ℝ) (hs : s ≤  -S.hb) => And.intro (fun i : Fin k => layerClock_lo hS.hb_pos i.castSucc hs)
    (layerClock_lo hS.hb_pos (Fin.last k) hs)
  have hhi := fun (s : ℝ) (hs : S.hb ≤ s) => And.intro (fun i : Fin k => layerClock_hi hS.hb_pos i.castSucc hs)
    (layerClock_hi hS.hb_pos (Fin.last k) hs)
  have hs₂ : SmoothOneFormFamily Q₂ :=
    globalSurfaceSecondPrimitive_smooth S.handle hS.hb_pos hS.hb_lt Φ
      (hD.K_smooth.comp planeMoments_smooth) (hN.mass_smooth.comp planeMoments_smooth)
      (fun i => (smoothCap_smooth a rr i).comp planeMoments_smooth)
      (fun i => (hclock.2.2.1 i.castSucc).1) (hclock.2.2.1 (Fin.last k)).1 hlo hhi
      (hΓ.comp planeMoments_smooth)
  have hres := native_surfaceRemainder_nonneg hD hHl hrr hP
  have hi₂ : ∀ t∈Icc (0:ℝ) 1,∀ z∈T.region,
      (manifoldExteriorOneForm (horizontalPath phaseArea Q₂ t) z).IsInvertible := by
    intro t ht z hz
    have hz' : z∈S.region := h.region_eq ▸ hz
    have hqt : SmoothOneFormFamily (fun v : Fibre m => Q₂ (t,v)) := by
      simpa only [Function.comp_def,id_eq] using hs₂.comp
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : Fibre m => t)).prodMk contDiff_id)
    rw [horizontalPath,productCouplingPrimitive_exterior (Γ:=fun v => Q₂ (t,v))
      phaseArea phaseArea_skew hqt z]
    exact globalSurfaceSecondPath_isInvertible S.handle hS.hb_pos hS.hb_lt hS.handle_orient
      hS.Λ_smooth hS.Λ_skew hS.Λ_pos hN.background_pos hγ hdγ hΓ hD.K_smooth hN.mass_smooth hHr hbase
      hW hBW hWA hform Φ hΦ
      (fun i => (smoothCap_smooth a rr i).comp planeMoments_smooth)
      (fun i => (hclock.2.2.1 i.castSucc).1) (hclock.2.2.1 (Fin.last k)).1 hlo hhi
      (fun i s => (hclock.2.2.2.1 i.castSucc s).2.2)
      (fun s => (hclock.2.2.2.1 (Fin.last k) s).2.2)
      (fun v _ i => smoothCap_nonneg (hrr i) _) hres ht hz'
  have hc₀ := hF.pathCutoff_spec hpq₀ hs₀ hregion hi₀
  have hc₁ := hF.pathCutoff_spec hpq₁ hs₁ hregion hi₁
  have hc₂ := hF.pathCutoff_spec hpq₂ hs₂ hregion hi₂
  obtain ⟨η,hη,hzero⟩ := hD.collar
  let Fface := fun ν (p : Moments m) => ∑ j,S.Δ.b ν j*p j
  let α := fun ν => S.Δ.ℓ ν-η
  have hface := fun ν => momentFace_smooth (S.Δ.b ν)
  have hα : ∀ ν,α ν<S.Δ.ℓ ν := fun ν => by dsimp [α];linarith
  have hY := planeRegion_outer_constraints S.Δ.b S.Δ.ℓ
  have hYC : IsCompact (planeMoments ⁻¹' S.Δ.set) := isCompact_preimage_planeMoments hS.Δ_spec.compact
  have hz : ∀ ν t v,α ν<(Fface ν ∘ planeMoments) v →
      fderiv ℝ (Fface ν ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0 := by
    intro ν t v hv
    have hh := hzero ν t v hv
    rw [fibreHamVF_eq_hamiltonianField hD.gen,←fibreIsotopy_hamiltonian hD.gen] at hh
    exact hh
  have hc₀' : MoserCutoff Q₀ χ₀ S.region := h.region_eq ▸ hc₀
  have hc₁' : MoserCutoff Q₁ χ₁ S.region := h.region_eq ▸ hc₁
  have hc₂' : MoserCutoff Q₂ χ₂ S.region := h.region_eq ▸ hc₂
  obtain ⟨K,hK,hKi,hstat⟩ := htarget.station
  obtain ⟨hD₀,hI₀,hf₀,_⟩ := toricMoserMap_spec hS.Γ_smooth hΓ hK hKi hstat
    (model_pos hS) hbase Fface hface α S.Δ.ℓ hα hY hYC
    hc₀'.smooth hc₀'.supp hc₀'.one hc₀'.compact
  obtain ⟨hD₁,hI₁,hf₁⟩ := handleMapCut_spec S hS Φ hD.K_smooth hN.mass_smooth hΓ hrr hHr hbase
    hN.background_pos hγ hdγ hW hBW hWA hform hΦ hres Fface hface α S.Δ.ℓ hα hY hYC hz
    (fun ν i => toric_collarInvariant (hface ν) (smoothCap_smooth a rr i) (α ν)) hc₁' hc₂'
  obtain ⟨hEbig,himEbig,hdisEbig⟩ := h.native_layerMaps_spec hS hι hambient hD hN hrr0 hrr hτ hcap
  have hsub (i : Fin k) : OAI.PackingSufficiencySupport.closedBall (m+1) (r i) ⊆ 
      OAI.PackingSufficiencySupport.closedBall (m+1) (rr i) := by
    intro z hz
    change OAI.PackingSufficiencySupport.capacity z ≤ r i at hz
    change OAI.PackingSufficiencySupport.capacity z ≤ rr i
    apply hz.trans
    change r i ≤ (3*a i+r i)/4
    linarith [hra i]
  have hE : ∀ i,FormNeighborhoodEmbedding (OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (fun _ => successorStandardForm m) (layerFormOf S Φ D.K H Γ a rr) (T.layerMaps D a rr i) := by
    intro i
    obtain ⟨V,hV,hBV,hs,he,hf⟩ := hEbig i
    exact ⟨V,hV,(hsub i).trans hBV,hs,he,hf⟩
  have himE : ∀ i,MapsTo (T.layerMaps D a rr i)
      (OAI.PackingSufficiencySupport.closedBall (m+1) (r i)) (interior S.region) :=
    fun i z hz => himEbig i (hsub i hz)
  have hdisE : Pairwise (fun i j => Disjoint
      (T.layerMaps D a rr i '' OAI.PackingSufficiencySupport.closedBall (m+1) (r i))
      (T.layerMaps D a rr j '' OAI.PackingSufficiencySupport.closedBall (m+1) (r j))) := by
    intro i j hij
    exact (hdisEbig hij).mono (image_mono (hsub i)) (image_mono (hsub j))
  obtain ⟨hpack₁,himage₁,hdis₁⟩ := transport_form_packing
    (fun i => OAI.PackingSufficiencySupport.closedBall (m+1) (r i)) (fun _ => successorStandardForm m)
    _ _ (handleMapCut S Φ D.K H Γ a rr χ₁ χ₂) hf₁ hD₁ hI₁ (T.layerMaps D a rr) hE himE hdisE
  have hpack := transport_form_packing
    (fun i => OAI.PackingSufficiencySupport.closedBall (m+1) (r i)) (fun _ => successorStandardForm m)
    _ _ (toricMoserMap S.Γ Γ χ₀) hf₀ hD₀ hI₀
    (fun i => (handleMapCut S Φ D.K H Γ a rr χ₁ χ₂).symm ∘ T.layerMaps D a rr i) hpack₁ himage₁ hdis₁
  have he₀ := hF.inverse_pathFlow_eq hpq₀ hs₀ hregion hi₀
  have he₁ := hF.inverse_pathFlow_eq hpq₁ hs₁ hregion hi₁
  have he₂ := hF.inverse_pathFlow_eq hpq₂ hs₂ hregion hi₂
  have heq (i : Fin k) : T.packing F D a r i=
      (toricMoserMap S.Γ Γ χ₀).symm ∘
        ((handleMapCut S Φ D.K H Γ a rr χ₁ χ₂).symm ∘ T.layerMaps D a rr i) := by
    change nativeInverse (T.pathFlow F P₀ 1) ∘ nativeInverse (T.pathFlow F P₁ 1) ∘
      nativeInverse (T.pathFlow F P₂ 1) ∘ T.layerMaps D a rr i=_
    rw [he₀,he₁,he₂]
    rfl
  simp_rw [heq]
  simpa only [h.region_eq,ToricModel.form,ToricModel.region,Polytope.set,planeRegion] using hpack
end RawModelAgreement
end SymplecticPacking.HighDim
