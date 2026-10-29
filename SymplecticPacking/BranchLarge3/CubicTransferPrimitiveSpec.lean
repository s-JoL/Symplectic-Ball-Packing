import SymplecticPacking.BranchLarge3.CubicTransferGuardSpec

/-!
# The native covector and the cubic degeneration primitive

Exact equality of the native covector with the cubic degeneration primitive.
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

def semanticPrimitive (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ℝ → ManifoldOneForm CubicPhysicalModel CubicPhysicalSpace :=
  fun t => semanticFullOneForm (atlas K).inclusion (primitiveNative A B D S L K t)

theorem primitiveAmbient_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ContDiff ℝ ∞ (primitiveAmbient A B D S L K) :=
  ambientCovector_contDiff hA hAB D S (1/(L*Real.pi)) L (CubicBridge.delta_pos A B L K) _ _

theorem primitive_semantic_eq {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K)) :
    semanticPrimitive A B D S L K =
      manifoldPullbackOneForm (famPrim A B D S (1/(L*Real.pi))
        (compactBase A B D S L K) (compactFibre A B D S L K)) (bridgeMap A B D S L K) := by
  have hIK := hK.image hΞ.continuous
  obtain ⟨hε,hU,hKU,hΦ,hΦ0,hΓ,hΓ0,hemb,hform⟩ :=
    fam_spec (A:=A) (B:=B) D S (1/(L*Real.pi)) (hIK.image continuous_fst) (hIK.image continuous_snd)
  funext t
  have hs := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
    (f:=fun q : CubicConeSpace => (t,q))
  have hg : ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,CubicConeTarget) ∞
      (fun q : CubicConeSpace =>
        ((famMap A B D S (1/(L*Real.pi)) (compactBase A B D S L K)
          (compactFibre A B D S L K) (t,q)).1,q.2)) :=
    (contDiff_fst.contMDiff.comp hs).prodMk_space
      (flatProduct_snd_smooth (E:=RealModel) (M:=BaseCurve) (V:=DiskPair))
  change semanticFullOneForm (atlas K).inclusion
    (fun x => primitiveAmbient A B D S L K (t,((atlas K).inclusion x.1,x.2))) = _
  rw [atlas_inclusion]
  exact covector_semantic hA hAB D S (1/(L*Real.pi)) L K (CubicBridge.delta_pos A B L K)
    (compactBase A B D S L K) (compactFibre A B D S L K) hΞ t hg

theorem semanticPrimitive_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K)) :
    SmoothOneFormFamily (semanticPrimitive A B D S L K) := by
  rw [primitive_semantic_eq hA hAB D S L hK hΞ]
  have hIK := hK.image hΞ.continuous
  obtain ⟨hε,hU,hKU,hΦ,hΦ0,hΓ,hΓ0,hemb,hform⟩ :=
    fam_spec (A:=A) (B:=B) D S (1/(L*Real.pi)) (hIK.image continuous_fst) (hIK.image continuous_snd)
  exact manifoldPullbackOneForm_smooth hΞ hΓ

theorem gramSum_actual_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,ℝ) ∞
      (gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K)) :=
  gramSum_smooth _ _ (atlas_geometry K).box_smooth (atlas_geometry K).box_inverse
    (primitiveAmbient_smooth hA hAB D S L K)

theorem cutoff_actual_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,ℝ) ∞ (cutoff A B D S L K) :=
  transferCut_smooth _ _ _ (atlas_geometry K).box_smooth (atlas_geometry K).box_inverse
    (primitiveAmbient_smooth hA hAB D S L K) K

end SymplecticPacking.BranchLarge3.RawTransfer
