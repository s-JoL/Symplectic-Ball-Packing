import SymplecticPacking.HighDim.Handle.NativeModelAgreement
import SymplecticPacking.HighDim.Handle.NativeAnnularComparison

/-!
# Native layer maps and geometric layer maps

The native layer formula agrees globally with the proved geometric layer map.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [NormalSpace M] [SigmaCompactSpace M] {m q k : ℕ}
namespace RawModelAgreement
variable {T : RawToricModel E M m q} {S : ToricModel M m q} (h : RawModelAgreement T S)
include h

theorem background_pullback_on (Γ : Moments m → M → E →L[ℝ] ℝ) (H : Moments m → ℝ) :
    EqOn (semanticOneForm T.presentation.inclusion (T.handleBackground Γ H))
      (ToricPackingStages.handleBackground S
        (fun p => semanticOneForm T.presentation.inclusion (Γ p)) H) S.handle.chart.target := by
  intro x hx
  have hc := RawAnnularHandle.clockPrimitive_pullback_on h.handle T.hb hx
  have hlin : semanticOneForm T.presentation.inclusion (T.handleBackground Γ H) x=
      semanticOneForm T.presentation.inclusion (Γ 0) x-
        H 0 • semanticOneForm T.presentation.inclusion (T.handle.clockPrimitive T.hb) x := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [hlin,hc]
  simp only [ToricPackingStages.handleBackground,Pi.sub_apply,Pi.smul_apply,h.hb_eq]

theorem layerDensity_eq_on
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion)
    (hambient : T.presentation.inclusion ∘ T.handle.cover=T.handle.ambientCover)
    (Γ : Moments m → M → E →L[ℝ] ℝ) (H : Moments m → ℝ) :
    EqOn (T.layerDensity (T.handleBackground Γ H))
      (ToricPackingStages.layerDensity S (ToricPackingStages.handleBackground S
        (fun p => semanticOneForm T.presentation.inclusion (Γ p)) H))
      (Ioo (-S.handle.width) S.handle.width ×ˢ univ) := by
  have hA := RawAnnularHandle.coverA_congr_on h.handle hι hambient (h.background_pullback_on Γ H)
  have hB := RawAnnularHandle.coverB_congr_on h.handle hι hambient (h.background_pullback_on Γ H)
  unfold RawToricModel.layerDensity ToricPackingStages.layerDensity
  rw [h.hδ_eq]
  exact normalizedAreaDensity_congr_on isOpen_Ioo isOpen_univ hA hB (fun _ _ => mem_univ _)

theorem layerBallMap_eq (hS : S.Spec)
    {K H : Moments m → ℝ} {γ : M → E →L[ℝ] ℝ} {β : ManifoldOneForm Plane M}
    (hden : EqOn (T.layerDensity γ) (ToricPackingStages.layerDensity S β)
      (Ioo (-S.handle.width) S.handle.width ×ˢ univ))
    (a r : Fin k → ℝ) (i : Fin k) :
    T.layerBallMap K H γ a r i=ToricPackingStages.layerBallMap S K H β a r i := by
  have hlo : T.ballLayerLo i=ToricPackingStages.ballLayerLo S i := by
    simp only [RawToricModel.ballLayerLo,ToricPackingStages.ballLayerLo,h.hb_eq]
  have hhi : T.ballLayerHi i=ToricPackingStages.ballLayerHi S i := by
    simp only [RawToricModel.ballLayerHi,ToricPackingStages.ballLayerHi,h.hb_eq]
  have hdom : T.layerMomentDomain=ToricPackingStages.layerMomentDomain S := by
    simp only [RawToricModel.layerMomentDomain,ToricPackingStages.layerMomentDomain,h.polytope_eq]
  have hbd := (layerClocks_spec (k+1) (by linarith [hS.hb_pos] : -S.hb<S.hb)).1 i.castSucc
  have hLo : ToricPackingStages.ballLayerLo S i∈Ioo (-S.handle.width) S.handle.width := by
    dsimp [ToricPackingStages.ballLayerLo]
    exact ⟨(neg_lt_neg hS.hb_lt).trans hbd.1,(hbd.2.1.trans hbd.2.2).trans hS.hb_lt⟩
  have hcoords : EqOn (T.layerCoord γ a r i) (ToricPackingStages.layerCoord S β a r i)
      (layerDomain (ToricPackingStages.ballLayerLo S i) (ToricPackingStages.ballLayerHi S i)
        (ToricPackingStages.layerMomentDomain S)) := by
    have hc := areaLayerCoordinate_congr_on (ι:=Fin m) (I:=Ioo (-S.handle.width) S.handle.width) (J:=univ)
      ordConnected_Ioo hden hLo (layerClock (k+1) (-S.hb) S.hb i.castSucc) (smoothCap (m:=m) a r i)
    intro x hx
    have hxlo : layerLo (k+1) (-S.hb) S.hb i.castSucc<x.1.1 := hx.1.1.1
    have hxhi : x.1.1<layerHi (k+1) (-S.hb) S.hb i.castSucc := hx.1.1.2
    have hwide : x.1.1∈Ioo (-S.handle.width) S.handle.width :=
      ⟨(neg_lt_neg hS.hb_lt).trans (hbd.1.trans hxlo),
        (hxhi.trans hbd.2.2).trans hS.hb_lt⟩
    simpa only [RawToricModel.layerCoord,ToricPackingStages.layerCoord,hlo,h.hb_eq] using
      hc (show x∈((Ioo (-S.handle.width) S.handle.width ×ˢ univ) ×ˢ univ) from
        ⟨⟨hwide,mem_univ _⟩,mem_univ _⟩)
  unfold RawToricModel.layerBallMap ToricPackingStages.layerBallMap
  rw [hlo,hhi,hdom,layerChartInv_congr_domain hcoords]

theorem layerMapsOf_eq (hS : S.Spec)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion)
    (hambient : T.presentation.inclusion ∘ T.handle.cover=T.handle.ambientCover)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι:=Fin m))) (K H : Moments m → ℝ)
    (Γ : Moments m → M → E →L[ℝ] ℝ) (a r : Fin k → ℝ) (i : Fin k) :
    T.layerMapsOf Φ K H Γ a r i=ToricPackingStages.layerMapsOf S Φ K H
      (fun p => semanticOneForm T.presentation.inclusion (Γ p)) a r i := by
  have hb := h.layerBallMap_eq (K:=K) (H:=H) hS (h.layerDensity_eq_on hι hambient Γ H) a r i
  have hu := RawAnnularHandle.unshear_eq h.handle Φ
  unfold RawToricModel.layerMapsOf ToricPackingStages.layerMapsOf
  rw [hb,hu,h.hb_eq,h.hδ_eq]

end RawModelAgreement
end SymplecticPacking.HighDim
