import SymplecticPacking.HighDim.Handle.RawFullProductMoserSpec

/-!
# Coordinate regularity of full covector paths

If the semantic full one-forms of a covector path are smooth, then its full covector and
full form are smooth in every raw box chart.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

theorem fullCovector_semantic_contDiffAt {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion=ι) (hB : B.box.Smooth)
    {α : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t)))
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) => B.fullCovector (α q.1) q.2) p := by
  have hb := (hB.inverse p.2.1 hp).contMDiffAt (B.box.chart.open_target.mem_nhds hp)
  have hs := euclideanPullbackOneForm_contDiffAt (E:=Plane × V) (F:=Plane × V)
    (M:=M × V) (α:=fun t => semanticFullOneForm ι (α t)) (p:=p)
    hα (flatProductMap_smoothAt (V:=V) hb)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(continuousAt_fst.comp continuousAt_snd).preimage_mem_nhds
    (B.box.chart.open_target.mem_nhds hp)] with q hq
  exact (B.fullCovector_pullback hι hinc hB (α q.1) hq).symm

theorem fullForm_semantic_contDiffAt {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion=ι) (hB : B.box.Smooth)
    {α : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t)))
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) => B.fullForm (α q.1) q.2) p := by
  have hc := B.fullCovector_semantic_contDiffAt hι hinc hB hα hp
  have hraw : ContDiffAt ℝ ∞ (fun q : (ℝ × (Plane × V)) × (Plane × V) =>
      B.fullCovector (α q.1.1) q.2) (p,p.2) :=
    hc.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) =>
      fderiv ℝ (B.fullCovector (α q.1)) q.2) p :=
    hraw.fderiv contDiffAt_snd (by simp)
  have hflip : ContDiff ℝ ∞ (fun L : (Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜:=ℝ) (n:=∞)
      (E:=(Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ)
      (F:=(Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ)
      (ContinuousLinearMap.flipₗᵢ ℝ (Plane × V) (Plane × V) ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
