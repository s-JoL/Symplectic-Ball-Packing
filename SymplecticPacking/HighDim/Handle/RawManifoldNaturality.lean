import SymplecticPacking.HighDim.Handle.RawManifoldBridge

/-!
# Naturality of the semantic forms under pullback

Exterior derivative compatibility between raw ambient covectors and manifold tensors.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semanticOneForm_pullback (C : RawAmbientBox E M) {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : C.inclusion=ι) (hC : C.box.Smooth)
    (α : M → E →L[ℝ] ℝ) {z : Plane} (hz : z ∈ C.box.chart.target) :
    manifoldPullbackOneForm (fun _ : ℝ => semanticOneForm ι α) C.box.chart.symm 0 z =
      C.coordinatePullback α z := by
  have hc := ((hC.inverse z hz).contMDiffAt (C.box.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp z hc.hasMFDerivAt).mfderiv
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (C.box.chart.symm z)
  let J : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) C.box.chart.symm z
  have he : C.inverseAmbient=ι ∘ C.box.chart.symm := by funext y; exact congrFun hinc _
  have hframe : C.frame z=A.comp J := by
    unfold RawAmbientBox.frame
    rw [he]
    simpa only [mfderiv_eq_fderiv] using hd
  apply ContinuousLinearMap.ext
  intro v
  change α (C.box.chart.symm z) (A (J v))=α (C.box.chart.symm z) (C.frame z v)
  rw [hframe]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semanticTwoForm_pullback (C : RawAmbientBox E M) {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : C.inclusion=ι) (hC : C.box.Smooth)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) {z : Plane} (hz : z ∈ C.box.chart.target) :
    manifoldPullbackTwoForm (fun _ : ℝ => semanticTwoForm ι Ω) C.box.chart.symm 0 z =
      (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z) := by
  have hc := ((hC.inverse z hz).contMDiffAt (C.box.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp z hc.hasMFDerivAt).mfderiv
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (C.box.chart.symm z)
  let J : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) C.box.chart.symm z
  have he : C.inverseAmbient=ι ∘ C.box.chart.symm := by funext y; exact congrFun hinc _
  have hframe : C.frame z=A.comp J := by
    unfold RawAmbientBox.frame
    rw [he]
    simpa only [mfderiv_eq_fderiv] using hd
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω (C.box.chart.symm z) (A (J u)) (A (J v)) =
    Ω (C.box.chart.symm z) (C.frame z u) (C.frame z v)
  rw [hframe]
  rfl

theorem rawIsPrimitive_of_semantic {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {α : M → E →L[ℝ] ℝ} (hα : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ α)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ∀ x u v, Ω x u v = -Ω x v u)
    (hd : manifoldExteriorOneForm (semanticOneForm ι α)=semanticTwoForm ι Ω) :
    RawIsPrimitive ι Ω α := by
  refine ⟨hα,?_⟩
  intro C hinc hC hsC z hz
  have hsm := semanticOneForm_smooth hι hα
  have hca := hsm.spatial_smooth 0 (C.box.chart.symm z) (mem_extChartAt_target _)
  have hg := (hC.inverse z hz).contMDiffAt (C.box.chart.open_target.mem_nhds hz)
  have hn := manifold_pullback_exterior_at hca hg
  have he : manifoldPullbackOneForm (fun _ : ℝ => semanticOneForm ι α) C.box.chart.symm 0
      =ᶠ[𝓝 z] C.coordinatePullback α := by
    filter_upwards [C.box.chart.open_target.mem_nhds hz] with w hw
    exact semanticOneForm_pullback C hι hinc hC α hw
  have hcurv : euclideanExteriorOneForm (C.coordinatePullback α) z =
      (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z) := by
    calc
      _ = euclideanExteriorOneForm (manifoldPullbackOneForm
          (fun _ : ℝ => semanticOneForm ι α) C.box.chart.symm 0) z := by
        simp only [euclideanExteriorOneForm,he.fderiv_eq]
      _ = manifoldPullbackTwoForm (fun _ : ℝ => semanticTwoForm ι Ω) C.box.chart.symm 0 z := by
        simpa only [vector_exteriorOneForm,hd] using hn
      _ = _ := semanticTwoForm_pullback C hι hinc hC Ω hz
  rw [hcurv]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let β := (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z)
  have hβ : ∀ u v, β u v = -β v u := fun u v => hΩ _ _ _
  have hcoeff : C.coefficient Ω z=β (1,0) (0,1) := by simp only [RawAmbientBox.coefficient,if_pos hz]; rfl
  rw [hcoeff]
  change β u v=β (1,0) (0,1)*planarArea u v
  exact planar_skew_coefficient β hβ u v

end SymplecticPacking.HighDim.ToricPackingStages
