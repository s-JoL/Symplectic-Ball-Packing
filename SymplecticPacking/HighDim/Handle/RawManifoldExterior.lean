import SymplecticPacking.HighDim.Handle.RawManifoldNaturality

/-!
# Manifold exterior derivatives of raw primitives

Raw primitive identities imply the corresponding manifold exterior derivative identity.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem rawCoefficient_area (C : RawAmbientBox E M)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ∀ x u v, Ω x u v = -Ω x v u)
    {z : Plane} (hz : z ∈ C.box.chart.target) :
    C.coefficient Ω z • planarArea =
      (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z) := by
  let β := (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z)
  have hβ : ∀ u v, β u v = -β v u := fun u v => hΩ _ _ _
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hc : C.coefficient Ω z=β (1,0) (0,1) := by
    simp only [RawAmbientBox.coefficient,if_pos hz]
    rfl
  rw [hc]
  change β (1,0) (0,1)*planarArea u v=β u v
  exact (planar_skew_coefficient β hβ u v).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem RawIsPrimitive.semantic_exterior {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {α : M → E →L[ℝ] ℝ} {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hα : RawIsPrimitive ι Ω α) (hΩ : ∀ x u v, Ω x u v = -Ω x v u)
    (hcover : ∀ x : M, ∃ C : RawAmbientBox E M,
      C.inclusion=ι ∧ C.box.Smooth ∧
      ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target ∧ x ∈ C.box.chart.source) :
    manifoldExteriorOneForm (semanticOneForm ι α)=semanticTwoForm ι Ω := by
  funext x
  obtain ⟨C,hinc,hC,hsC,hx⟩ := hcover x
  let z := C.box.chart x
  have hz : z ∈ C.box.chart.target := C.box.chart.map_source hx
  have hxz : C.box.chart.symm z=x := C.box.chart.left_inv hx
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) M Plane ∞ :=
    { toPartialEquiv := C.box.chart.toPartialEquiv
      open_source := C.box.chart.open_source
      open_target := C.box.chart.open_target
      contMDiffOn_toFun := hC.forward
      contMDiffOn_invFun := hC.inverse }
  let J : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) C.box.chart.symm z
  let L : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) C.box.chart x
  have hinv : J.comp L=ContinuousLinearMap.id ℝ Plane := handle_mfderiv_symm_comp e hx
  have hsm := semanticOneForm_smooth hι hα.smooth
  have hca := hsm.spatial_smooth 0 (C.box.chart.symm z) (mem_extChartAt_target _)
  have hg := (hC.inverse z hz).contMDiffAt (C.box.chart.open_target.mem_nhds hz)
  have hn := manifold_pullback_exterior_at hca hg
  have he : manifoldPullbackOneForm (E := Plane) (F := Plane) (M := M) (N := Plane) (fun _ : ℝ => semanticOneForm ι α) C.box.chart.symm 0
      =ᶠ[𝓝 z] C.coordinatePullback α := by
    filter_upwards [C.box.chart.open_target.mem_nhds hz] with w hw
    exact semanticOneForm_pullback C hι hinc hC α hw
  have hpb : manifoldPullbackTwoForm (E := Plane) (F := Plane) (M := M) (N := Plane)
      (fun _ : ℝ => manifoldExteriorOneForm (semanticOneForm ι α)) C.box.chart.symm 0 z =
      manifoldPullbackTwoForm (E := Plane) (F := Plane) (M := M) (N := Plane) (fun _ : ℝ => semanticTwoForm ι Ω) C.box.chart.symm 0 z := by
    calc
      _ = manifoldExteriorOneForm (manifoldPullbackOneForm (E := Plane) (F := Plane) (M := M) (N := Plane)
          (fun _ : ℝ => semanticOneForm ι α) C.box.chart.symm 0) z := hn.symm
      _ = euclideanExteriorOneForm (C.coordinatePullback α) z := by
        rw [vector_exteriorOneForm]
        simp only [euclideanExteriorOneForm,he.fderiv_eq]
      _ = C.coefficient Ω z • planarArea := hα.curvature C hinc hC hsC z hz
      _ = (Ω (C.box.chart.symm z)).bilinearComp (C.frame z) (C.frame z) := rawCoefficient_area C hΩ hz
      _ = _ := (semanticTwoForm_pullback C hι hinc hC Ω hz).symm
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hval := congrArg (fun B => B (L u) (L v)) hpb
  change manifoldExteriorOneForm (semanticOneForm ι α) (C.box.chart.symm z) (J (L u)) (J (L v)) =
    semanticTwoForm ι Ω (C.box.chart.symm z) (J (L u)) (J (L v)) at hval
  have hu : J (L u)=u := congrArg (fun A => A u) hinv
  have hv : J (L v)=v := congrArg (fun A => A v) hinv
  simpa only [hxz,hu,hv] using hval

end SymplecticPacking.HighDim.ToricPackingStages
