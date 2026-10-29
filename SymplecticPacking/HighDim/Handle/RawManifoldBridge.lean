import SymplecticPacking.HighDim.Handle.RawAmbientLinearity
import OAI.Geometry.BallPacking.Forms.ManifoldFormTransport

/-!
# Semantic manifold forms of raw ambient forms

Semantic comparison with the manifold tensor representation.
The raw algorithms do not call these coordinate-representation functions.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

def semanticOneForm (ι : M → E) (α : M → E →L[ℝ] ℝ) : ManifoldOneForm Plane M :=
  fun x => (α x).comp (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι x)

def semanticTwoForm (ι : M → E) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : ManifoldTwoForm Plane M :=
  fun x => (Ω x).bilinearComp (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι x)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem chartOneForm_semantic {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (α : M → E →L[ℝ] ℝ) {c : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target) :
    chartOneForm (semanticOneForm ι α) c y =
      (α ((extChartAt 𝓘(ℝ,Plane) c).symm y)).comp
        (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y) := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c).mem_nhds hy)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp y hc.hasMFDerivAt).mfderiv
  apply ContinuousLinearMap.ext
  intro u
  simp only [chartOneForm,semanticOneForm,ContinuousLinearMap.comp_apply]
  rw [chartDifferential_inverse hy]
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι
    ((extChartAt 𝓘(ℝ,Plane) c).symm y)
  let J : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
    (extChartAt 𝓘(ℝ,Plane) c).symm y
  have hd' : fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y = A.comp J := by
    simpa only [mfderiv_eq_fderiv] using hd
  change α ((extChartAt 𝓘(ℝ,Plane) c).symm y) (A (J u)) =
    α ((extChartAt 𝓘(ℝ,Plane) c).symm y) (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y u)
  rw [hd']
  rfl

theorem semanticOneForm_smooth {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {α : M → E →L[ℝ] ℝ} (hα : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ α) :
    SmoothOneFormFamily (fun _ : ℝ => semanticOneForm ι α) := by
  intro c
  have hg := (hι.comp_contMDiffOn (contMDiffOn_extChartAt_symm
    (I := 𝓘(ℝ,Plane)) (n := ∞) c)).contDiffOn
  have ha := (hα.comp_contMDiffOn (contMDiffOn_extChartAt_symm
    (I := 𝓘(ℝ,Plane)) (n := ∞) c)).contDiffOn
  have hraw := ha.clm_comp (hg.fderiv_of_isOpen (isOpen_extChartAt_target c) (by simp))
  have hs := hraw.comp (contDiffOn_snd : ContDiffOn ℝ ∞
    (Prod.snd : ℝ × Plane → Plane) (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    (fun q hq => hq.2)
  apply hs.congr
  intro q hq
  exact chartOneForm_semantic hι α hq.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem chartTwoForm_semantic {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) {c : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target) :
    chartTwoForm (semanticTwoForm ι Ω) c y =
      (Ω ((extChartAt 𝓘(ℝ,Plane) c).symm y)).bilinearComp
        (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y)
        (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y) := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c).mem_nhds hy)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp y hc.hasMFDerivAt).mfderiv
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [chartTwoForm,semanticTwoForm,ContinuousLinearMap.bilinearComp_apply]
  simp only [chartDifferential_inverse hy]
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι
    ((extChartAt 𝓘(ℝ,Plane) c).symm y)
  let J : Plane →L[ℝ] Plane := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
    (extChartAt 𝓘(ℝ,Plane) c).symm y
  have hd' : fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y = A.comp J := by
    simpa only [mfderiv_eq_fderiv] using hd
  change Ω ((extChartAt 𝓘(ℝ,Plane) c).symm y) (A (J u)) (A (J v)) =
    Ω ((extChartAt 𝓘(ℝ,Plane) c).symm y)
      (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y u)
      (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y v)
  rw [hd']
  rfl

theorem semanticTwoForm_smooth {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω) :
    SmoothTwoForm (semanticTwoForm ι Ω) := by
  intro c
  have hg := (hι.comp_contMDiffOn (contMDiffOn_extChartAt_symm
    (I := 𝓘(ℝ,Plane)) (n := ∞) c)).contDiffOn
  have hω := (hΩ.comp_contMDiffOn (contMDiffOn_extChartAt_symm
    (I := 𝓘(ℝ,Plane)) (n := ∞) c)).contDiffOn
  have hF := hg.fderiv_of_isOpen (isOpen_extChartAt_target c) (m := ∞) (by simp)
  have hpre : ContDiffOn ℝ ∞ (fun y =>
      (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) y).precomp ℝ)
      (extChartAt 𝓘(ℝ,Plane) c).target := hF.contMDiffOn.clm_precomp.contDiffOn
  have hraw := hpre.clm_comp (hω.clm_comp hF)
  apply hraw.congr
  intro y hy
  rw [chartTwoForm_semantic hι Ω hy]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

end SymplecticPacking.HighDim.ToricPackingStages
