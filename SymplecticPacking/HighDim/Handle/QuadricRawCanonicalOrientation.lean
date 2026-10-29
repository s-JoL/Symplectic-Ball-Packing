import SymplecticPacking.HighDim.Handle.QuadricRawOrientation
import OAI.Geometry.BallPacking.Surfaces.QuadricOrientation

/-!
# Canonical orientation of the explicit quadric root charts

Explicit root charts have the canonical complex orientation. Selected atlas
objects occur only in this semantic comparison proof.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def rawQuadricRealChart (c : locus a) (tag : Option (Fin m))
    (hc : c.val∈regularCoordinate tag) : OpenPartialHomeomorph (locus a) Plane :=
  (rawQuadricChart c tag hc).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

theorem rawQuadricChart_canonical_transition_positive
    (centre : locus a) (tag : Option (Fin m)) (hc : centre.val∈regularCoordinate tag)
    (b : locus a) {y : Plane}
    (hy : y ∈ (rawQuadricRealChart centre tag hc).target)
    (hb : (rawQuadricRealChart centre tag hc).symm y ∈ (extChartAt 𝓘(ℝ,Plane) b).source) :
    0 < (fderiv ℝ ((extChartAt 𝓘(ℝ,Plane) b) ∘ (rawQuadricRealChart centre tag hc).symm) y).det := by
  have hehome : (Complex.equivRealProdCLM.toHomeomorph : ℂ → Plane)=Complex.equivRealProdCLM := rfl
  have hehomeinv : (Complex.equivRealProdCLM.toHomeomorph.symm : Plane → ℂ)=Complex.equivRealProdCLM.symm := rfl
  have hbchart : chartAt Plane b=realChart a b := rfl
  let c := rawQuadricChart centre tag hc
  let d := (normalChartAt a b).sliceChart b
  let e := c.symm.trans d
  have hye : Complex.equivRealProdCLM.symm y ∈ e.source := by
    refine ⟨hy.2,?_⟩
    simpa only [mfld_simps,rawQuadricRealChart,hbchart,realChart,c,d,hehomeinv] using hb
  have hf : ContDiffOn ℂ ∞ e e.source := by
    have h := (curveCoordinate (normalChartAt a b).coordinate).contDiff.comp_contDiffOn
      (rawQuadricChart_inverse_smooth centre tag hc)
    exact h.mono inter_subset_left
  have hg : ContDiffOn ℂ ∞ e.symm e.symm.source := by
    have h := (curveCoordinate tag).contDiff.comp_contDiffOn
      ((normalChartAt a b).sliceChart_inverse_smooth b)
    apply (h.mono inter_subset_left).congr
    intro z hz
    exact rawQuadricChart_apply centre tag hc _
  have hp := holomorphic_partialHomeomorph_orientation e hye
    ((hf.contDiffAt (e.open_source.mem_nhds hye)).differentiableAt (by simp))
    ((hg.contDiffAt (e.symm.open_source.mem_nhds (e.map_source hye))).differentiableAt (by simp))
  have heq : (extChartAt 𝓘(ℝ,Plane) b) ∘ (rawQuadricRealChart centre tag hc).symm =
      Complex.equivRealProdCLM ∘ e ∘ Complex.equivRealProdCLM.symm := by
    funext z
    simp only [mfld_simps,rawQuadricRealChart,hbchart,realChart,e,d,c,hehome,hehomeinv]
  rwa [heq]

end SymplecticPacking.HighDim.ToricPackingStages
