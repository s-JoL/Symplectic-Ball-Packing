import SymplecticPacking.HighDim.Handle.QuadricRawBoxes

/-!
# Orientation of the explicit quadric root-chart transitions

Positive real orientation of transitions between the explicit root charts.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

def rawQuadricChart {m : ℕ} {a : Fin m → ℂ} (c : locus a) (tag : Option (Fin m))
    (hc : c.val ∈ regularCoordinate tag) : OpenPartialHomeomorph (locus a) ℂ :=
  match tag, hc with
  | none, hc => ordinaryExplicitChart c hc
  | some i, hc => branchExplicitChart c i hc

theorem rawQuadricChart_apply {m : ℕ} {a : Fin m → ℂ} (c : locus a) (tag : Option (Fin m))
    (hc : c.val ∈ regularCoordinate tag) (x : locus a) :
    rawQuadricChart c tag hc x = curveCoordinate tag x.val := by cases tag <;> rfl

theorem rawQuadricChart_inverse_smooth {m : ℕ} {a : Fin m → ℂ} (c : locus a) (tag : Option (Fin m))
    (hc : c.val ∈ regularCoordinate tag) :
    ContDiffOn ℂ ∞ (fun u => ((rawQuadricChart c tag hc).symm u : Affine m))
      (rawQuadricChart c tag hc).target := by
  cases tag with
  | none => exact ordinaryLocalLift_smooth c hc
  | some i => exact branchLocalLift_smooth c i hc

theorem rawQuadricChart_transition_smooth {m : ℕ} {a : Fin m → ℂ}
    (c d : locus a) (tag t : Option (Fin m))
    (hc : c.val ∈ regularCoordinate tag) (hd : d.val ∈ regularCoordinate t) :
    ContDiffOn ℂ ∞ ((rawQuadricChart c tag hc).symm.trans (rawQuadricChart d t hd))
      ((rawQuadricChart c tag hc).symm.trans (rawQuadricChart d t hd)).source := by
  have hh := (curveCoordinate t).contDiff.comp_contDiffOn (rawQuadricChart_inverse_smooth c tag hc)
  apply (hh.mono inter_subset_left).congr
  intro z hz
  exact rawQuadricChart_apply d t hd _

theorem rawQuadricChart_transition_positive {m : ℕ} {a : Fin m → ℂ}
    (c d : locus a) (tag t : Option (Fin m))
    (hc : c.val ∈ regularCoordinate tag) (hd : d.val ∈ regularCoordinate t)
    {y : ℝ × ℝ}
    (hy : Complex.equivRealProdCLM.symm y ∈
      ((rawQuadricChart c tag hc).symm.trans (rawQuadricChart d t hd)).source) :
    0 < (fderiv ℝ (Complex.equivRealProdCLM ∘
      ((rawQuadricChart c tag hc).symm.trans (rawQuadricChart d t hd)) ∘
      Complex.equivRealProdCLM.symm) y).det := by
  let e := (rawQuadricChart c tag hc).symm.trans (rawQuadricChart d t hd)
  have hf := (rawQuadricChart_transition_smooth c d tag t hc hd).contDiffAt
    (e.open_source.mem_nhds hy)
  have hg := (rawQuadricChart_transition_smooth d c t tag hd hc).contDiffAt
    (e.symm.open_source.mem_nhds (e.map_source hy))
  exact holomorphic_partialHomeomorph_orientation e hy
    (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))

end SymplecticPacking.HighDim.ToricPackingStages
