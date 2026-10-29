import SymplecticPacking.HighDim.Handle.RawManifoldBridge

/-!
# Joint smoothness of semantic one-form families

Joint smoothness of the semantic representation, used only in proofs.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E P M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semanticOneForm_family_smooth {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {α : P → M → E →L[ℝ] ℝ}
    (hα : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => α q.1 q.2)) :
    SmoothOneFormFamily (fun p => semanticOneForm ι (α p)) := by
  intro c
  let V := (univ : Set P) ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target
  have hinv := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c
  have hmap : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane))
      ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) ∞
      (fun q : P × Plane => (q.1,(extChartAt 𝓘(ℝ,Plane) c).symm q.2)) V :=
    contMDiffOn_fst.prodMk (hinv.comp contMDiffOn_snd (fun q hq => hq.2))
  have haMD := hα.comp_contMDiffOn hmap
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at haMD
  have ha := haMD.contDiffOn
  have hg := (hι.comp_contMDiffOn hinv).contDiffOn
  have hJ := hg.fderiv_of_isOpen (isOpen_extChartAt_target c) (m := ∞) (by simp)
  have hJprod := hJ.comp (contDiffOn_snd : ContDiffOn ℝ ∞
    (Prod.snd : P × Plane → Plane) V) (fun q hq => hq.2)
  apply (ha.clm_comp hJprod).congr
  intro q hq
  exact chartOneForm_semantic hι (α q.1) hq.2

end SymplecticPacking.HighDim.ToricPackingStages
