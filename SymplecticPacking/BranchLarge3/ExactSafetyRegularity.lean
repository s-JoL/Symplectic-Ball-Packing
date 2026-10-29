import SymplecticPacking.BranchLarge3.ExactSafetyFlow

/-!
# Time regularity of scalar guards

Time-derivative regularity of scalar guards on a product manifold.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.ExactSafety
open Set Function Manifold
open scoped ContDiff Manifold Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem time_derivative_smoothAt {F : ℝ × M → ℝ} {p : ℝ × M}
    (hF : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F p) :
    ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × M => deriv (fun s => F (s,q.2)) q.1) p := by
  let f : (ℝ × M) → ℝ → ℝ := fun q s => F (s,q.2)
  have hmap : ContMDiffAt (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,ℝ))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞
      (fun q : (ℝ × M) × ℝ => (q.2,q.1.2)) (p,p.1) :=
    contMDiffAt_snd.prodMk contMDiffAt_fst.snd
  have hf : ContMDiffAt (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (Function.uncurry f) (p,p.1) := hF.comp (p,p.1) hmap
  have hg : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (Prod.fst : ℝ × M → ℝ) p := contMDiffAt_fst
  have hd := hf.mfderiv f Prod.fst hg (by simp : (∞:WithTop ℕ∞)+1≤∞)
  simp only [mfderiv_eq_fderiv] at hd
  rw [inTangentCoordinates_model_space] at hd
  have hh := hd.clm_apply (contMDiffAt_const (c:=(1:ℝ)))
  simpa only [mfderiv_eq_fderiv,deriv,f] using hh

theorem time_derivative_continuousOn {F : ℝ × M → ℝ} {K : Set M}
    (hF : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (Ioo (-2:ℝ) 2 ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × M => deriv (fun s => F (s,q.2)) q.1) (Icc (-1) 1 ×ˢ K) := by
  intro p hp
  have hpO : p∈Ioo (-2:ℝ) 2 ×ˢ (univ:Set M) :=
    ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,mem_univ _⟩
  exact (time_derivative_smoothAt ((hF p hpO).contMDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpO))).continuousAt.continuousWithinAt

end SymplecticPacking.BranchLarge3.ExactSafety
