import SymplecticPacking.HighDim.Handle.RawHandlePaths
import SymplecticPacking.HighDim.Handle.RawLayerMapsSpec

/-!
# Native annular coefficients and the geometric pullback

Local agreement of native annular coefficients with the geometric pullback.
-/

noncomputable section
namespace SymplecticPacking.HighDim.RawAnnularHandle
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {A : RawAnnularHandle E M} {D : AnnularHandleData Plane M} {b : ℝ}

theorem coverCovector_pullback {ι : M → E} (h : A.Agreement ι D b)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hambient : ι ∘ A.cover=A.ambientCover) (γ : M → E →L[ℝ] ℝ)
    {y : Plane} (hy : y.1∈Ioo (-D.width) D.width) :
    A.coverCovector γ y=euclideanPullbackOneForm (fun _ => semanticOneForm ι γ)
      D.handleAnnularCover (0,y) := by
  have he : A.cover=D.handleAnnularCover := by
    funext z
    simp only [cover,h.forward_eq]
    rfl
  have hs : cylinderCover y∈D.chart.source := by
    rw [D.source_eq]
    exact ⟨hy,mem_univ _⟩
  have hc := (D.chart.contMDiffOn.contMDiffAt (D.chart.open_source.mem_nhds hs)).comp y
    cylinderCover_smooth.contMDiffAt
  have hg : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) D.handleAnnularCover y :=
    hc.mdifferentiableAt (by simp)
  have hd := mfderiv_comp y (hι.mdifferentiable (by simp) _) hg
  have ha : ι ∘ D.handleAnnularCover=A.ambientCover := by rw [←he];exact hambient
  rw [ha,mfderiv_eq_fderiv] at hd
  apply ContinuousLinearMap.ext
  intro v
  change γ (A.cover y) (fderiv ℝ A.ambientCover y v)=
    γ (D.handleAnnularCover y)
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (D.handleAnnularCover y))
        ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) D.handleAnnularCover y) v))
  rw [hd,he]
  rfl

theorem coverCovector_congr_on {ι : M → E} (h : A.Agreement ι D b)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hambient : ι ∘ A.cover=A.ambientCover)
    {γ : M → E →L[ℝ] ℝ} {β : ManifoldOneForm Plane M}
    (hγ : EqOn (semanticOneForm ι γ) β D.chart.target)
    {y : Plane} (hy : y.1∈Ioo (-D.width) D.width) :
    A.coverCovector γ y=euclideanPullbackOneForm (fun _ => β) D.handleAnnularCover (0,y) := by
  rw [coverCovector_pullback h hι hambient γ hy]
  have hs : cylinderCover y∈D.chart.source := by rw [D.source_eq];exact ⟨hy,mem_univ _⟩
  have hx : D.handleAnnularCover y∈D.chart.target := D.chart.map_source hs
  exact congrArg (fun L : Plane →L[ℝ] ℝ =>
    L.comp (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) D.handleAnnularCover y)) (hγ hx)

theorem coverA_congr_on {ι : M → E} (h : A.Agreement ι D b)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hambient : ι ∘ A.cover=A.ambientCover)
    {γ : M → E →L[ℝ] ℝ} {β : ManifoldOneForm Plane M}
    (hγ : EqOn (semanticOneForm ι γ) β D.chart.target) :
    EqOn (A.coverA γ) (D.annularCoverA β) (Ioo (-D.width) D.width ×ˢ univ) := by
  intro y hy
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (1,0)) (coverCovector_congr_on h hι hambient hγ hy.1)

theorem coverB_congr_on {ι : M → E} (h : A.Agreement ι D b)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hambient : ι ∘ A.cover=A.ambientCover)
    {γ : M → E →L[ℝ] ℝ} {β : ManifoldOneForm Plane M}
    (hγ : EqOn (semanticOneForm ι γ) β D.chart.target) :
    EqOn (A.coverB γ) (D.annularCoverB β) (Ioo (-D.width) D.width ×ˢ univ) := by
  intro y hy
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (0,1)) (coverCovector_congr_on h hι hambient hγ hy.1)

theorem clockPrimitive_pullback_on {ι : M → E} (h : A.Agreement ι D b) (c : ℝ) :
    EqOn (semanticOneForm ι (A.clockPrimitive c)) (D.clockPrimitive c) D.chart.target := by
  intro x hx
  have hx' : x∈A.target := h.target_eq.symm ▸ hx
  rw [D.clockPrimitive_eq c hx]
  apply ContinuousLinearMap.ext
  intro v
  have hd := congrArg (fun f : ManifoldOneForm Plane M => f x v) h.dual_eq
  simp only [semanticOneForm,clockPrimitive,if_pos hx',h.inverse_eq,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at hd ⊢
  rw [hd]
end SymplecticPacking.HighDim.RawAnnularHandle
