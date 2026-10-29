import SymplecticPacking.HighDim.Handle.RawAmbientBoxPrimitive

/-!
# Linearity of raw coordinate primitives

Linear operations on primitives expressed in all raw coordinates.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

theorem coefficient_add (Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ) :
    B.coefficient (Ω+Ξ) = B.coefficient Ω+B.coefficient Ξ := by
  funext z
  by_cases hz : z ∈ B.box.chart.target <;> simp [coefficient, hz]

theorem coefficient_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) :
    B.coefficient (a • Ω) = a • B.coefficient Ω := by
  funext z
  by_cases hz : z ∈ B.box.chart.target <;> simp [coefficient, hz]

theorem coefficient_sub (Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ) :
    B.coefficient (Ω-Ξ) = B.coefficient Ω-B.coefficient Ξ := by
  funext z
  by_cases hz : z ∈ B.box.chart.target <;> simp [coefficient, hz]

theorem mass_sub {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : Integrable (B.coefficient Ω)) (hΞ : Integrable (B.coefficient Ξ)) :
    B.mass (Ω-Ξ) = B.mass Ω-B.mass Ξ := by
  unfold mass
  simp only [SymplecticPacking.Explicit.planeVolume_eq_volume]
  rw [B.coefficient_sub]
  exact integral_sub hΩ hΞ

theorem mass_smul (a : ℝ) (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) :
    B.mass (a • Ω) = a * B.mass Ω := by
  unfold mass
  rw [B.coefficient_smul]
  exact integral_const_mul a _

theorem coordinatePullback_add (α β : M → E →L[ℝ] ℝ) :
    B.coordinatePullback (α+β) = B.coordinatePullback α+B.coordinatePullback β := by
  funext z
  exact ContinuousLinearMap.add_comp _ _ _

theorem coordinatePullback_smul (a : ℝ) (α : M → E →L[ℝ] ℝ) :
    B.coordinatePullback (a • α) = a • B.coordinatePullback α := by
  funext z
  exact ContinuousLinearMap.smul_comp _ _ _

theorem coordinatePullback_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {α : M → E →L[ℝ] ℝ} (hα : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ α) :
    ContDiffOn ℝ ∞ (B.coordinatePullback α) B.box.chart.target :=
  (hα.comp_contMDiffOn hB.inverse).contDiffOn.clm_comp
    (hsB.fderiv_of_isOpen B.box.chart.open_target (by simp))

end RawAmbientBox

variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

/-- A smooth ambient covector has the specified exterior derivative in every raw chart.
All smooth compatibility and exterior derivative assertions are proof data. -/
structure RawIsPrimitive (inclusion : M → E)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (α : M → E →L[ℝ] ℝ) : Prop where
  smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ α
  curvature : ∀ C : RawAmbientBox E M, C.inclusion = inclusion → C.box.Smooth →
    ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target → ∀ z ∈ C.box.chart.target,
      euclideanExteriorOneForm (C.coordinatePullback α) z = C.coefficient Ω z • planarArea

namespace RawIsPrimitive
variable {inclusion : M → E}
  {Ω Ξ : M → E →L[ℝ] E →L[ℝ] ℝ} {α β : M → E →L[ℝ] ℝ}

theorem zero (inclusion : M → E) : RawIsPrimitive inclusion 0 0 := by
  refine ⟨contMDiff_const, ?_⟩
  intro C hinc hC hsC z hz
  have he : C.coordinatePullback (0 : M → E →L[ℝ] ℝ) = 0 := by
    funext w
    exact ContinuousLinearMap.zero_comp _
  rw [he]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp [euclideanExteriorOneForm, RawAmbientBox.coefficient, hz]

theorem add (hα : RawIsPrimitive inclusion Ω α) (hβ : RawIsPrimitive inclusion Ξ β) :
    RawIsPrimitive inclusion (Ω+Ξ) (α+β) := by
  refine ⟨hα.smooth.add hβ.smooth, ?_⟩
  intro C hinc hC hsC z hz
  rw [C.coordinatePullback_add, euclideanExteriorOneForm_add
    (((C.coordinatePullback_smooth hC hsC hα.smooth).contDiffAt
      (C.box.chart.open_target.mem_nhds hz)).differentiableAt (by simp))
    (((C.coordinatePullback_smooth hC hsC hβ.smooth).contDiffAt
      (C.box.chart.open_target.mem_nhds hz)).differentiableAt (by simp)),
    hα.curvature C hinc hC hsC z hz, hβ.curvature C hinc hC hsC z hz,
    C.coefficient_add]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [Pi.add_apply, smul_apply, smul_eq_mul, add_apply]
  ring

theorem smul (a : ℝ) (hα : RawIsPrimitive inclusion Ω α) :
    RawIsPrimitive inclusion (a • Ω) (a • α) := by
  have hs : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ (a • α) :=
    (a • ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).contDiff.contMDiff.comp hα.smooth
  refine ⟨hs, ?_⟩
  intro C hinc hC hsC z hz
  rw [C.coordinatePullback_smul, euclideanExteriorOneForm_smul a
    (((C.coordinatePullback_smooth hC hsC hα.smooth).contDiffAt
      (C.box.chart.open_target.mem_nhds hz)).differentiableAt (by simp)),
    hα.curvature C hinc hC hsC z hz, C.coefficient_smul]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  ring

theorem sum {I : Type} (s : Finset I)
    (Ω : I → M → E →L[ℝ] E →L[ℝ] ℝ) (α : I → M → E →L[ℝ] ℝ)
    (h : ∀ i ∈ s, RawIsPrimitive inclusion (Ω i) (α i)) :
    RawIsPrimitive inclusion (∑ i ∈ s, Ω i) (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using RawIsPrimitive.zero inclusion
  | @insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end RawIsPrimitive
end SymplecticPacking.HighDim.ToricPackingStages
