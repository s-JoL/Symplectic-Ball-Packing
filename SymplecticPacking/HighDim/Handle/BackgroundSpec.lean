import SymplecticPacking.HighDim.Handle.LayerMapsDef

/-!
# Curvature of the handle background

The explicitly read background inherits the constant curvature on the handle.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] {m q : ℕ}

theorem handleBackground_spec (T : ToricModel M m q)
    {Γ : (Fin m → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    (H : (Fin m → ℝ) → ℝ) {s : ℝ}
    (hdΓ : ∀ x ∈ T.handle.chart.target,
      manifoldExteriorOneForm (Γ 0) x = s • T.Λ x + H 0 • T.handle.density T.hb x) :
    (∀ x ∈ T.handle.chart.target, ContDiffAt ℝ ∞
      (chartOneForm (handleBackground T Γ H) x) (extChartAt 𝓘(ℝ, Plane) x x)) ∧
    (∀ x ∈ T.handle.chart.target,
      manifoldExteriorOneForm (handleBackground T Γ H) x = s • T.Λ x) := by
  have h0 (x : M) : ContDiffAt ℝ ∞ (chartOneForm (Γ 0) x)
      (extChartAt 𝓘(ℝ, Plane) x x) :=
    hΓ.spatial_smooth 0 x ((extChartAt 𝓘(ℝ, Plane) x).map_source (mem_extChartAt_source x))
  have hC (x : M) (hx : x ∈ T.handle.chart.target) :
      ContDiffAt ℝ ∞ (chartOneForm (H 0 • T.handle.clockPrimitive T.hb) x)
        (extChartAt 𝓘(ℝ, Plane) x x) := by
    rw [show chartOneForm (H 0 • T.handle.clockPrimitive T.hb) x =
      (fun y => H 0 • chartOneForm (T.handle.clockPrimitive T.hb) x y) from
      funext (chartOneForm_smul (H 0) (T.handle.clockPrimitive T.hb) x)]
    exact (contDiffAt_const (c := H 0)).smul (T.handle.clockPrimitive_smooth T.hb hx)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hh := (h0 x).sub (hC x hx)
    change ContDiffAt ℝ ∞ (chartOneForm (Γ 0-H 0 • T.handle.clockPrimitive T.hb) x) _
    rw [show chartOneForm (Γ 0-H 0 • T.handle.clockPrimitive T.hb) x =
      (fun y => chartOneForm (Γ 0) x y-chartOneForm (H 0 • T.handle.clockPrimitive T.hb) x y) from
      funext (chartOneForm_sub (Γ 0) (H 0 • T.handle.clockPrimitive T.hb) x)]
    exact hh
  · intro x hx
    change manifoldExteriorOneForm (Γ 0 - H 0 • T.handle.clockPrimitive T.hb) x = _
    rw [manifoldExteriorOneForm_sub_at (h0 x) (hC x hx),
      manifoldExteriorOneForm_smul_at (H 0) (T.handle.clockPrimitive_smooth T.hb hx),
      T.handle.clockPrimitive_exterior T.hb hx, hdΓ x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change s * T.Λ x u v + H 0 * T.handle.density T.hb x u v -
      H 0 * T.handle.density T.hb x u v = s * T.Λ x u v
    ring

end SymplecticPacking.HighDim.ToricPackingStages
