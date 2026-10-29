import SymplecticPacking.HighDim.Handle.RawAmbientPrimitive

/-!
# Formula primitives of zero-mass forms in a raw box

A compactly supported zero-mass raw two-form has a formula primitive in its box.
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

def formPrimitive (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) : M → E →L[ℝ] ℝ :=
  B.primitive (B.coefficient Ω)

theorem coefficient_face_zero {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} {K : Set M}
    (hKB : K ⊆ B.box.carrier) (hz : ∀ x, x ∉ K → Ω x = 0)
    (x y : ℝ) (hxy : B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2|) :
    B.coefficient Ω (x,y) = 0 := by
  apply B.coefficient_zero hz
  rintro ⟨u, hu, he⟩
  have hb := (hKB hu).2
  change B.box.chart u ∈ Metric.ball B.box.point B.box.radius at hb
  rw [he] at hb
  have hn : max |x-B.box.point.1| |y-B.box.point.2| < B.box.radius := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs] using hb
  rcases hxy with hx | hy
  · exact (not_lt_of_ge hx) ((le_max_left _ _).trans_lt hn)
  · exact (not_lt_of_ge hy) ((le_max_right _ _).trans_lt hn)

theorem formPrimitive_spec [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v, Ω x u v = -Ω x v u)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.carrier)
    (hz : ∀ x, x ∉ K → Ω x = 0) (hm : B.mass Ω = 0) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] ℝ) ∞ (B.formPrimitive Ω) ∧
      (∀ x, x ∉ B.box.compactCarrier → B.formPrimitive Ω x = 0) ∧
      ∀ C : RawAmbientBox E M, B.inclusion = C.inclusion →
        ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target →
        ∀ z ∈ C.box.chart.target,
          euclideanExteriorOneForm (C.coordinatePullback (B.formPrimitive Ω)) z =
            C.coefficient Ω z • planarArea := by
  have hKs : K ⊆ B.box.chart.source := fun x hx => (hKB hx).1
  have hf := B.coefficient_smooth hB hsB hΩ hK hKs hz
  have hface := B.coefficient_face_zero hKB hz
  refine ⟨B.primitive_smooth hB hsB hf hface hm,
    (B.primitive_spec hsB hf hface hm).1, ?_⟩
  intro C hinc hsC z hzt
  exact B.primitive_curvature C hinc hsB hsC hsk hf hface hm hKs hz hzt

end RawAmbientBox
#check_explicit RawAmbientBox.formPrimitive
end SymplecticPacking.HighDim.ToricPackingStages
