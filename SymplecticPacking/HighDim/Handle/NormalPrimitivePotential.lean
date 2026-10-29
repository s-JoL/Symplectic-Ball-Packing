import OAI.Geometry.BallPacking.Hamiltonian.AnnularDensityMass

/-!
# Explicit annular coordinate potential (towards `RawToricModel.normalPrimitive`)

The annular normalization step of the normalized primitive `Γ₁` (compare the OpenAI library `exists_normalized_primitive_on_annular_chart`)
needs, for the closed difference `α = e^*(Γ − N)` on the handle cylinder, a potential `F` with
`dF = α − per(α) · f(θ) dθ`. The library produces it existentially
(`exists_intrinsic_annular_coordinate_potential`), although its proof uses one fixed formula.
This file states that formula as an explicit definition, `annularCoordinatePotential`
(the normalized annular primitive of the cylinder coefficients of `α`, read through `e`), and
proves the library's specification for it.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Manifold Function
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

namespace ToricPackingStages

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- **The explicit annular coordinate potential**: the library's normalized annular primitive
(base circle `s = a`, angular profile `f ∘ circleTurn`) of the cylinder coefficients of `α`,
pulled back along `e : M → HandleCylinder`. -/
def annularCoordinatePotential (a : ℝ) (α : P → ManifoldOneForm CylinderModel HandleCylinder)
    (f : Circle → ℝ) (e : M → HandleCylinder) : P × M → ℝ :=
  fun q => annularCylinderScalar
    (normalizedAnnularPrimitive a (cylinderFormA α) (cylinderFormB α) (f ∘ circleTurn))
    q.1 (e q.2)

/-- The explicit potential satisfies the specification of the library's
`exists_intrinsic_annular_coordinate_potential`. -/
theorem annularCoordinatePotential_spec
    {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p ∈ V, ∀ z : HandleCylinder, z.1 ∈ I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p, extChartAt 𝓘(ℝ, CylinderModel) z z))
    (hclosed : ∀ p ∈ V, ∀ z : HandleCylinder, z.1 ∈ I → manifoldExteriorOneForm (α p) z = 0)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ, CircleModel) 𝓘(ℝ, ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1, f (circleTurn t)) = 1)
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, CylinderModel) ∞ e U)
    (hmem : ∀ x ∈ U, (e x).1 ∈ I) :
    ContMDiffOn ((𝓘(ℝ, P)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (annularCoordinatePotential a α f e)
      (V ×ˢ U) ∧
    ∀ p ∈ V, ∀ x ∈ U, ∀ v : E,
      manifoldScalarDifferential (E := E) (fun y => annularCoordinatePotential a α f e (p, y))
        x v =
        α p (e x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, CylinderModel) e x v) -
          cylinderFormPeriod a α p * f (e x).2 *
            circleAngular (e x).2 (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, CylinderModel) e x v).2 := by
  have hβ : ContDiff ℝ ∞ (f ∘ circleTurn) := (hf.comp circleTurn_smooth).contDiff
  have hpβ : Periodic (f ∘ circleTurn) 1 := fun t => congrArg f (circleTurn_period_one t)
  have hα' : ∀ p ∈ V, ∀ q : Plane, q.1 ∈ I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ, CylinderModel) (cylinderCover q) (cylinderCover q)) := by
    intro p hp q hq
    exact (hα p hp (cylinderCover q) hq).comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have hA := (cylinderForm_coefficients_smooth hα).1
  have hB := (cylinderForm_coefficients_smooth hα).2
  have hpA : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => cylinderFormA α (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic α p s).1
  have hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => cylinderFormB α (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic α p s).2
  have hrep : ∀ p ∈ V, ∀ q : Plane, q.1 ∈ I →
      euclideanPullbackOneForm (fun _ => α p) cylinderCover (0, q) =
        planarCovector (cylinderFormA α (p, q)) (cylinderFormB α (p, q)) :=
    fun p _ q _ => cylinderForm_rep α p q
  have hcurl : ∀ p ∈ V, ∀ s ∈ I, ∀ t,
      fderiv ℝ (fun z => cylinderFormA α (p, z)) (s, t) (0, 1) =
      fderiv ℝ (fun z => cylinderFormB α (p, z)) (s, t) (1, 0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation hI
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hα' p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hF, hper, _⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hfint hpA hpB hcurl
  obtain ⟨_, hFd⟩ := closed_cylinder_normalized_potential hV hI hc ha hA hB
    hβ hpβ hfint hpA hpB hα' hclosed hrep
  refine ⟨annularCylinderScalar_family_pullback_smoothOn hV hI hF hper he hmem, ?_⟩
  intro p hp x hx v
  have hd := manifoldScalarDifferential_comp_at
    (annularCylinderScalar_smoothAt hV hI hF hper hp (hmem x hx))
    (he.contMDiffAt (hU.mem_nhds hx))
  change (manifoldScalarDifferential (E := E)
    (annularCylinderScalar (normalizedAnnularPrimitive a (cylinderFormA α) (cylinderFormB α)
      (f ∘ circleTurn)) p ∘ e) x) v = _
  rw [hd]
  have h := hFd p hp (e x) (hmem x hx) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, CylinderModel) e x v)
  refine h.trans ?_
  simp only [cylinderFormPeriod, circlePeriodicDescent, Function.comp_apply,
    circleTurn_shortCircleArgument]

end ToricPackingStages

end SymplecticPacking.HighDim
