import SymplecticPacking.BranchLarge3.OAIOpen

/-!
# Step S3b: the explicit annular handle on the genus-one base curve

The explicit version of the OpenAI theorem
`DiagonalQuadrics.Explicit.exists_positive_fixed_annularHandleData` for `m = 0`: an annular handle
(chart, width, clock, density chart) on the base curve `BaseCurve = Surface 0`, of width
`transverseCylinderWidth 0 / 2`, with clock `positiveCircleClock (1/4)` and positively oriented
density chart. The handle is the transverse cylinder of the explicit quadric chart
(OpenAI `Annuli/QuadricCylinderChart`).

The dual one-form is written down explicitly (no existence statement is used in its definition):
with `w₀ = transverseCylinderWidth 0`, `e` the transverse cylinder of width `w₀`, `β₀` the
compactly supported dual form `compactDualForm 0` (period one around the core circle),
`F` the explicit normalized annular primitive of `e^*β₀ − f dθ` (OpenAI
`normalizedAnnularPrimitive`, transported by `e⁻¹`), and `χ(s)` the explicit smooth cutoff
`T((7w₀/8 − s)·4/w₀)·T((7w₀/8 + s)·4/w₀)` (`T = Real.smoothTransition`), equal to `1` for
`|s| ≤ 5w₀/8` and to `0` for `|s| ≥ 7w₀/8`, the dual form is
`β = β₀ − d(χ(s)·F)`.
On `|s| < 5w₀/8` it equals `f(θ) dθ` in the cylinder coordinates.

Paper: supplement `handle.tex` (closed-base handle).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold

namespace HandleConstruction

local notation "w₀" => transverseCylinderWidth 0

theorem w0_pos : 0 < w₀ := transverseCylinderWidth_pos 0

/-- The transverse cylinder chart of full width `w₀`. -/
def cyl : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) HandleCylinder (Surface 0) ∞ :=
  restrictedTransverseCylinder 0 w₀

theorem cyl_source : cyl.source = Ioo (-w₀) w₀ ×ˢ univ :=
  restrictedTransverseCylinder_source 0 le_rfl

theorem cyl_mem_source {z : HandleCylinder} (hz : z.1 ∈ Ioo (-w₀) w₀) : z ∈ cyl.source := by
  rw [cyl_source]; exact ⟨hz, mem_univ _⟩

theorem cyl_symm_mem {x : Surface 0} (hx : x ∈ cyl.target) : (cyl.symm x).1 ∈ Ioo (-w₀) w₀ := by
  have hm := cyl.map_target hx
  rw [cyl_source] at hm
  exact hm.1

/-- The clock. -/
def clk : Circle → ℝ := positiveCircleClock (1 / 4)

theorem clk_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ clk :=
  positiveCircleClock_smooth (by norm_num) (by norm_num)

theorem clk_integral : (∫ t in (0:ℝ)..1, clk (circleTurn t)) = 1 :=
  positiveCircleClock_integral (by norm_num) (by norm_num)

/-- The pullback of `compactDualForm 0` to the cylinder (constant family). -/
def cylForm : ℝ → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (E := RealModel) (F := CylinderModel)
    (fun _ : ℝ => compactDualForm 0) cyl

/-- The explicit normalized annular primitive of `e^*β₀ − f dθ`, transported to the surface. -/
def potential (q : ℝ × Surface 0) : ℝ :=
  annularCylinderScalar
    (normalizedAnnularPrimitive 0 (cylinderFormA cylForm) (cylinderFormB cylForm)
      (clk ∘ circleTurn)) q.1 (cyl.symm q.2)

/-- The explicit smooth cutoff in the transverse coordinate. -/
def bump (s : ℝ) : ℝ :=
  Real.smoothTransition ((7 * w₀ / 8 - s) * (4 / w₀)) *
    Real.smoothTransition ((7 * w₀ / 8 + s) * (4 / w₀))

/-- The cutoff on the surface (zero off the cylinder). -/
def cutoff : Surface 0 → ℝ :=
  cyl.target.indicator (fun x => bump (cyl.symm x).1)

/-- The gauge function `χ · F`. -/
def gauge (x : Surface 0) : ℝ := cutoff x * potential (0, x)

/-- The explicit dual form `β₀ − d(χ F)`. -/
def dual : ManifoldOneForm RealModel (Surface 0) :=
  normalizedManifoldPrimitive (fun _ : ℝ => compactDualForm 0) (0 : ManifoldOneForm RealModel (Surface 0))
    (fun _ => 0) (fun q : ℝ × Surface 0 => gauge q.2) 0

/-- The flat clock one-form `f(θ) dθ` transported to the surface. -/
def clockForm : ManifoldOneForm RealModel (Surface 0) :=
  manifoldPullbackOneForm (E := CylinderModel) (F := RealModel)
    (fun _ => cylinderClockPrimitive (fun _ => 1) clk) cyl.symm 0

/-! ### The cutoff -/

theorem bump_smooth : ContDiff ℝ ∞ bump := by
  unfold bump
  exact (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.add contDiff_id).mul contDiff_const))

theorem bump_zero {s : ℝ} (hs : s ∉ Icc (-(7 * w₀ / 8)) (7 * w₀ / 8)) : bump s = 0 := by
  have h4 : 0 ≤ 4 / w₀ := (div_pos (by norm_num) w0_pos).le
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  unfold bump
  rcases hs with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 * w₀ / 8 + s) * (4 / w₀))
      (mul_nonpos_iff.mpr (Or.inr ⟨by linarith, h4⟩)), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 * w₀ / 8 - s) * (4 / w₀))
      (mul_nonpos_iff.mpr (Or.inr ⟨by linarith, h4⟩)), zero_mul]

theorem bump_one {s : ℝ} (hs : s ∈ Ioo (-(5 * w₀ / 8)) (5 * w₀ / 8)) : bump s = 1 := by
  have hw := w0_pos
  unfold bump
  have h1 : 1 ≤ (7 * w₀ / 8 - s) * (4 / w₀) := by
    rw [show (7 * w₀ / 8 - s) * (4 / w₀) = (7 * w₀ / 8 - s) * 4 / w₀ by ring, le_div_iff₀ hw]
    linarith [hs.2]
  have h2 : 1 ≤ (7 * w₀ / 8 + s) * (4 / w₀) := by
    rw [show (7 * w₀ / 8 + s) * (4 / w₀) = (7 * w₀ / 8 + s) * 4 / w₀ by ring, le_div_iff₀ hw]
    linarith [hs.1]
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

/-- The compact band on which the cutoff lives. -/
def band : Set (Surface 0) := cyl '' (Icc (-(7 * w₀ / 8)) (7 * w₀ / 8) ×ˢ (univ : Set Circle))

theorem band_sub_source :
    Icc (-(7 * w₀ / 8)) (7 * w₀ / 8) ×ˢ (univ : Set Circle) ⊆ cyl.source := by
  intro z hz
  have hw := w0_pos
  exact cyl_mem_source ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩

theorem band_compact : IsCompact band :=
  (isCompact_Icc.prod isCompact_univ).image_of_continuousOn
    (cyl.contMDiffOn.continuousOn.mono band_sub_source)

theorem band_sub_target : band ⊆ cyl.target :=
  image_subset_iff.mpr (fun _ hz => cyl.map_source (band_sub_source hz))

theorem cutoff_zero {x : Surface 0} (hx : x ∉ band) : cutoff x = 0 := by
  by_cases ht : x ∈ cyl.target
  · rw [cutoff, indicator_of_mem ht]
    apply bump_zero
    intro hs
    exact hx ⟨cyl.symm x, ⟨hs, mem_univ _⟩, cyl.right_inv ht⟩
  · rw [cutoff, indicator_of_notMem ht]

theorem cutoff_tsupport : tsupport cutoff ⊆ band :=
  closure_minimal (fun x hx => by by_contra hn; exact hx (cutoff_zero hn)) band_compact.isClosed

theorem cutoff_smooth : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ cutoff := by
  intro x
  by_cases ht : x ∈ cyl.target
  · have hs : ContMDiffAt 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun y => bump (cyl.symm y).1) x :=
      bump_smooth.contMDiff.contMDiffAt.comp x
        (cylinder_fst_smooth.contMDiffAt.comp x
          (cyl.symm.contMDiffOn.contMDiffAt (cyl.open_target.mem_nhds ht)))
    apply hs.congr_of_eventuallyEq
    filter_upwards [cyl.open_target.mem_nhds ht] with y hy
    rw [cutoff, indicator_of_mem hy]
  · have hb : x ∉ band := fun hb => ht (band_sub_target hb)
    apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [band_compact.isClosed.isOpen_compl.mem_nhds hb] with y hy
    exact cutoff_zero hy

/-- The open set where the cutoff is identically one. -/
def innerBand : Set (Surface 0) :=
  cyl.target ∩ cyl.symm ⁻¹' (Ioo (-(5 * w₀ / 8)) (5 * w₀ / 8) ×ˢ (univ : Set Circle))

theorem innerBand_open : IsOpen innerBand :=
  cyl.symm.contMDiffOn.continuousOn.isOpen_inter_preimage cyl.open_target
    (isOpen_Ioo.prod isOpen_univ)

theorem cutoff_one {x : Surface 0} (hx : x ∈ innerBand) : cutoff x = 1 := by
  rw [cutoff, indicator_of_mem hx.1]
  exact bump_one hx.2.1

/-! ### The potential -/

theorem baseDual_at (p : ℝ) (x : Surface 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × RealModel =>
      chartOneForm ((fun _ : ℝ => compactDualForm 0) q.1) x q.2)
      (p, extChartAt 𝓘(ℝ,RealModel) x x) :=
  (compactDualForm_smooth 0 x).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,RealModel)) x)).mem_nhds
      ⟨mem_univ _, (extChartAt 𝓘(ℝ,RealModel) x).map_source (mem_extChartAt_source x)⟩)

theorem cylForm_smoothAt (p : ℝ) (z : HandleCylinder) (hz : z.1 ∈ Ioo (-w₀) w₀) :
    ContDiffAt ℝ ∞ (fun q : ℝ × CylinderModel => chartOneForm (cylForm q.1) z q.2)
      (p, extChartAt 𝓘(ℝ,CylinderModel) z z) :=
  parameterManifoldPullbackOneForm_contDiffAt (baseDual_at p (cyl z))
    (cyl.contMDiffOn.contMDiffAt (cyl.open_source.mem_nhds (cyl_mem_source hz)))

theorem cylForm_closed (p : ℝ) (z : HandleCylinder) (hz : z.1 ∈ Ioo (-w₀) w₀) :
    manifoldExteriorOneForm (cylForm p) z = 0 := by
  change manifoldExteriorOneForm (manifoldPullbackOneForm (E := RealModel) (F := CylinderModel)
    (fun _ => compactDualForm 0) cyl 0) z = 0
  rw [manifold_pullback_exterior_at (α := compactDualForm 0) (g := cyl) (b := z)
    ((baseDual_at p (cyl z)).comp _ (contDiffAt_const.prodMk contDiffAt_id))
    (cyl.contMDiffOn.contMDiffAt (cyl.open_source.mem_nhds (cyl_mem_source hz)))]
  dsimp only [manifoldPullbackTwoForm]
  rw [compactDualForm_closed]
  rfl

theorem potential_spec :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,RealModel)) 𝓘(ℝ,ℝ) ∞ potential (univ ×ˢ cyl.target) ∧
      ∀ p : ℝ, ∀ x ∈ cyl.target, ∀ v : RealModel,
        manifoldScalarDifferential (E := RealModel) (fun y => potential (p, y)) x v =
          cylForm p (cyl.symm x) (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) cyl.symm x v) -
            cylinderFormPeriod 0 cylForm p * clk (cyl.symm x).2 *
              circleAngular (cyl.symm x).2
                (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) cyl.symm x v).2 := by
  have hw := w0_pos
  have h0 : (0:ℝ) ∈ Ioo (-w₀) w₀ := ⟨by linarith, hw⟩
  have hα : ∀ p ∈ (univ : Set ℝ), ∀ z : HandleCylinder, z.1 ∈ Ioo (-w₀) w₀ → ContDiffAt ℝ ∞
      (fun q : ℝ × CylinderModel => chartOneForm (cylForm q.1) z q.2)
      (p, extChartAt 𝓘(ℝ,CylinderModel) z z) := fun p _ z hz => cylForm_smoothAt p z hz
  have hβ : ContDiff ℝ ∞ (clk ∘ circleTurn) := (clk_smooth.comp circleTurn_smooth).contDiff
  have hpβ : Periodic (clk ∘ circleTurn) 1 := fun t => congrArg clk (circleTurn_period_one t)
  have hα' : ∀ p ∈ (univ : Set ℝ), ∀ q : Plane, q.1 ∈ Ioo (-w₀) w₀ → ContDiffAt ℝ ∞
      (chartOneForm (cylForm p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)) := by
    intro p hp q hq
    exact (hα p hp (cylinderCover q) hq).comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have hA := (cylinderForm_coefficients_smooth hα).1
  have hB := (cylinderForm_coefficients_smooth hα).2
  have hpA : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀,
      Periodic (fun t => cylinderFormA cylForm (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic cylForm p s).1
  have hpB : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀,
      Periodic (fun t => cylinderFormB cylForm (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic cylForm p s).2
  have hclosed : ∀ p ∈ (univ : Set ℝ), ∀ z : HandleCylinder, z.1 ∈ Ioo (-w₀) w₀ →
      manifoldExteriorOneForm (cylForm p) z = 0 := fun p _ z hz => cylForm_closed p z hz
  have hrep : ∀ p ∈ (univ : Set ℝ), ∀ q : Plane, q.1 ∈ Ioo (-w₀) w₀ →
      euclideanPullbackOneForm (fun _ => cylForm p) cylinderCover (0, q) =
        planarCovector (cylinderFormA cylForm (p, q)) (cylinderFormB cylForm (p, q)) :=
    fun p _ q _ => cylinderForm_rep cylForm p q
  have hcurl : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀, ∀ t,
      fderiv ℝ (fun z => cylinderFormA cylForm (p, z)) (s, t) (0, 1) =
      fderiv ℝ (fun z => cylinderFormB cylForm (p, z)) (s, t) (1, 0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation isOpen_Ioo
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hα' p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hF, hper, _⟩ := annular_normalization isOpen_univ isOpen_Ioo (convex_Ioo _ _) h0
    hA hB hβ hpβ clk_integral hpA hpB hcurl
  obtain ⟨_, hFd⟩ := closed_cylinder_normalized_potential isOpen_univ isOpen_Ioo (convex_Ioo _ _)
    h0 hA hB hβ hpβ clk_integral hpA hpB hα' hclosed hrep
  refine ⟨annularCylinderScalar_family_pullback_smoothOn isOpen_univ isOpen_Ioo hF hper
    cyl.symm.contMDiffOn (fun x hx => cyl_symm_mem hx), ?_⟩
  intro p x hx v
  have hd := manifoldScalarDifferential_comp_at
    (annularCylinderScalar_smoothAt isOpen_univ isOpen_Ioo hF hper (mem_univ p) (cyl_symm_mem hx))
    (cyl.symm.contMDiffOn.contMDiffAt (cyl.open_target.mem_nhds hx))
  change (manifoldScalarDifferential (E := RealModel)
    (annularCylinderScalar (normalizedAnnularPrimitive 0 (cylinderFormA cylForm)
      (cylinderFormB cylForm) (clk ∘ circleTurn)) p ∘ cyl.symm) x) v = _
  rw [hd]
  have h := hFd p (mem_univ p) (cyl.symm x) (cyl_symm_mem hx)
    (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) cyl.symm x v)
  simp only [circlePeriodicDescent, Function.comp_apply, circleTurn_shortCircleArgument] at h
  exact h

theorem potential_fiber_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun y => potential (0, y)) cyl.target :=
  potential_spec.1.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hx => ⟨mem_univ _, hx⟩)

theorem potential_differential {x : Surface 0} (hx : x ∈ cyl.target) :
    manifoldScalarDifferential (E := RealModel) (fun y => potential (0, y)) x =
      compactDualForm 0 x - clockForm x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [potential_spec.2 0 x hx v]
  have hd := parameterManifoldPullbackOneForm_inverse_apply cyl (fun _ : ℝ => compactDualForm 0) 0 hx v
  change cylForm 0 (cyl.symm x) (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) cyl.symm x v) = _ at hd
  rw [hd]
  have hp' : cylinderFormPeriod 0 cylForm 0 = 1 := cylinderDualForm_period 0 0
  rw [hp', one_mul]
  simp only [clockForm, sub_apply, manifoldPullbackOneForm,
    cylinderClockPrimitive, weightedCylinderAngular, one_mul, manifoldMapDifferential]
  change compactDualForm 0 x v - _ = compactDualForm 0 x v - clk (cyl.symm x).2 *
    cylinderAngular (cyl.symm x) (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) cyl.symm x v)
  erw [cylinderAngular_apply]

/-! ### The gauge and the dual form -/

theorem gauge_smooth : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ gauge :=
  manifold_local_potential_smooth cyl.open_target potential_fiber_smooth cutoff_smooth
    (cutoff_tsupport.trans band_sub_target)

theorem gauge_compact : HasCompactSupport gauge :=
  HasCompactSupport.of_support_subset_isCompact band_compact
    (subset_closure.trans ((scalar_product_tsupport_left _ cutoff).trans cutoff_tsupport))

theorem zero_form_smooth (c : Surface 0) :
    ContDiffOn ℝ ∞ (chartOneForm (0 : ManifoldOneForm RealModel (Surface 0)) c)
      (extChartAt 𝓘(ℝ,RealModel) c).target := by
  simpa only [show chartOneForm (0 : ManifoldOneForm RealModel (Surface 0)) c = (fun _ => 0) from
    funext (chartOneForm_zero c)] using (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : RealModel => (0 : RealModel →L[ℝ] ℝ)) (extChartAt 𝓘(ℝ,RealModel) c).target)

theorem dual_eq (x : Surface 0) :
    dual x = compactDualForm 0 x - manifoldScalarDifferential (E := RealModel) gauge x := by
  simp only [dual, normalizedManifoldPrimitive, Pi.sub_apply,
    smul_zero, sub_zero]

theorem dual_smooth : SmoothOneFormFamily (fun _ : ℝ => dual) := by
  intro c
  exact normalizedManifoldPrimitive_smooth (V := univ) isOpen_univ
    (Γ := fun _ : ℝ => compactDualForm 0) (fun c => compactDualForm_smooth 0 c)
    zero_form_smooth contDiffOn_const
    (G := fun q : ℝ × Surface 0 => gauge q.2) (gauge_smooth.comp contMDiff_snd).contMDiffOn c

theorem dual_closed (x : Surface 0) : manifoldExteriorOneForm dual x = 0 :=
  (manifold_closed_exact_normalization (fun c => compactDualForm_smooth 0 c |>.comp
      ((contDiff_const (c := (0:ℝ))).prodMk contDiff_id).contDiffOn (fun _ hy => ⟨mem_univ _, hy⟩))
    zero_form_smooth manifoldExteriorOneForm_zero gauge_smooth 0 x).trans
    (compactDualForm_closed 0 x)

theorem dual_compact : HasCompactSupport dual := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((compactDualForm_compact 0).union gauge_compact)
  intro x hx
  by_contra hn
  rw [mem_union, not_or] at hn
  apply hx
  have h1 : compactDualForm 0 x = 0 :=
    notMem_support.mp (fun hv => hn.1 (subset_closure hv))
  have h2 : manifoldScalarDifferential (E := RealModel) gauge x = 0 :=
    notMem_support.mp (fun hv => hn.2 (manifoldScalarDifferential_support gauge hv))
  rw [dual_eq, h1, h2, sub_zero]

theorem dual_eq_clockForm {x : Surface 0} (hx : x ∈ innerBand) : dual x = clockForm x := by
  have he : gauge =ᶠ[𝓝 x] (fun y => potential (0, y)) := by
    filter_upwards [innerBand_open.mem_nhds hx] with y hy
    rw [gauge, cutoff_one hy, one_mul]
  have hd : manifoldScalarDifferential (E := RealModel) gauge x =
      manifoldScalarDifferential (E := RealModel) (fun y => potential (0, y)) x :=
    he.mfderiv_eq
  rw [dual_eq, hd, potential_differential hx.1, sub_sub_cancel]

theorem clockForm_pullback {z : HandleCylinder} (hz : z ∈ cyl.source) (v : CylinderModel) :
    clockForm (cyl z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) cyl z v) =
      clk z.2 * circleAngular z.2 v.2 := by
  have hi := parameterManifoldPullbackOneForm_inverse_apply cyl.symm
    (fun _ : ℝ => cylinderClockPrimitive (fun _ => 1) clk) 0 hz v
  change clockForm (cyl z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) cyl z v) =
    cylinderClockPrimitive (fun _ => 1) clk z v at hi
  rw [hi]
  simp only [cylinderClockPrimitive, weightedCylinderAngular, smul_apply,
    smul_eq_mul, one_mul, cylinderAngular_apply]

end HandleConstruction

open HandleConstruction in
/-- The explicit annular handle on `Surface 0`. -/
def handle : AnnularHandleData Plane (Surface 0) where
  width := transverseCylinderWidth 0 / 2
  width_pos := half_pos w0_pos
  chart := restrictedTransverseCylinder 0 (transverseCylinderWidth 0 / 2)
  source_eq := restrictedTransverseCylinder_source 0 (by linarith [w0_pos])
  compact_target := by
    have hd : (restrictedTransverseCylinder 0 (transverseCylinderWidth 0 / 2)).target ⊆ band := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := (restrictedTransverseCylinder 0
        (transverseCylinderWidth 0 / 2)).toPartialEquiv.surjOn hx
      rw [restrictedTransverseCylinder_source 0 (by linarith [w0_pos])] at hz
      have hw := w0_pos
      exact ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩, hzx⟩
    exact band_compact.of_isClosed_subset isClosed_closure
      (closure_minimal hd band_compact.isClosed)
  clock := positiveCircleClock (1 / 4)
  clock_smooth := clk_smooth
  clock_nonneg := positiveCircleClock_nonneg (by norm_num)
  clock_support := positiveCircleClock_cut (by norm_num) (by norm_num)
  clock_integral := clk_integral
  dual := dual
  dual_smooth := dual_smooth
  dual_compact := dual_compact
  dual_closed := dual_closed
  dual_pullback := by
    intro z hz v
    rw [restrictedTransverseCylinder_source 0 (by linarith [w0_pos])] at hz
    have hw := w0_pos
    have hzs : z ∈ cyl.source := cyl_mem_source ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have hin : cyl z ∈ innerBand := by
      refine ⟨cyl.map_source hzs, ?_⟩
      show cyl.symm (cyl z) ∈ Ioo (-(5 * transverseCylinderWidth 0 / 8)) (5 * transverseCylinderWidth 0 / 8) ×ˢ (univ : Set Circle)
      have hl : cyl.symm.toPartialEquiv (cyl.toPartialEquiv z) = z := cyl.toPartialEquiv.left_inv hzs
      rw [hl]
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
    change dual (cyl z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) cyl z v) = _
    rw [dual_eq_clockForm hin]
    exact clockForm_pullback hzs v

end SymplecticPacking.BranchLarge3
