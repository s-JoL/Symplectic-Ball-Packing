import SymplecticPacking.BranchSmall.HandleWidth
import SymplecticPacking.BranchSmall.HandleDual
import OAI.Geometry.BallPacking.Models.RationalSlack

/-!
# The explicit annular handle on the affine quadric curve `Surface m`

Explicit version of the OpenAI theorem
`DiagonalQuadrics.Explicit.exists_positive_fixed_annularHandleData`, for every `m`, following the
`m = 0` construction of `BranchLarge3/HandleData.lean` with both widths made explicit:
`w₀ = explicitCylinderWidth m` (HandleWidth.lean) and the dual form `β_m = explicitDualForm m`
(HandleDual.lean, width `explicitAnnulusWidth m`).

With `e` the transverse cylinder of width `w₀`, `F` the explicit normalized annular primitive of
`e^*β_m − f dθ` (OpenAI `normalizedAnnularPrimitive`) and `χ(s)` the explicit smooth cutoff
`T((7w₀/8 − s)·4/w₀)·T((7w₀/8 + s)·4/w₀)` (`T = Real.smoothTransition`), the dual form of the
handle is `β = β_m − d(χ(s)·F)`; it equals `f(θ) dθ` on `|s| < 5w₀/8`.

The handle (chart closure and dual support) lies in `{‖z‖ ≤ 3}` for the projection `z = x.1`,
hence in the interior of every exhaustion piece `projectionDomain (parameters m) (exhaustionRadius _ ℓ)`.

Paper: supplement `handle.tex` (closed-base handle), prop:vtr-handle.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold

namespace QHandle

variable (m : ℕ)

local notation "w₀" => explicitCylinderWidth m

theorem w0_pos : 0 < w₀ := explicitCylinderWidth_pos m

/-- The transverse cylinder chart of width `w₀`. -/
def cyl : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) HandleCylinder (Surface m) ∞ :=
  restrictedTransverseCylinder m w₀

theorem cyl_source : (cyl m).source = Ioo (-w₀) w₀ ×ˢ univ :=
  restrictedTransverseCylinder_source_explicit le_rfl

theorem cyl_mem_source {z : HandleCylinder} (hz : z.1 ∈ Ioo (-w₀) w₀) : z ∈ (cyl m).source := by
  rw [cyl_source]; exact ⟨hz, mem_univ _⟩

theorem cyl_symm_mem {x : Surface m} (hx : x ∈ (cyl m).target) :
    ((cyl m).symm x).1 ∈ Ioo (-w₀) w₀ := by
  have hm := (cyl m).map_target hx
  rw [cyl_source] at hm
  exact hm.1

/-- The clock. -/
def clk : Circle → ℝ := positiveCircleClock (1 / 4)

theorem clk_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ clk :=
  positiveCircleClock_smooth (by norm_num) (by norm_num)

theorem clk_integral : (∫ t in (0:ℝ)..1, clk (circleTurn t)) = 1 :=
  positiveCircleClock_integral (by norm_num) (by norm_num)

/-- The pullback of `β_m` to the cylinder (constant family). -/
def cylForm : ℝ → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (E := RealModel) (F := CylinderModel)
    (fun _ : ℝ => explicitDualForm m) (cyl m)

/-- The explicit normalized annular primitive of `e^*β_m − f dθ`, transported to the surface. -/
def potential (q : ℝ × Surface m) : ℝ :=
  annularCylinderScalar
    (normalizedAnnularPrimitive 0 (cylinderFormA (cylForm m)) (cylinderFormB (cylForm m))
      (clk ∘ circleTurn)) q.1 ((cyl m).symm q.2)

/-- The explicit smooth cutoff in the transverse coordinate. -/
def bump (s : ℝ) : ℝ :=
  Real.smoothTransition ((7 * w₀ / 8 - s) * (4 / w₀)) *
    Real.smoothTransition ((7 * w₀ / 8 + s) * (4 / w₀))

/-- The cutoff on the surface (zero off the cylinder). -/
def cutoff : Surface m → ℝ :=
  (cyl m).target.indicator (fun x => bump m ((cyl m).symm x).1)

/-- The gauge function `χ · F`. -/
def gauge (x : Surface m) : ℝ := cutoff m x * potential m (0, x)

/-- The explicit dual form `β_m − d(χ F)`. -/
def dual : ManifoldOneForm RealModel (Surface m) :=
  normalizedManifoldPrimitive (fun _ : ℝ => explicitDualForm m)
    (0 : ManifoldOneForm RealModel (Surface m))
    (fun _ => 0) (fun q : ℝ × Surface m => gauge m q.2) 0

/-- The flat clock one-form `f(θ) dθ` transported to the surface. -/
def clockForm : ManifoldOneForm RealModel (Surface m) :=
  manifoldPullbackOneForm (E := CylinderModel) (F := RealModel)
    (fun _ => cylinderClockPrimitive (fun _ => 1) clk) (cyl m).symm 0

/-! ### The cutoff -/

theorem bump_smooth : ContDiff ℝ ∞ (bump m) := by
  unfold bump
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).mul contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.add contDiff_id).mul contDiff_const))

theorem bump_zero {s : ℝ} (hs : s ∉ Icc (-(7 * w₀ / 8)) (7 * w₀ / 8)) : bump m s = 0 := by
  have h4 : 0 ≤ 4 / w₀ := (div_pos (by norm_num) (w0_pos m)).le
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  unfold bump
  rcases hs with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 * w₀ / 8 + s) * (4 / w₀))
      (mul_nonpos_iff.mpr (Or.inr ⟨by linarith, h4⟩)), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 * w₀ / 8 - s) * (4 / w₀))
      (mul_nonpos_iff.mpr (Or.inr ⟨by linarith, h4⟩)), zero_mul]

theorem bump_one {s : ℝ} (hs : s ∈ Ioo (-(5 * w₀ / 8)) (5 * w₀ / 8)) : bump m s = 1 := by
  have hw := w0_pos m
  unfold bump
  have h1 : 1 ≤ (7 * w₀ / 8 - s) * (4 / w₀) := by
    rw [show (7 * w₀ / 8 - s) * (4 / w₀) = (7 * w₀ / 8 - s) * 4 / w₀ by ring, le_div_iff₀ hw]
    linarith [hs.2]
  have h2 : 1 ≤ (7 * w₀ / 8 + s) * (4 / w₀) := by
    rw [show (7 * w₀ / 8 + s) * (4 / w₀) = (7 * w₀ / 8 + s) * 4 / w₀ by ring, le_div_iff₀ hw]
    linarith [hs.1]
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

/-- The compact band on which the cutoff lives. -/
def band : Set (Surface m) :=
  (cyl m) '' (Icc (-(7 * w₀ / 8)) (7 * w₀ / 8) ×ˢ (univ : Set Circle))

theorem band_sub_source :
    Icc (-(7 * w₀ / 8)) (7 * w₀ / 8) ×ˢ (univ : Set Circle) ⊆ (cyl m).source := by
  intro z hz
  have hw := w0_pos m
  exact cyl_mem_source m ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩

theorem band_compact : IsCompact (band m) :=
  (isCompact_Icc.prod isCompact_univ).image_of_continuousOn
    ((cyl m).contMDiffOn.continuousOn.mono (band_sub_source m))

theorem band_sub_target : band m ⊆ (cyl m).target :=
  image_subset_iff.mpr (fun _ hz => (cyl m).map_source (band_sub_source m hz))

theorem cutoff_zero {x : Surface m} (hx : x ∉ band m) : cutoff m x = 0 := by
  by_cases ht : x ∈ (cyl m).target
  · rw [cutoff, indicator_of_mem ht]
    apply bump_zero
    intro hs
    exact hx ⟨(cyl m).symm x, ⟨hs, mem_univ _⟩, (cyl m).right_inv ht⟩
  · rw [cutoff, indicator_of_notMem ht]

theorem cutoff_tsupport : tsupport (cutoff m) ⊆ band m :=
  closure_minimal (fun x hx => by by_contra hn; exact hx (cutoff_zero m hn))
    (band_compact m).isClosed

theorem cutoff_smooth : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (cutoff m) := by
  intro x
  by_cases ht : x ∈ (cyl m).target
  · have hs : ContMDiffAt 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun y => bump m ((cyl m).symm y).1) x :=
      (bump_smooth m).contMDiff.contMDiffAt.comp x
        (cylinder_fst_smooth.contMDiffAt.comp x
          ((cyl m).symm.contMDiffOn.contMDiffAt ((cyl m).open_target.mem_nhds ht)))
    apply hs.congr_of_eventuallyEq
    filter_upwards [(cyl m).open_target.mem_nhds ht] with y hy
    rw [cutoff, indicator_of_mem hy]
  · have hb : x ∉ band m := fun hb => ht (band_sub_target m hb)
    apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(band_compact m).isClosed.isOpen_compl.mem_nhds hb] with y hy
    exact cutoff_zero m hy

/-- The open set where the cutoff is identically one. -/
def innerBand : Set (Surface m) :=
  (cyl m).target ∩ (cyl m).symm ⁻¹' (Ioo (-(5 * w₀ / 8)) (5 * w₀ / 8) ×ˢ (univ : Set Circle))

theorem innerBand_open : IsOpen (innerBand m) :=
  (cyl m).symm.contMDiffOn.continuousOn.isOpen_inter_preimage (cyl m).open_target
    (isOpen_Ioo.prod isOpen_univ)

theorem cutoff_one {x : Surface m} (hx : x ∈ innerBand m) : cutoff m x = 1 := by
  rw [cutoff, indicator_of_mem hx.1]
  exact bump_one m hx.2.1

/-! ### The potential -/

theorem baseDual_at (p : ℝ) (x : Surface m) :
    ContDiffAt ℝ ∞ (fun q : ℝ × RealModel =>
      chartOneForm ((fun _ : ℝ => explicitDualForm m) q.1) x q.2)
      (p, extChartAt 𝓘(ℝ,RealModel) x x) :=
  (explicitDualForm_smooth m x).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,RealModel)) x)).mem_nhds
      ⟨mem_univ _, (extChartAt 𝓘(ℝ,RealModel) x).map_source (mem_extChartAt_source x)⟩)

theorem cylForm_smoothAt (p : ℝ) (z : HandleCylinder) (hz : z.1 ∈ Ioo (-w₀) w₀) :
    ContDiffAt ℝ ∞ (fun q : ℝ × CylinderModel => chartOneForm (cylForm m q.1) z q.2)
      (p, extChartAt 𝓘(ℝ,CylinderModel) z z) :=
  parameterManifoldPullbackOneForm_contDiffAt (baseDual_at m p (cyl m z))
    ((cyl m).contMDiffOn.contMDiffAt ((cyl m).open_source.mem_nhds (cyl_mem_source m hz)))

theorem cylForm_closed (p : ℝ) (z : HandleCylinder) (hz : z.1 ∈ Ioo (-w₀) w₀) :
    manifoldExteriorOneForm (cylForm m p) z = 0 := by
  change manifoldExteriorOneForm (manifoldPullbackOneForm (E := RealModel) (F := CylinderModel)
    (fun _ => explicitDualForm m) (cyl m) 0) z = 0
  rw [manifold_pullback_exterior_at (α := explicitDualForm m) (g := cyl m) (b := z)
    ((baseDual_at m p (cyl m z)).comp _ (contDiffAt_const.prodMk contDiffAt_id))
    ((cyl m).contMDiffOn.contMDiffAt ((cyl m).open_source.mem_nhds (cyl_mem_source m hz)))]
  dsimp only [manifoldPullbackTwoForm]
  rw [explicitDualForm_closed]
  rfl

theorem potential_spec :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,RealModel)) 𝓘(ℝ,ℝ) ∞ (potential m)
        (univ ×ˢ (cyl m).target) ∧
      ∀ p : ℝ, ∀ x ∈ (cyl m).target, ∀ v : RealModel,
        manifoldScalarDifferential (E := RealModel) (fun y => potential m (p, y)) x v =
          cylForm m p ((cyl m).symm x)
              (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) (cyl m).symm x v) -
            cylinderFormPeriod 0 (cylForm m) p * clk ((cyl m).symm x).2 *
              circleAngular ((cyl m).symm x).2
                (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) (cyl m).symm x v).2 := by
  have hw := w0_pos m
  have h0 : (0:ℝ) ∈ Ioo (-w₀) w₀ := ⟨by linarith, hw⟩
  have hα : ∀ p ∈ (univ : Set ℝ), ∀ z : HandleCylinder, z.1 ∈ Ioo (-w₀) w₀ → ContDiffAt ℝ ∞
      (fun q : ℝ × CylinderModel => chartOneForm (cylForm m q.1) z q.2)
      (p, extChartAt 𝓘(ℝ,CylinderModel) z z) := fun p _ z hz => cylForm_smoothAt m p z hz
  have hβ : ContDiff ℝ ∞ (clk ∘ circleTurn) := (clk_smooth.comp circleTurn_smooth).contDiff
  have hpβ : Periodic (clk ∘ circleTurn) 1 := fun t => congrArg clk (circleTurn_period_one t)
  have hα' : ∀ p ∈ (univ : Set ℝ), ∀ q : Plane, q.1 ∈ Ioo (-w₀) w₀ → ContDiffAt ℝ ∞
      (chartOneForm (cylForm m p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)) := by
    intro p hp q hq
    exact (hα p hp (cylinderCover q) hq).comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have hA := (cylinderForm_coefficients_smooth hα).1
  have hB := (cylinderForm_coefficients_smooth hα).2
  have hpA : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀,
      Periodic (fun t => cylinderFormA (cylForm m) (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic (cylForm m) p s).1
  have hpB : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀,
      Periodic (fun t => cylinderFormB (cylForm m) (p, (s, t))) 1 :=
    fun p _ s _ => (cylinderForm_coefficients_periodic (cylForm m) p s).2
  have hclosed : ∀ p ∈ (univ : Set ℝ), ∀ z : HandleCylinder, z.1 ∈ Ioo (-w₀) w₀ →
      manifoldExteriorOneForm (cylForm m p) z = 0 := fun p _ z hz => cylForm_closed m p z hz
  have hrep : ∀ p ∈ (univ : Set ℝ), ∀ q : Plane, q.1 ∈ Ioo (-w₀) w₀ →
      euclideanPullbackOneForm (fun _ => cylForm m p) cylinderCover (0, q) =
        planarCovector (cylinderFormA (cylForm m) (p, q)) (cylinderFormB (cylForm m) (p, q)) :=
    fun p _ q _ => cylinderForm_rep (cylForm m) p q
  have hcurl : ∀ p ∈ (univ : Set ℝ), ∀ s ∈ Ioo (-w₀) w₀, ∀ t,
      fderiv ℝ (fun z => cylinderFormA (cylForm m) (p, z)) (s, t) (0, 1) =
      fderiv ℝ (fun z => cylinderFormB (cylForm m) (p, z)) (s, t) (1, 0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation isOpen_Ioo
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp, hz⟩))
      (hα' p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hF, hper, _⟩ := annular_normalization isOpen_univ isOpen_Ioo (convex_Ioo _ _) h0
    hA hB hβ hpβ clk_integral hpA hpB hcurl
  obtain ⟨_, hFd⟩ := closed_cylinder_normalized_potential isOpen_univ isOpen_Ioo
    (convex_Ioo _ _) h0 hA hB hβ hpβ clk_integral hpA hpB hα' hclosed hrep
  refine ⟨annularCylinderScalar_family_pullback_smoothOn isOpen_univ isOpen_Ioo hF hper
    (cyl m).symm.contMDiffOn (fun x hx => cyl_symm_mem m hx), ?_⟩
  intro p x hx v
  have hd := manifoldScalarDifferential_comp_at
    (annularCylinderScalar_smoothAt isOpen_univ isOpen_Ioo hF hper (mem_univ p)
      (cyl_symm_mem m hx))
    ((cyl m).symm.contMDiffOn.contMDiffAt ((cyl m).open_target.mem_nhds hx))
  change (manifoldScalarDifferential (E := RealModel)
    (annularCylinderScalar (normalizedAnnularPrimitive 0 (cylinderFormA (cylForm m))
      (cylinderFormB (cylForm m)) (clk ∘ circleTurn)) p ∘ (cyl m).symm) x) v = _
  rw [hd]
  have h := hFd p (mem_univ p) ((cyl m).symm x) (cyl_symm_mem m hx)
    (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) (cyl m).symm x v)
  simp only [circlePeriodicDescent, Function.comp_apply, circleTurn_shortCircleArgument] at h
  exact h

theorem potential_fiber_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun y => potential m (0, y)) (cyl m).target :=
  (potential_spec m).1.comp (contMDiffOn_const.prodMk contMDiffOn_id)
    (fun _ hx => ⟨mem_univ _, hx⟩)

theorem potential_differential {x : Surface m} (hx : x ∈ (cyl m).target) :
    manifoldScalarDifferential (E := RealModel) (fun y => potential m (0, y)) x =
      explicitDualForm m x - clockForm m x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [(potential_spec m).2 0 x hx v]
  have hd := parameterManifoldPullbackOneForm_inverse_apply (cyl m)
    (fun _ : ℝ => explicitDualForm m) 0 hx v
  change cylForm m 0 ((cyl m).symm x)
    (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) (cyl m).symm x v) = _ at hd
  rw [hd]
  have hp' : cylinderFormPeriod 0 (cylForm m) 0 = 1 := xCylinderDualForm_period m 0
  rw [hp', one_mul]
  simp only [clockForm, sub_apply, manifoldPullbackOneForm,
    cylinderClockPrimitive, weightedCylinderAngular, one_mul, manifoldMapDifferential]
  change explicitDualForm m x v - _ = explicitDualForm m x v - clk ((cyl m).symm x).2 *
    cylinderAngular ((cyl m).symm x)
      (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,CylinderModel) (cyl m).symm x v)
  erw [cylinderAngular_apply]

/-! ### The gauge and the dual form -/

theorem gauge_smooth : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (gauge m) :=
  manifold_local_potential_smooth (cyl m).open_target (potential_fiber_smooth m)
    (cutoff_smooth m) ((cutoff_tsupport m).trans (band_sub_target m))

theorem gauge_tsupport : tsupport (gauge m) ⊆ band m :=
  (scalar_product_tsupport_left _ (cutoff m)).trans (cutoff_tsupport m)

theorem gauge_compact : HasCompactSupport (gauge m) :=
  HasCompactSupport.of_support_subset_isCompact (band_compact m)
    (subset_closure.trans (gauge_tsupport m))

theorem zero_form_smooth (c : Surface m) :
    ContDiffOn ℝ ∞ (chartOneForm (0 : ManifoldOneForm RealModel (Surface m)) c)
      (extChartAt 𝓘(ℝ,RealModel) c).target := by
  simpa only [show chartOneForm (0 : ManifoldOneForm RealModel (Surface m)) c = (fun _ => 0) from
    funext (chartOneForm_zero c)] using (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : RealModel => (0 : RealModel →L[ℝ] ℝ)) (extChartAt 𝓘(ℝ,RealModel) c).target)

theorem dual_eq (x : Surface m) :
    dual m x = explicitDualForm m x - manifoldScalarDifferential (E := RealModel) (gauge m) x := by
  simp only [dual, normalizedManifoldPrimitive, Pi.sub_apply, smul_zero, sub_zero]

theorem dual_smooth : SmoothOneFormFamily (fun _ : ℝ => dual m) := by
  intro c
  exact normalizedManifoldPrimitive_smooth (V := univ) isOpen_univ
    (Γ := fun _ : ℝ => explicitDualForm m) (fun c => explicitDualForm_smooth m c)
    (zero_form_smooth m) contDiffOn_const
    (G := fun q : ℝ × Surface m => gauge m q.2) ((gauge_smooth m).comp contMDiff_snd).contMDiffOn c

theorem dual_closed (x : Surface m) : manifoldExteriorOneForm (dual m) x = 0 :=
  (manifold_closed_exact_normalization (fun c => explicitDualForm_smooth m c |>.comp
      ((contDiff_const (c := (0:ℝ))).prodMk contDiff_id).contDiffOn
        (fun _ hy => ⟨mem_univ _, hy⟩))
    (zero_form_smooth m) manifoldExteriorOneForm_zero (gauge_smooth m) 0 x).trans
    (explicitDualForm_closed m x)

theorem dual_support_sub :
    support (dual m) ⊆ tsupport (explicitDualForm m) ∪ tsupport (gauge m) := by
  intro x hx
  by_contra hn
  rw [mem_union, not_or] at hn
  apply hx
  have h1 : explicitDualForm m x = 0 :=
    notMem_support.mp (fun hv => hn.1 (subset_closure hv))
  have h2 : manifoldScalarDifferential (E := RealModel) (gauge m) x = 0 :=
    notMem_support.mp (fun hv => hn.2 (manifoldScalarDifferential_support (gauge m) hv))
  rw [dual_eq, h1, h2, sub_zero]

theorem dual_compact : HasCompactSupport (dual m) :=
  HasCompactSupport.of_support_subset_isCompact
    ((explicitDualForm_compact m).union (gauge_compact m)) (dual_support_sub m)

theorem dual_tsupport :
    tsupport (dual m) ⊆ tsupport (explicitDualForm m) ∪ tsupport (gauge m) :=
  closure_minimal (dual_support_sub m)
    ((explicitDualForm_compact m).union (gauge_compact m)).isClosed

theorem dual_eq_clockForm {x : Surface m} (hx : x ∈ innerBand m) :
    dual m x = clockForm m x := by
  have he : gauge m =ᶠ[𝓝 x] (fun y => potential m (0, y)) := by
    filter_upwards [(innerBand_open m).mem_nhds hx] with y hy
    rw [gauge, cutoff_one m hy, one_mul]
  have hd : manifoldScalarDifferential (E := RealModel) (gauge m) x =
      manifoldScalarDifferential (E := RealModel) (fun y => potential m (0, y)) x :=
    he.mfderiv_eq
  rw [dual_eq, hd, potential_differential m hx.1, sub_sub_cancel]

theorem clockForm_pullback {z : HandleCylinder} (hz : z ∈ (cyl m).source) (v : CylinderModel) :
    clockForm m (cyl m z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) (cyl m) z v) =
      clk z.2 * circleAngular z.2 v.2 := by
  have hi := parameterManifoldPullbackOneForm_inverse_apply (cyl m).symm
    (fun _ : ℝ => cylinderClockPrimitive (fun _ => 1) clk) 0 hz v
  change clockForm m (cyl m z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) (cyl m) z v) =
    cylinderClockPrimitive (fun _ => 1) clk z v at hi
  rw [hi]
  simp only [cylinderClockPrimitive, weightedCylinderAngular, smul_apply,
    smul_eq_mul, one_mul, cylinderAngular_apply]

/-! ### The handle chart -/

theorem half_le : w₀ / 2 ≤ explicitCylinderWidth m := by linarith [w0_pos m]

theorem chart_source :
    (restrictedTransverseCylinder m (w₀ / 2)).source = Ioo (-(w₀ / 2)) (w₀ / 2) ×ˢ univ :=
  restrictedTransverseCylinder_source_explicit (half_le m)

theorem chart_target_sub_band : (restrictedTransverseCylinder m (w₀ / 2)).target ⊆ band m := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := (restrictedTransverseCylinder m (w₀ / 2)).toPartialEquiv.surjOn hx
  rw [chart_source] at hz
  have hw := w0_pos m
  exact ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩, hzx⟩

theorem chart_closure_sub_band :
    closure (restrictedTransverseCylinder m (w₀ / 2)).target ⊆ band m :=
  closure_minimal (chart_target_sub_band m) (band_compact m).isClosed

end QHandle

open QHandle in
/-- **The explicit annular handle on `Surface m`.** -/
def quadricHandleData (m : ℕ) : AnnularHandleData Plane (Surface m) where
  width := explicitCylinderWidth m / 2
  width_pos := half_pos (w0_pos m)
  chart := restrictedTransverseCylinder m (explicitCylinderWidth m / 2)
  source_eq := chart_source m
  compact_target := (band_compact m).of_isClosed_subset isClosed_closure (chart_closure_sub_band m)
  clock := positiveCircleClock (1 / 4)
  clock_smooth := clk_smooth
  clock_nonneg := positiveCircleClock_nonneg (by norm_num)
  clock_support := positiveCircleClock_cut (by norm_num) (by norm_num)
  clock_integral := clk_integral
  dual := dual m
  dual_smooth := dual_smooth m
  dual_compact := dual_compact m
  dual_closed := dual_closed m
  dual_pullback := by
    intro z hz v
    rw [chart_source m] at hz
    have hw := w0_pos m
    have hzs : z ∈ (cyl m).source :=
      cyl_mem_source m ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have hin : cyl m z ∈ innerBand m := by
      refine ⟨(cyl m).map_source hzs, ?_⟩
      show (cyl m).symm (cyl m z) ∈ Ioo (-(5 * explicitCylinderWidth m / 8))
        (5 * explicitCylinderWidth m / 8) ×ˢ (univ : Set Circle)
      have hl : (cyl m).symm.toPartialEquiv ((cyl m).toPartialEquiv z) = z :=
        (cyl m).toPartialEquiv.left_inv hzs
      rw [hl]
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
    change dual m (cyl m z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) (cyl m) z v) = _
    rw [dual_eq_clockForm m hin]
    exact clockForm_pullback m hzs v

theorem quadricHandleData_clock (m : ℕ) :
    (quadricHandleData m).clock = positiveCircleClock (1 / 4) := rfl

/-- The density chart of the handle is positively oriented (as the OpenAI
`fixed_handle_densityChart_positive`, for the explicit width). -/
theorem quadricHandleData_positive (m : ℕ) :
    PositivePartialChart (quadricHandleData m).densityChart := by
  set H := quadricHandleData m
  have heq : (H.densityChart : Plane → Surface m) = transverseDiffeomorph m ∘ rectanglePolar := by
    funext y
    rw [AnnularHandleData.densityChart_apply]
    rfl
  intro c y hy hc
  have hys : cylinderCover y ∈ H.chart.source := hy.2
  have hyc : cylinderCover y ∈ (transverseCylinder m).source := hys.1
  rw [transverseCylinder_source] at hyc
  have hyd : rectanglePolar y ∈ (transverseDiffeomorph m).source := by
    rw [transverseDiffeomorph_source]
    change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM
      (cylinderComplexMap (cylinderCover y))) ∈ transverseAnnulusDomain m
    simpa only [ContinuousLinearEquiv.symm_apply_apply, mem_preimage] using hyc
  have hc' : transverseDiffeomorph m (rectanglePolar y) ∈ (extChartAt 𝓘(ℝ,Plane) c).source := by
    simpa only [heq, Function.comp_apply] using hc
  have hpos := transverseDiffeomorph_positive m c (rectanglePolar y) hyd hc'
  have hf : DifferentiableAt ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m)
      (rectanglePolar y) := by
    have hi := (transverseDiffeomorph m).contMDiffOn.contMDiffAt
      ((transverseDiffeomorph m).open_source.mem_nhds hyd)
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc')
    exact (ho.comp _ hi).contDiffAt.differentiableAt (by simp)
  rw [heq, ← Function.comp_assoc,
    fderiv_comp y hf (rectanglePolar_smooth.differentiable (by simp) y)]
  change 0 < LinearMap.det ((fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m)
    (rectanglePolar y)).toLinearMap.comp (fderiv ℝ rectanglePolar y).toLinearMap)
  rw [LinearMap.det_comp]
  exact mul_pos hpos (rectanglePolar_det_pos y)

/-! ### The handle lies in `{‖z‖ ≤ 3}` -/

theorem norm_plus_le {s : ℂ} (_hs : s ≠ 0) : ‖plus s‖ ≤ (‖s‖ + ‖s‖⁻¹) / 2 := by
  unfold plus
  rw [norm_div, show ‖(2:ℂ)‖ = 2 by norm_num, ← norm_inv]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)

theorem band_projection (m : ℕ) : QHandle.band m ⊆ projectionDomain (parameters m) 3 := by
  rintro x ⟨z, hz, rfl⟩
  have hw := QHandle.w0_pos m
  have hw2 := explicitCylinderWidth_le_one m
  have hs : |z.1| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  set c := cylinderComplexMap z with hc
  have hc0 : c ≠ 0 := cylinderComplexMap_ne_zero z
  have hval : (QHandle.cyl m z).val = transverseAnnulusPoint m c := by
    change (transverseAnnulusInverse m c).val = _
    exact transverseAnnulusInverse_val m hc0
  change ‖(QHandle.cyl m z).val.1‖ ≤ 3
  rw [hval]
  change ‖plus c‖ ≤ 3
  have hn : ‖c‖ = Real.exp z.1 := cylinderComplexMap_norm z
  have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h1 : Real.exp z.1 ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_abs_le hs)
  have h2 : (Real.exp z.1)⁻¹ ≤ Real.exp 1 := by
    rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith [neg_abs_le z.1])
  calc ‖plus c‖ ≤ (‖c‖ + ‖c‖⁻¹) / 2 := norm_plus_le hc0
    _ ≤ 3 := by rw [hn]; linarith

theorem annulus_projection (m : ℕ) :
    (annulusDiffeomorph m) '' planeClosedAnnulus (explicitAnnulusWidth m) ⊆
      projectionDomain (parameters m) 3 := by
  rintro x ⟨y, hy, rfl⟩
  have hε := explicitAnnulusWidth_pos m
  have hε2 := explicitAnnulusWidth_le m
  set s := Complex.equivRealProdCLM.symm y with hsdef
  have hy1 : 1 - explicitAnnulusWidth m ≤ ‖s‖ := hy.1
  have hy2 : ‖s‖ ≤ 1 + explicitAnnulusWidth m := hy.2
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have hval : (annulusDiffeomorph m y).val = annulusPoint m s := by
    change (annulusInverse m s).val = _
    exact annulusInverse_val m hs0
  have hloc := mem_locus.mp (annulusDiffeomorph m y).property 0
  rw [hval, annulusPoint_zero] at hloc
  have hpar : parameters m 0 = 1 := by simp [parameters]
  rw [hpar] at hloc
  change ‖(annulusDiffeomorph m y).val.1‖ ≤ 3
  rw [hval]
  set u := (annulusPoint m s).1
  have hu : u ^ 2 = 1 + plus s ^ 2 := by linear_combination -hloc
  have hpn : ‖plus s‖ ≤ 2 := by
    have hsn : 0 < ‖s‖ := by linarith
    have hi : ‖s‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hsn (by norm_num)]; linarith
    linarith [norm_plus_le hs0]
  have hun : ‖u‖ ^ 2 ≤ 5 := by
    rw [← norm_pow, hu]
    calc ‖1 + plus s ^ 2‖ ≤ ‖(1:ℂ)‖ + ‖plus s ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖plus s‖ ^ 2 := by rw [norm_one, norm_pow]
      _ ≤ 5 := by nlinarith [norm_nonneg (plus s)]
  nlinarith [norm_nonneg u]

theorem quadricHandleData_in_projection (m : ℕ) :
    closure (quadricHandleData m).chart.target ∪ tsupport (quadricHandleData m).dual ⊆
      projectionDomain (parameters m) 3 := by
  apply union_subset
  · exact (QHandle.chart_closure_sub_band m).trans (band_projection m)
  · refine (QHandle.dual_tsupport m).trans (union_subset ?_ ?_)
    · exact (explicitDualForm_support m).trans (annulus_projection m)
    · exact (QHandle.gauge_tsupport m).trans (band_projection m)

theorem three_lt_exhaustionRadius (m ℓ : ℕ) : 3 < exhaustionRadius (parameters m) ℓ := by
  have h1 : ‖parameters m 1‖ = 2 := by
    simp [parameters]; norm_num
  have hs : ‖parameters m 1‖ ≤ ∑ j, ‖parameters m j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (parameters m j)) (Finset.mem_univ 1)
  unfold exhaustionRadius
  have : (0:ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  linarith

/-- The handle lies in the interior of every exhaustion piece. -/
theorem quadricHandleData_in_exhaustion (m ℓ : ℕ) :
    closure (quadricHandleData m).chart.target ∪ tsupport (quadricHandleData m).dual ⊆
      interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)) :=
  (quadricHandleData_in_projection m).trans
    (projectionDomain_nested (parameters m) (three_lt_exhaustionRadius m ℓ))

end SymplecticPacking.BranchSmall
