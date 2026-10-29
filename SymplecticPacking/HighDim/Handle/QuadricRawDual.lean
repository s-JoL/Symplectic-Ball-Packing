import SymplecticPacking.BranchSmall.HandleExplicit
import SymplecticPacking.BranchSmall.QuadricRawForms
import SymplecticPacking.HighDim.Handle.RawAmbientLinearity
import SymplecticPacking.HighDim.Handle.RawManifoldNaturality

/-!
# Native ambient covectors for the quadric handle

The annular coordinate is the fixed projection `w₀+w₁`; sheet membership is a
finite list of strict real inequalities. The data never read a manifold one-form
or a selected manifold chart.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.QuadricRawDual
open Set Function Filter Manifold ContinuousLinearMap
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (m : ℕ)

/-- The raw annular coordinate in real components. -/
def annularProjection : Affine (m + 2) →L[ℝ] Plane :=
  Complex.equivRealProdCLM.toContinuousLinearMap.comp ((annulusCoordinate m).restrictScalars ℝ)

/-- The native sheet is specified directly by the fixed-root sign inequalities. -/
def annularSheet (z : Affine (m + 2)) : Prop :=
  annulusCoordinate m z ∈ annulusDomain m ∧ 0 < z.1.re ∧
    ∀ j : Fin (m + 2), 1 < j.val → 0 < (z.2 j).im

/-- The displayed annular gradient, as an ambient covector. -/
def annularGradient (ε : ℝ) (z : Affine (m + 2)) : Affine (m + 2) →L[ℝ] ℝ :=
  (fderiv ℝ (planeRadialStep ε) (annularProjection m z)).comp (annularProjection m)

/-- The first raw dual form, supported on the native annular sheet. -/
def annularDual (ε : ℝ) (z : Affine (m + 2)) : Affine (m + 2) →L[ℝ] ℝ := by
  classical
  exact if annularSheet m z then annularGradient m ε z else 0

@[simp] theorem annularProjection_symm (x : Surface m) :
    annularProjection m x.val = (annulusDiffeomorph m).symm x := rfl

@[simp] theorem annularSheet_iff (x : Surface m) :
    annularSheet m x.val ↔ x ∈ (annulusDiffeomorph m).target := by
  rw [annulusDiffeomorph_target]
  rfl

theorem annularGradient_contDiff (ε : ℝ) : ContDiff ℝ ∞ (annularGradient m ε) :=
  (((planeRadialStep_smooth ε).fderiv_right (m := ∞) (by simp)).comp
    (annularProjection m).contDiff).clm_comp contDiff_const

theorem annularProjection_mfderiv (x : Surface m) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (annulusDiffeomorph m).symm x =
      (annularProjection m).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) := by
  have hi := (real_inclusion_contMDiff (parameters m)).mdifferentiable (by simp) x
  have hc := mfderiv_comp x (annularProjection m).hasFDerivAt.differentiableAt.mdifferentiableAt hi
  change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (annulusDiffeomorph m).symm x = _ at hc
  simpa only [mfderiv_eq_fderiv, (annularProjection m).fderiv] using hc

/-- The pushforward is identified only in this proposition, after the raw data are defined. -/
theorem annularDual_pullback (ε : ℝ) (x : Surface m) :
    handlePushforwardOneForm (annulusDiffeomorph m)
        (manifoldScalarDifferential (planeRadialStep ε)) x =
      (annularDual m ε x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) := by
  by_cases hx : annularSheet m x.val
  · have ht := (annularSheet_iff m x).mp hx
    rw [handlePushforwardOneForm, extendManifoldOneForm_inside ht]
    unfold manifoldPullbackOneForm manifoldMapDifferential manifoldScalarDifferential
    change (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (planeRadialStep ε) ((annulusDiffeomorph m).symm x)).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (annulusDiffeomorph m).symm x) = _
    rw [mfderiv_eq_fderiv, annularProjection_mfderiv]
    rw [annularDual, if_pos hx]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  · have ht := mt (annularSheet_iff m x).mpr hx
    rw [handlePushforwardOneForm, extendManifoldOneForm_outside ht]
    rw [annularDual, if_neg hx, ContinuousLinearMap.zero_comp]

theorem annularDual_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hsrc : planeClosedAnnulus ε ⊆ (annulusDiffeomorph m).source) (x : Surface m)
    (hx : x ∉ (annulusDiffeomorph m) '' planeClosedAnnulus ε) :
    annularDual m ε x.val = 0 := by
  by_cases hsheet : annularSheet m x.val
  · have ht := (annularSheet_iff m x).mp hsheet
    have hcoord : annularProjection m x.val ∉ planeClosedAnnulus ε := by
      intro hmem
      have he : (annulusDiffeomorph m) (annularProjection m x.val) = x := by
        change (annulusDiffeomorph m) ((annulusDiffeomorph m).symm x) = x
        exact (annulusDiffeomorph m).right_inv ht
      exact hx ⟨_, hmem, he⟩
    have hz := planeRadialDifferential_zero hε hε1 (annularProjection m x.val) hcoord
    have hdf : fderiv ℝ (planeRadialStep ε) (annularProjection m x.val) = 0 := by
      simpa only [manifoldScalarDifferential, mfderiv_eq_fderiv] using hz
    simp only [annularDual, if_pos hsheet, annularGradient, hdf, ContinuousLinearMap.zero_comp]
  · exact if_neg hsheet

theorem annularDual_contMDiff {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hsrc : planeClosedAnnulus ε ⊆ (annulusDiffeomorph m).source) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => annularDual m ε x.val) := by
  let K := (annulusDiffeomorph m) '' planeClosedAnnulus ε
  have hK : IsCompact K := (planeClosedAnnulus_compact ε).image_of_continuousOn
    ((annulusDiffeomorph m).contMDiffOn.continuousOn.mono hsrc)
  have hKt : K ⊆ (annulusDiffeomorph m).target :=
    image_subset_iff.mpr (fun z hz => (annulusDiffeomorph m).map_source (hsrc hz))
  have hraw := (annularGradient_contDiff m ε).contMDiff.comp (real_inclusion_contMDiff (parameters m))
  intro x
  by_cases hx : x ∈ (annulusDiffeomorph m).target
  · apply (hraw x).congr_of_eventuallyEq
    filter_upwards [(annulusDiffeomorph m).open_target.mem_nhds hx] with y hy
    exact if_pos ((annularSheet_iff m y).mpr hy)
  · have hxK : x ∉ K := fun h => hx (hKt h)
    apply (contMDiffAt_const (c := (0 : Affine (m + 2) →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact annularDual_zero m hε hε1 hsrc y hy

theorem explicitDualForm_eq_raw (x : Surface m) :
    BranchSmall.explicitDualForm m x =
      (annularDual m (BranchSmall.explicitAnnulusWidth m) x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) :=
  annularDual_pullback m (BranchSmall.explicitAnnulusWidth m) x

/-! ### The transverse cover and its two-integral primitive -/

/-- The ambient transverse cylinder, written directly with the fixed square roots. -/
def transverseCover (q : Plane) : Affine (m + 2) :=
  transverseAnnulusPoint m (cylinderComplexMap (cylinderCover q))

/-- The pulled-back native covector. No manifold chart enters this definition. -/
def coverCovector (ε : ℝ) (q : Plane) : Plane →L[ℝ] ℝ :=
  (annularDual m ε (transverseCover m q)).comp (fderiv ℝ (transverseCover m) q)

def coverA (ε : ℝ) (q : Plane) : ℝ := coverCovector m ε q (1, 0)
def coverB (ε : ℝ) (q : Plane) : ℝ := coverCovector m ε q (0, 1)

/-- The radial segment followed by the angular segment; the clock has period one. -/
def segmentPotential (ε : ℝ) (q : Plane) : ℝ :=
  (∫ s in (0:ℝ)..q.1, coverA m ε (s, 0)) +
    ∫ t in (0:ℝ)..q.2, coverB m ε (q.1, t) - BranchSmall.QHandle.clk (circleTurn t)

theorem transverseCover_eq (q : Plane) :
    transverseCover m q = (BranchSmall.QHandle.cyl m (cylinderCover q)).val := by
  change transverseAnnulusPoint m (cylinderComplexMap (cylinderCover q)) =
    (transverseAnnulusInverse m (cylinderComplexMap (cylinderCover q))).val
  exact (transverseAnnulusInverse_val m (cylinderComplexMap_ne_zero _)).symm

theorem coverCovector_eq (q : Plane)
    (hq : q.1 ∈ Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)) :
    coverCovector m (BranchSmall.explicitAnnulusWidth m) q =
      parameterEuclideanPullbackOneForm (BranchSmall.QHandle.cylForm m) cylinderCover (0, q) := by
  let e := BranchSmall.QHandle.cyl m
  let g : Plane → Surface m := e ∘ cylinderCover
  have he : ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) ∞ e (cylinderCover q) :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (BranchSmall.QHandle.cyl_mem_source m hq))
  have hg : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ g q :=
    he.comp q cylinderCover_smooth.contMDiffAt
  have hι := (real_inclusion_contMDiff (parameters m)).contMDiffAt (x := g q)
  have hcomp := mfderiv_comp q (hι.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  have hcomp2 := mfderiv_comp q (he.mdifferentiableAt (by simp))
    (cylinderCover_smooth.mdifferentiableAt (by simp))
  have hraw : (Subtype.val : Surface m → Affine (m + 2)) ∘ g = transverseCover m := by
    funext z
    exact (transverseCover_eq m z).symm
  rw [hraw, mfderiv_eq_fderiv] at hcomp
  unfold coverCovector
  rw [hcomp, hcomp2, transverseCover_eq]
  change _ = ((BranchSmall.explicitDualForm m (g q)).comp
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) e (cylinderCover q))).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)
  rw [explicitDualForm_eq_raw]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem coverA_eq (q : Plane)
    (hq : q.1 ∈ Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)) :
    coverA m (BranchSmall.explicitAnnulusWidth m) q =
      cylinderFormA (BranchSmall.QHandle.cylForm m) (0, q) := by
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (1, 0)) (coverCovector_eq m q hq)

theorem coverB_eq (q : Plane)
    (hq : q.1 ∈ Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)) :
    coverB m (BranchSmall.explicitAnnulusWidth m) q =
      cylinderFormB (BranchSmall.QHandle.cylForm m) (0, q) := by
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (0, 1)) (coverCovector_eq m q hq)

theorem segmentPotential_eq (q : Plane)
    (hq : q.1 ∈ Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)) :
    segmentPotential m (BranchSmall.explicitAnnulusWidth m) q =
      normalizedAnnularPrimitive 0 (cylinderFormA (BranchSmall.QHandle.cylForm m))
        (cylinderFormB (BranchSmall.QHandle.cylForm m))
        (BranchSmall.QHandle.clk ∘ circleTurn) (0, q) := by
  have hw := BranchSmall.explicitCylinderWidth_pos m
  have hperiod : annularMean 0 (cylinderFormB (BranchSmall.QHandle.cylForm m)) 0 = 1 :=
    BranchSmall.xCylinderDualForm_period m 0
  unfold segmentPotential normalizedAnnularPrimitive annularPrimitive stripPrimitive
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro r hr
    have hlow : -(BranchSmall.explicitCylinderWidth m) < min 0 q.1 :=
      lt_min (by linarith) hq.1
    have hhigh : max 0 q.1 < BranchSmall.explicitCylinderWidth m := max_lt (by linarith) hq.2
    exact coverA_eq m (r, 0) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · apply intervalIntegral.integral_congr
    intro t ht
    simp only [annularNormalized, hperiod, one_mul, Function.comp_apply]
    rw [coverB_eq m (q.1, t) hq]

/-- The descended scalar uses the canonical argument, whose cut disappears by periodicity. -/
def cylinderPotential (ε : ℝ) (z : HandleCylinder) : ℝ :=
  segmentPotential m ε (z.1, shortCircleArgument z.2)

theorem cylinderPotential_eq (z : HandleCylinder)
    (hz : z.1 ∈ Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)) :
    cylinderPotential m (BranchSmall.explicitAnnulusWidth m) z =
      annularCylinderScalar
        (normalizedAnnularPrimitive 0 (cylinderFormA (BranchSmall.QHandle.cylForm m))
          (cylinderFormB (BranchSmall.QHandle.cylForm m))
          (BranchSmall.QHandle.clk ∘ circleTurn)) 0 z :=
  segmentPotential_eq m _ hz

/-- The transverse projection, independently of the annular projection above. -/
def transverseProjection : Affine (m + 2) →L[ℝ] Plane :=
  Complex.equivRealProdCLM.toContinuousLinearMap.comp ((transverseCoordinate m).restrictScalars ℝ)

/-- The native transverse sheet and the finite cylinder band. -/
def transverseSheet (z : Affine (m + 2)) : Prop :=
  transverseCoordinate m z ∈ transverseAnnulusDomain m ∧
    (∀ j : Fin (m + 2), j ≠ 0 → 0 < (z.2 j).im) ∧
    Real.log ‖transverseCoordinate m z‖ ∈
      Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m)

/-- A scalar on the explicit transverse coordinate plane. -/
def coordinateGauge (ε : ℝ) (z : Plane) : ℝ :=
  let c := cylinderComplexInverse (Complex.equivRealProdCLM.symm z)
  BranchSmall.QHandle.bump m c.1 * cylinderPotential m ε c

/-- The ambient correction covector, extended by zero across the native sheet boundary. -/
def gaugeCovector (ε : ℝ) (z : Affine (m + 2)) : Affine (m + 2) →L[ℝ] ℝ := by
  classical
  exact if transverseSheet m z then
    (fderiv ℝ (coordinateGauge m ε) (transverseProjection m z)).comp (transverseProjection m)
  else 0

/-- The native raw representative of the corrected handle dual. -/
def correctedDual (ε : ℝ) (z : Affine (m + 2)) : Affine (m + 2) →L[ℝ] ℝ :=
  annularDual m ε z - gaugeCovector m ε z

@[simp] theorem transverseProjection_symm (x : Surface m) :
    cylinderComplexInverse (Complex.equivRealProdCLM.symm (transverseProjection m x.val)) =
      (BranchSmall.QHandle.cyl m).symm x := by
  change cylinderComplexInverse (transverseCoordinate m x.val) = (transverseCylinder m).symm x
  exact (transverseCylinder_symm_apply m x).symm

theorem transverseCylinder_target (x : Surface m) :
    x ∈ (transverseCylinder m).target ↔
      transverseCoordinate m x.val ∈ transverseAnnulusDomain m ∧
        ∀ j : Fin (m + 2), j ≠ 0 → 0 < (x.val.2 j).im := by
  change (x ∈ (transverseDiffeomorph m).target ∧
    (transverseDiffeomorph m).symm x ∈
      (cylinderComplexDiffeomorph.trans
        Complex.equivRealProdCLM.toDiffeomorph.toPartialDiffeomorph).target) ↔ _
  rw [transverseDiffeomorph_target]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    change (transverseDiffeomorph m).symm x ∈ (univ : Set Plane) ∧
      Complex.equivRealProdCLM.symm ((transverseDiffeomorph m).symm x) ≠ 0
    refine ⟨mem_univ _, ?_⟩
    change transverseCoordinate m x.val ≠ 0
    exact h.1.1

theorem transverseSheet_iff (x : Surface m) :
    transverseSheet m x.val ↔ x ∈ (BranchSmall.QHandle.cyl m).target := by
  change _ ↔ x ∈ (transverseCylinder m).target ∩
    (transverseCylinder m).symm ⁻¹'
      (Ioo (-(BranchSmall.explicitCylinderWidth m)) (BranchSmall.explicitCylinderWidth m) ×ˢ univ)
  rw [mem_inter_iff, transverseCylinder_target]
  simp only [transverseSheet, mem_preimage, mem_prod, mem_univ, and_true,
    transverseCylinder_symm_apply, cylinderComplexInverse]
  tauto

theorem coordinateGauge_eq (x : Surface m) (hx : x ∈ (BranchSmall.QHandle.cyl m).target) :
    coordinateGauge m (BranchSmall.explicitAnnulusWidth m) (transverseProjection m x.val) =
      BranchSmall.QHandle.gauge m x := by
  unfold coordinateGauge
  rw [transverseProjection_symm]
  dsimp only
  rw [cylinderPotential_eq m _ (BranchSmall.QHandle.cyl_symm_mem m hx)]
  unfold BranchSmall.QHandle.gauge BranchSmall.QHandle.cutoff BranchSmall.QHandle.potential
  rw [indicator_of_mem hx]

theorem coordinateGauge_contDiffAt (x : Surface m)
    (hx : x ∈ (BranchSmall.QHandle.cyl m).target) :
    ContDiffAt ℝ ∞ (coordinateGauge m (BranchSmall.explicitAnnulusWidth m))
      (transverseProjection m x.val) := by
  let d := transverseDiffeomorph m
  let U := d.source ∩ d ⁻¹' (BranchSmall.QHandle.cyl m).target
  have hU : IsOpen U := d.contMDiffOn.continuousOn.isOpen_inter_preimage d.open_source
    (BranchSmall.QHandle.cyl m).open_target
  have hxt : x ∈ d.target := by
    change x ∈ (transverseDiffeomorph m).target
    rw [transverseDiffeomorph_target]
    exact (transverseCylinder_target m x).mp hx.1
  have hz : transverseProjection m x.val ∈ d.source := d.map_target hxt
  have he : d (transverseProjection m x.val) = x := d.right_inv hxt
  have hzU : transverseProjection m x.val ∈ U := by
    refine ⟨hz, ?_⟩
    change d (transverseProjection m x.val) ∈ (BranchSmall.QHandle.cyl m).target
    rw [he]
    exact hx
  have hs := ((BranchSmall.QHandle.gauge_smooth m).contMDiffAt.comp _
    (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hz))).contDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with z hz'
  have hproj : transverseProjection m (d z).val = z := d.left_inv hz'.1
  calc
    _ = coordinateGauge m (BranchSmall.explicitAnnulusWidth m) (transverseProjection m (d z).val) :=
      congrArg _ hproj.symm
    _ = _ := coordinateGauge_eq m (d z) hz'.2

theorem gaugeCovector_pullback_inside (x : Surface m)
    (hx : x ∈ (BranchSmall.QHandle.cyl m).target) :
    manifoldScalarDifferential (E := Plane) (BranchSmall.QHandle.gauge m) x =
      (gaugeCovector m (BranchSmall.explicitAnnulusWidth m) x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) := by
  have hf := coordinateGauge_contDiffAt m x hx
  have hι := (real_inclusion_contMDiff (parameters m)).contMDiffAt (x := x)
  have hP := (transverseProjection m).contDiff.contMDiff.contMDiffAt.comp x hι
  have hD := mfderiv_comp x (hf.contMDiffAt.mdifferentiableAt (by simp))
    (hP.mdifferentiableAt (by simp))
  have hD2 := mfderiv_comp x (transverseProjection m).hasFDerivAt.differentiableAt.mdifferentiableAt
    (hι.mdifferentiableAt (by simp))
  have hlocal : BranchSmall.QHandle.gauge m =ᶠ[𝓝 x]
      coordinateGauge m (BranchSmall.explicitAnnulusWidth m) ∘
        ((transverseProjection m) ∘ (Subtype.val : Surface m → Affine (m + 2))) := by
    filter_upwards [(BranchSmall.QHandle.cyl m).open_target.mem_nhds hx] with y hy
    exact (coordinateGauge_eq m y hy).symm
  have hderiv : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (BranchSmall.QHandle.gauge m) x =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ)
        (coordinateGauge m (BranchSmall.explicitAnnulusWidth m) ∘
          ((transverseProjection m) ∘ (Subtype.val : Surface m → Affine (m + 2)))) x :=
    hlocal.mfderiv_eq
  unfold manifoldScalarDifferential
  rw [hderiv, hD, hD2]
  rw [gaugeCovector, if_pos ((transverseSheet_iff m x).mpr hx)]
  simp only [mfderiv_eq_fderiv, (transverseProjection m).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem gaugeCovector_zero (ε : ℝ) (x : Surface m)
    (hx : x ∉ BranchSmall.QHandle.band m) : gaugeCovector m ε x.val = 0 := by
  by_cases hsheet : transverseSheet m x.val
  · have ht := (transverseSheet_iff m x).mp hsheet
    let z := transverseProjection m x.val
    let r : Plane → ℝ := fun u => (cylinderComplexInverse (Complex.equivRealProdCLM.symm u)).1
    have hrx : r z = ((BranchSmall.QHandle.cyl m).symm x).1 :=
      congrArg Prod.fst (transverseProjection_symm m x)
    have hnot : r z ∉ Icc (-(7 * BranchSmall.explicitCylinderWidth m / 8))
        (7 * BranchSmall.explicitCylinderWidth m / 8) := by
      intro h
      apply hx
      refine ⟨(BranchSmall.QHandle.cyl m).symm x, ⟨?_, mem_univ _⟩,
        (BranchSmall.QHandle.cyl m).right_inv ht⟩
      rwa [← hrx]
    have hnonzero : Complex.equivRealProdCLM.symm z ≠ 0 :=
      transverseCoordinate_ne_zero m x.property
    have hr : ContinuousAt r z := continuous_fst.continuousAt.comp
      ((cylinderComplexInverse_smoothAt hnonzero).continuousAt.comp
        Complex.equivRealProdCLM.symm.continuous.continuousAt)
    have hlocal : coordinateGauge m ε =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [hr (isClosed_Icc.isOpen_compl.mem_nhds hnot)] with u hu
      unfold coordinateGauge
      dsimp only
      rw [BranchSmall.QHandle.bump_zero m hu, zero_mul]
    have hd : fderiv ℝ (coordinateGauge m ε) z = 0 := by
      rw [hlocal.fderiv_eq, fderiv_const_apply]
    dsimp only [z] at hd
    simp only [gaugeCovector, if_pos hsheet, hd, ContinuousLinearMap.zero_comp]
  · exact if_neg hsheet

theorem gaugeCovector_pullback (x : Surface m) :
    manifoldScalarDifferential (E := Plane) (BranchSmall.QHandle.gauge m) x =
      (gaugeCovector m (BranchSmall.explicitAnnulusWidth m) x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) := by
  by_cases hx : x ∈ (BranchSmall.QHandle.cyl m).target
  · exact gaugeCovector_pullback_inside m x hx
  · have hband : x ∉ BranchSmall.QHandle.band m := fun h => hx (BranchSmall.QHandle.band_sub_target m h)
    have he : BranchSmall.QHandle.gauge m =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [(BranchSmall.QHandle.band_compact m).isClosed.isOpen_compl.mem_nhds hband]
        with y hy
      exact image_eq_zero_of_notMem_tsupport
        (fun h => hy (BranchSmall.QHandle.gauge_tsupport m h))
    have hd : manifoldScalarDifferential (E := Plane) (BranchSmall.QHandle.gauge m) x = 0 := by
      have hD : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (BranchSmall.QHandle.gauge m) x =
          mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (fun _ : Surface m => (0:ℝ)) x := he.mfderiv_eq
      rw [manifoldScalarDifferential, hD, mfderiv_const]
    rw [hd, gaugeCovector_zero m _ x hband, ContinuousLinearMap.zero_comp]

theorem correctedDual_pullback (x : Surface m) :
    BranchSmall.QHandle.dual m x =
      (correctedDual m (BranchSmall.explicitAnnulusWidth m) x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2)) (Subtype.val : Surface m → Affine (m + 2)) x) := by
  rw [BranchSmall.QHandle.dual_eq, explicitDualForm_eq_raw, gaugeCovector_pullback]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem gaugeCovector_contMDiff :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => gaugeCovector m (BranchSmall.explicitAnnulusWidth m) x.val) := by
  intro x
  by_cases hx : x ∈ (BranchSmall.QHandle.cyl m).target
  · have hP := (transverseProjection m).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m))
    have hgrad : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2) →L[ℝ] ℝ) ∞
        (fun y : Surface m => (fderiv ℝ (coordinateGauge m (BranchSmall.explicitAnnulusWidth m))
          (transverseProjection m y.val)).comp (transverseProjection m)) x :=
      (((coordinateGauge_contDiffAt m x hx).fderiv_right (m := ∞) (by simp)).contMDiffAt.comp
        x hP.contMDiffAt).clm_comp (contMDiffAt_const (c := transverseProjection m))
    apply hgrad.congr_of_eventuallyEq
    filter_upwards [(BranchSmall.QHandle.cyl m).open_target.mem_nhds hx] with y hy
    exact if_pos ((transverseSheet_iff m y).mpr hy)
  · have hband : x ∉ BranchSmall.QHandle.band m := fun h => hx (BranchSmall.QHandle.band_sub_target m h)
    apply (contMDiffAt_const (c := (0 : Affine (m + 2) →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [(BranchSmall.QHandle.band_compact m).isClosed.isOpen_compl.mem_nhds hband]
      with y hy
    exact gaugeCovector_zero m _ y hy

theorem correctedDual_contMDiff :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => correctedDual m (BranchSmall.explicitAnnulusWidth m) x.val) :=
  (annularDual_contMDiff m (BranchSmall.explicitAnnulusWidth_pos m)
    (BranchSmall.explicitAnnulusWidth_lt_one m) (BranchSmall.explicitAnnulusWidth_subset m)).sub
      (gaugeCovector_contMDiff m)

/-- The native dual used by the quadric provider. -/
def actualDual (z : Affine (m + 2)) : Affine (m + 2) →L[ℝ] ℝ :=
  correctedDual m (BranchSmall.explicitAnnulusWidth m) z

theorem actualDual_contMDiff :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m + 2) →L[ℝ] ℝ) ∞
      (fun x : Surface m => actualDual m x.val) := correctedDual_contMDiff m

#check_explicit actualDual

#check_explicit transverseCover
#check_explicit coverCovector
#check_explicit segmentPotential
#check_explicit correctedDual

#check_explicit annularProjection
#check_explicit annularSheet
#check_explicit annularDual

end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawDual
