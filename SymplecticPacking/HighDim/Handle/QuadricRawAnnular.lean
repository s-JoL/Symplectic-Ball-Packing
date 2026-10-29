import SymplecticPacking.HighDim.Handle.QuadricRawDensity
import SymplecticPacking.HighDim.Handle.AnnularNormalizeFormula
import SymplecticPacking.HighDim.Handle.RawManifoldFamily

/-!
# Native annular normalization of a raw primitive

Native two-integral annular normalization of a raw ambient primitive.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
open Set Function Filter Manifold MeasureTheory
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (m : ℕ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def coverPoint (q : Plane) : Surface m :=
  transverseAnnulusInverse m (cylinderComplexMap (cylinderCover q))

def coverCovector (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (q : Plane) : Plane →L[ℝ] ℝ :=
  (δ p (coverPoint m q)).comp (fderiv ℝ (QuadricRawDual.transverseCover m) q)

def coverA (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (q : P × Plane) : ℝ :=
  coverCovector m δ q.1 q.2 (1,0)

def coverB (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (q : P × Plane) : ℝ :=
  coverCovector m δ q.1 q.2 (0,1)

def period (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) : P → ℝ :=
  annularMean 0 (coverB m δ)

def potential (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (z : HandleCylinder) : ℝ :=
  annularCylinderScalar
    (normalizedAnnularPrimitive 0 (coverA m δ) (coverB m δ) (BranchSmall.QHandle.clk ∘ circleTurn)) p z

/-- Fixed midpoint widths inside the width 1/8. -/
def cutWidth (b : ℝ) : ℝ := (b+1/8)/2

def coordinateGauge (b : ℝ) (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (z : Plane) : ℝ :=
  let c := cylinderComplexInverse (Complex.equivRealProdCLM.symm z)
  intervalPlateau (cutWidth b) (cutWidth (cutWidth b)) c.1 * potential m δ p c

def gaugeCovector (b : ℝ) (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (z : Affine (m+2)) : Affine (m+2) →L[ℝ] ℝ := by
  classical
  exact if QuadricRawDensity.nativeSheet m z then
    (fderiv ℝ (coordinateGauge m b δ p) (QuadricRawDual.transverseProjection m z)).comp
      (QuadricRawDual.transverseProjection m)
  else 0

def normalize (b : ℝ) (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (x : Surface m) : Affine (m+2) →L[ℝ] ℝ :=
  Γ p x-period m (Γ-N) p • QuadricRawDual.actualDual m x.val-
    gaugeCovector m b (Γ-N) p x.val

theorem coverCovector_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (q : Plane)
    (hq : q.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) :
    coverCovector m δ p q=parameterEuclideanPullbackOneForm (E := CylinderModel) (F := Plane)
      (parameterManifoldPullbackOneForm (E := Plane) (F := CylinderModel) (fun p => semanticOneForm Subtype.val (δ p))
        (BranchSmall.quadricHandleData m).chart) cylinderCover (p,q) := by
  let e := (BranchSmall.quadricHandleData m).chart
  let g : Plane → Surface m := e ∘ cylinderCover
  have hsrc : cylinderCover q∈e.source := by
    rw [(BranchSmall.quadricHandleData m).source_eq]
    exact ⟨hq,mem_univ _⟩
  have he := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hsrc)
  have hg := he.comp q cylinderCover_smooth.contMDiffAt
  have hi := (real_inclusion_contMDiff (parameters m)).contMDiffAt (x := g q)
  have hc := mfderiv_comp q (hi.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  have hc2 := mfderiv_comp q (he.mdifferentiableAt (by simp))
    (cylinderCover_smooth.mdifferentiableAt (by simp))
  have heq : (Subtype.val : Surface m → Affine (m+2)) ∘ g=QuadricRawDual.transverseCover m := by
    funext z
    exact (QuadricRawDual.transverseCover_eq m z).symm
  rw [heq,mfderiv_eq_fderiv] at hc
  unfold coverCovector
  rw [hc,hc2]
  apply ContinuousLinearMap.ext
  intro v
  rfl

def semanticCylinder (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) :
    P → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (E := Plane) (F := CylinderModel)
    (fun p => semanticOneForm Subtype.val (δ p)) (BranchSmall.quadricHandleData m).chart

theorem coverA_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (q : Plane)
    (hq : q.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) :
    coverA m δ (p,q)=cylinderFormA (semanticCylinder m δ) (p,q) :=
  congrArg (fun A : Plane →L[ℝ] ℝ => A (1,0)) (coverCovector_eq m δ p q hq)

theorem coverB_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (q : Plane)
    (hq : q.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) :
    coverB m δ (p,q)=cylinderFormB (semanticCylinder m δ) (p,q) :=
  congrArg (fun A : Plane →L[ℝ] ℝ => A (0,1)) (coverCovector_eq m δ p q hq)

theorem period_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) :
    period m δ=cylinderFormPeriod 0 (semanticCylinder m δ) := by
  funext p
  unfold period cylinderFormPeriod annularMean
  apply intervalIntegral.integral_congr
  intro t ht
  apply coverB_eq m δ p (0,t)
  exact ⟨neg_neg_of_pos (BranchSmall.quadricHandleData m).width_pos,(BranchSmall.quadricHandleData m).width_pos⟩

theorem segmentPotential_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (q : Plane)
    (hq : q.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) :
    normalizedAnnularPrimitive 0 (coverA m δ) (coverB m δ) (BranchSmall.QHandle.clk ∘ circleTurn) (p,q)=
      normalizedAnnularPrimitive 0 (cylinderFormA (semanticCylinder m δ))
        (cylinderFormB (semanticCylinder m δ)) (BranchSmall.QHandle.clk ∘ circleTurn) (p,q) := by
  unfold normalizedAnnularPrimitive annularPrimitive stripPrimitive annularNormalized
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    apply coverA_eq m δ p (t,0)
    have h0 : (0:ℝ)∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width :=
      ⟨neg_neg_of_pos (BranchSmall.quadricHandleData m).width_pos,(BranchSmall.quadricHandleData m).width_pos⟩
    have hconv : Convex ℝ (Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) := convex_Ioo _ _
    exact hconv.segment_subset h0 hq (by simpa only [segment_eq_uIcc] using ht)
  · apply intervalIntegral.integral_congr
    intro t ht
    change coverB m δ (p,(q.1,t))-period m δ p*BranchSmall.QHandle.clk (circleTurn t) =
      cylinderFormB (semanticCylinder m δ) (p,(q.1,t))-
        cylinderFormPeriod 0 (semanticCylinder m δ) p*BranchSmall.QHandle.clk (circleTurn t)
    rw [coverB_eq m δ p (q.1,t) hq]
    rw [period_eq]

theorem potential_eq (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (z : HandleCylinder)
    (hz : z.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width) :
    potential m δ p z=annularCylinderScalar
      (normalizedAnnularPrimitive 0 (cylinderFormA (semanticCylinder m δ))
        (cylinderFormB (semanticCylinder m δ)) (BranchSmall.QHandle.clk ∘ circleTurn)) p z := by
  unfold potential annularCylinderScalar annularScalarDescent circleFamilyDescent circlePeriodicDescent
  exact segmentPotential_eq m δ p (z.1,shortCircleArgument z.2) hz

theorem cutWidth_eq (b : ℝ) : cutWidth b=annularCutWidth (BranchSmall.quadricHandleData m) b := by
  change (b+1/8)/2=(b+BranchSmall.explicitCylinderWidth m/2)/2
  norm_num [BranchSmall.explicitCylinderWidth]

theorem semanticCylinder_difference (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ) :
    semanticCylinder m (Γ-N)=annularDifference (BranchSmall.quadricHandleData m)
      (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p)) := by
  funext p x
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem coordinateGauge_eq (b : ℝ) (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ)
    (p : P) (x : Surface m) (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    coordinateGauge m b (Γ-N) p (QuadricRawDual.transverseProjection m x.val)=
      annularCutoff (BranchSmall.quadricHandleData m) (annularCutWidth (BranchSmall.quadricHandleData m) b) x *
        annularPotential (BranchSmall.quadricHandleData m)
          (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p)) (p,x) := by
  have hinv : cylinderComplexInverse
      (Complex.equivRealProdCLM.symm (QuadricRawDual.transverseProjection m x.val))=
      (BranchSmall.quadricHandleData m).chart.symm x := QuadricRawDual.transverseProjection_symm m x
  have hs := (BranchSmall.quadricHandleData m).chart.map_target hx
  rw [(BranchSmall.quadricHandleData m).source_eq] at hs
  let z : HandleCylinder := (BranchSmall.quadricHandleData m).chart.symm.toPartialEquiv x
  have hz : z.1∈Ioo (-(BranchSmall.quadricHandleData m).width) (BranchSmall.quadricHandleData m).width := hs.1
  have hp := potential_eq m (Γ-N) p z hz
  unfold coordinateGauge
  rw [hinv]
  change intervalPlateau (cutWidth b) (cutWidth (cutWidth b)) z.1 * potential m (Γ-N) p z=_
  rw [hp]
  simp only [cutWidth_eq m]
  rw [annularCutoff,if_pos hx,semanticCylinder_difference]
  rfl

#check_explicit normalize
end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
