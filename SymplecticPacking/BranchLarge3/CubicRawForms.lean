import SymplecticPacking.BranchLarge3.PrimitiveExtension

/-!
# Ambient representatives of the physical primitive

Ambient representatives of the six-dimensional model's physical primitive.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawCubic

open Set Function Manifold ContinuousLinearMap
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The displayed polynomial coefficient map, before restriction to the curve. -/
def weightedMap (D m : ℕ) (z : Affine 2) : PlanePhase (Option (Fin 3)) :=
  affinePhase 3 (weightedProjection D m (projection z))

theorem weightedMap_contDiff (D m : ℕ) : ContDiff ℝ ∞ (weightedMap D m) :=
  (affinePhase 3).contDiff.comp
    (((weightedProjection_contDiff D m).restrict_scalars ℝ).comp
      (projection_contDiff.restrict_scalars ℝ))

/-- Its Fubini--Study connection form in fixed ambient coordinates. -/
def weightedPrimitive (D m : ℕ) (c : ℝ) (z : Affine 2) : Affine 2 →L[ℝ] ℝ :=
  (affineFSPrimitive c (weightedMap D m z)).comp (fderiv ℝ (weightedMap D m) z)

theorem weightedPrimitive_contDiff (D m : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (weightedPrimitive D m c) :=
  ((affineFSPrimitive_smooth c).comp (weightedMap_contDiff D m)).clm_comp
    ((weightedMap_contDiff D m).fderiv_right (by simp))

def coefficient (D m : ℕ) (z : Affine 2) : ℝ := 1+phaseSq (weightedMap D m z)

theorem coefficient_contDiff (D m : ℕ) : ContDiff ℝ ∞ (coefficient D m) :=
  contDiff_const.add (phaseSq_smooth.comp (weightedMap_contDiff D m))

theorem coefficient_ge_one (D m : ℕ) (z : Affine 2) : 1 ≤ coefficient D m z := by
  unfold coefficient
  linarith [phaseSq_nonneg (weightedMap D m z)]

def coefficientMap (A B D S : ℕ) (z : Affine 2) : TrapezoidWeight A B → ℝ :=
  fun i => coefficient (cubicDegree D i) (cubicMarkedOrder S i) z

theorem coefficientMap_contDiff (A B D S : ℕ) :
    ContDiff ℝ ∞ (coefficientMap A B D S) :=
  contDiff_pi.mpr fun i => coefficient_contDiff _ _

/-- The continued-weight extension, expressed wholly in ambient coordinates. -/
def extendedPrimitive (A B D S : ℕ) (c β m δ : ℝ) (p : Radial.Plane) (z : Affine 2) :
    Affine 2 →L[ℝ] ℝ :=
  ∑ i : TrapezoidWeight A B,
    PrimExt.extSel A B β m δ (coefficientMap A B D S z,p) i •
      weightedPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c z

theorem extendedPrimitive_contDiff {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (c β : ℝ) {m : ℝ} (hm : 0 < m) (hmA : m ≤ A) :
    ContDiff ℝ ∞ (fun x : Radial.Plane × Affine 2 =>
      extendedPrimitive A B D S c β m (PrimExt.width A B β m) x.1 x.2) := by
  apply ContDiff.sum
  intro i hi
  have hweight : ContDiff ℝ ∞ (fun x : Radial.Plane × Affine 2 =>
      PrimExt.extSel A B β m (PrimExt.width A B β m) (coefficientMap A B D S x.2,x.1) i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have ha : ContDiff ℝ ∞ (fun x : Radial.Plane × Affine 2 => coefficientMap A B D S x.2) :=
      (coefficientMap_contDiff A B D S).comp contDiff_snd
    have harg : ContDiff ℝ ∞ (fun x : Radial.Plane × Affine 2 =>
        (coefficientMap A B D S x.2,x.1)) := ha.prodMk contDiff_fst
    have hsel := PrimExt.extSel_contDiffAt (β := β) (m := m) hA hAB hm hmA
      (z := (coefficientMap A B D S x.2,x.1))
      (fun j => by
        change 1/2 ≤ coefficient (cubicDegree D j) (cubicMarkedOrder S j) x.2
        have := coefficient_ge_one (cubicDegree D j) (cubicMarkedOrder S j) x.2
        linarith)
    exact ((contDiff_apply ℝ ℝ i).contDiffAt.comp _ hsel).comp x harg.contDiffAt
  have hbase : ContDiff ℝ ∞ (fun x : Radial.Plane × Affine 2 =>
      weightedPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c x.2) :=
    (weightedPrimitive_contDiff _ _ c).comp contDiff_snd
  exact hweight.smul hbase

def physicalExtension (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (p : Moments 2) (z : Affine 2) : Affine 2 →L[ℝ] ℝ :=
  extendedPrimitive A B D S c (PrimExt.betaC A B D S ℓ) (PrimExt.margin A B L P)
    (PrimExt.width A B (PrimExt.betaC A B D S ℓ) (PrimExt.margin A B L P))
    (physicalParameter L p) z

theorem physicalExtension_contDiff {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (hm : 0 < PrimExt.margin A B L P) (hmA : PrimExt.margin A B L P ≤ A) :
    ContDiff ℝ ∞ (fun x : Moments 2 × Affine 2 =>
      physicalExtension A B D S c L P ℓ x.1 x.2) := by
  let β := PrimExt.betaC A B D S ℓ
  let m := PrimExt.margin A B L P
  have h : ContDiff ℝ ∞ (fun y : Radial.Plane × Affine 2 =>
      extendedPrimitive A B D S c β m (PrimExt.width A B β m) y.1 y.2) :=
    extendedPrimitive_contDiff hA hAB D S c β hm hmA
  have harg : ContDiff ℝ ∞ (fun x : Moments 2 × Affine 2 =>
      (physicalParameter L x.1,x.2)) :=
    ((physicalParameter_smooth L).comp contDiff_fst).prodMk contDiff_snd
  apply contDiff_iff_contDiffAt.mpr
  intro x
  change ContDiffAt ℝ ∞ (fun z : Moments 2 × Affine 2 =>
    extendedPrimitive A B D S c β m (PrimExt.width A B β m) (physicalParameter L z.1) z.2) x
  exact ContDiffAt.comp
    (g := fun y : Radial.Plane × Affine 2 =>
      extendedPrimitive A B D S c β m (PrimExt.width A B β m) y.1 y.2)
    (f := fun z : Moments 2 × Affine 2 => (physicalParameter L z.1,z.2))
    x h.contDiffAt harg.contDiffAt

/- The following equalities use manifold derivatives only in propositions. -/

theorem coefficientMap_eq (A B D S : ℕ) (x : BaseCurve) :
    coefficientMap A B D S x.val = PrimExt.aMap A B D S x := rfl

theorem weightedPhaseInclusion_mfderiv (D m : ℕ) (x : BaseCurve) :
    mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) (weightedPhaseInclusion D m) x =
      (fderiv ℝ (weightedMap D m) x.val).comp
        (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) x) := by
  have hi := (real_inclusion_contMDiff (parameters 0)).mdifferentiable (by simp) x
  have hm := (weightedMap_contDiff D m).differentiable (by simp) x.val
  have hc := mfderiv_comp x hm.mdifferentiableAt hi
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3)))
    (weightedPhaseInclusion D m) x = _ at hc
  simpa only [mfderiv_eq_fderiv] using hc

theorem weightedFSPrimitive_eq (D m : ℕ) (c : ℝ) (x : BaseCurve) :
    weightedFSPrimitive D m c x = (weightedPrimitive D m c x.val).comp
      (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) x) := by
  unfold weightedFSPrimitive manifoldPullbackOneForm manifoldMapDifferential
  rw [weightedPhaseInclusion_mfderiv]
  apply ContinuousLinearMap.ext
  intro v
  unfold weightedPrimitive
  rfl

theorem extendedPrimitive_eq (A B D S : ℕ) (c β m δ : ℝ) (p : Radial.Plane) (x : BaseCurve) :
    PrimExt.extFamily A B D S c β m δ p x = (extendedPrimitive A B D S c β m δ p x.val).comp
      (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) x) := by
  unfold PrimExt.extFamily extendedPrimitive
  rw [coefficientMap_eq]
  apply ContinuousLinearMap.ext
  intro v
  simp only [Finset.sum_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, weightedFSPrimitive_eq]

theorem physicalExtension_eq (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ)
    (p : Moments 2) (x : BaseCurve) :
    primitiveExt A B D S c L P ℓ p x = (physicalExtension A B D S c L P ℓ p x.val).comp
      (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) x) :=
  extendedPrimitive_eq _ _ _ _ _ _ _ _ _ _

#check_explicit weightedMap
#check_explicit weightedPrimitive
#check_explicit coefficientMap
#check_explicit extendedPrimitive
#check_explicit physicalExtension

end SymplecticPacking.BranchLarge3.RawCubic
