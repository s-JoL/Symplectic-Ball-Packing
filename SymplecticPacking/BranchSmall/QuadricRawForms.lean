import SymplecticPacking.Explicit
import OAI.Geometry.BallPacking.Models.EqualNormalModelConvergence
import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus

/-!
# Ambient representatives of the diagonal-quadric forms

The data are global formulas on the affine ambient vector space. Manifold
coordinates occur only in the proofs identifying their restrictions to the curve.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.RawQuadric
open Set Function Manifold ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine Fubini--Study form in ambient quadric coordinates. -/
def ambientFSForm {m : ℕ} (c : ℝ) (z : Affine m) : Affine m →L[ℝ] Affine m →L[ℝ] ℝ :=
  (affineFSForm c (affinePhase m z)).bilinearComp (affinePhase m) (affinePhase m)

/-- An arbitrary displayed parameter coefficient multiplying the ambient primitive. -/
def scaledPrimitive {m : ℕ} {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (z : Affine m) :
    Affine m →L[ℝ] ℝ := ρ p • ambientFSPrimitive c z

def scaledForm {m : ℕ} {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (z : Affine m) :
    Affine m →L[ℝ] Affine m →L[ℝ] ℝ := ρ p • ambientFSForm c z

/-- The physical horizontal primitive, before restriction to the quadric curve. -/
def ambientGamma {m q : ℕ} (b : ℝ) (p : Fin q → ℝ) (z : Affine m) : Affine m →L[ℝ] ℝ :=
  scaledPrimitive (1 / Real.pi) (equalNormalCoefficient q b) p z

def ambientPhysicalForm {m q : ℕ} (b : ℝ) (p : Fin q → ℝ) (z : Affine m) :
    Affine m →L[ℝ] Affine m →L[ℝ] ℝ :=
  scaledForm (1 / Real.pi) (equalNormalCoefficient q b) p z

theorem ambientFSForm_contDiff {m : ℕ} (c : ℝ) : ContDiff ℝ ∞ (ambientFSForm (m := m) c) := by
  have h := (affineFSForm_smooth (ι := Option (Fin m)) c).comp (affinePhase m).contDiff
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  change ContDiff ℝ ∞ (fun z => affineFSForm c (affinePhase m z) (affinePhase m u) (affinePhase m v))
  exact (h.clm_apply contDiff_const).clm_apply contDiff_const

theorem ambientFSForm_skew {m : ℕ} (c : ℝ) (z u v : Affine m) :
    ambientFSForm c z u v = -ambientFSForm c z v u :=
  affineFSForm_skew c (affinePhase m z) (affinePhase m u) (affinePhase m v)

theorem scaledForm_skew {m : ℕ} {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (z u v : Affine m) :
    scaledForm c ρ p z u v = -scaledForm c ρ p z v u := by
  change ρ p * ambientFSForm c z u v = -(ρ p * ambientFSForm c z v u)
  rw [ambientFSForm_skew]
  ring

section parameter
variable {m : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaledPrimitive_contDiff (c : ℝ) {ρ : P → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (fun x : P × Affine m => scaledPrimitive c ρ x.1 x.2) :=
  (hρ.comp contDiff_fst).smul ((ambientFSPrimitive_smooth (m := m) c).comp contDiff_snd)

theorem scaledForm_contDiff (c : ℝ) {ρ : P → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (fun x : P × Affine m => scaledForm c ρ x.1 x.2) := by
  have h := (ambientFSForm_contDiff (m := m) c).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : P × Affine m → Affine m))
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  change ContDiff ℝ ∞ (fun x : P × Affine m => ρ x.1 * ambientFSForm c x.2 u v)
  exact (hρ.comp contDiff_fst).mul ((h.clm_apply contDiff_const).clm_apply contDiff_const)

end parameter

theorem scaledPrimitive_exterior {m : ℕ} {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (z : Affine m) :
    euclideanExteriorOneForm (scaledPrimitive c ρ p) z = scaledForm c ρ p z := by
  change euclideanExteriorOneForm (ρ p • ambientFSPrimitive c) z = _
  rw [euclideanExteriorOneForm_smul _ ((ambientFSPrimitive_smooth c).differentiable (by simp) z),
    ambientFSPrimitive_exterior]
  rfl

def ambientLargeGamma {m q : ℕ} (p : Fin (q + 1) → ℝ) (z : Affine m) : Affine m →L[ℝ] ℝ :=
  scaledPrimitive (1 / Real.pi) (largeNormalCoefficient q) p z

def ambientLargePhysicalForm {m q : ℕ} (p : Fin (q + 1) → ℝ) (z : Affine m) :
    Affine m →L[ℝ] Affine m →L[ℝ] ℝ :=
  scaledForm (1 / Real.pi) (largeNormalCoefficient q) p z

section restriction
variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]

theorem phaseInclusion_mfderiv (x : locus a) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,PlanePhase (Option (Fin m))) (phaseInclusion a) x =
      (affinePhase m).comp (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x) := by
  have hi := (real_inclusion_contMDiff a).mdifferentiable (by simp) x
  have hc := mfderiv_comp x (affinePhase m).hasFDerivAt.differentiableAt.mdifferentiableAt hi
  change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,PlanePhase (Option (Fin m))) (phaseInclusion a) x = _ at hc
  simpa only [mfderiv_eq_fderiv, (affinePhase m).fderiv] using hc

/-- Identification of the global raw base form with the curve form. -/
theorem curveFSForm_eq_raw (c : ℝ) (x : locus a) :
    curveFSForm a c x = (ambientFSForm c x.val).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x) := by
  unfold curveFSForm manifoldPullbackTwoForm manifoldMapDifferential
  rw [phaseInclusion_mfderiv]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem curveFSPrimitive_eq_raw (c : ℝ) (x : locus a) :
    curveFSPrimitive a c x = (ambientFSPrimitive c x.val).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x) := by
  unfold curveFSPrimitive manifoldPullbackOneForm manifoldMapDifferential
  rw [phaseInclusion_mfderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem scaledPrimitive_eq_raw {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (x : locus a) :
    ρ p • curveFSPrimitive a c x = (scaledPrimitive c ρ p x.val).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x) := by
  rw [curveFSPrimitive_eq_raw]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem scaledForm_eq_raw {P : Type} (c : ℝ) (ρ : P → ℝ) (p : P) (x : locus a) :
    ρ p • curveFSForm a c x = (scaledForm c ρ p x.val).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m) (Subtype.val : locus a → Affine m) x) := by
  rw [curveFSForm_eq_raw]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

section parameter
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaledPrimitive_restriction_contMDiff (c : ℝ) {ρ : P → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine m →L[ℝ] ℝ) ∞
      (fun x : P × locus a => scaledPrimitive c ρ x.1 x.2.val) :=
  (scaledPrimitive_contDiff (m := m) c hρ).contMDiff.comp
    (contMDiff_fst.prodMk_space ((real_inclusion_contMDiff a).comp contMDiff_snd))

theorem scaledForm_restriction_contMDiff (c : ℝ) {ρ : P → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine m →L[ℝ] Affine m →L[ℝ] ℝ) ∞
      (fun x : P × locus a => scaledForm c ρ x.1 x.2.val) :=
  (scaledForm_contDiff (m := m) c hρ).contMDiff.comp
    (contMDiff_fst.prodMk_space ((real_inclusion_contMDiff a).comp contMDiff_snd))

end parameter

theorem ambientFSForm_restriction_contMDiff (c : ℝ) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m →L[ℝ] Affine m →L[ℝ] ℝ) ∞
      (fun x : locus a => ambientFSForm c x.val) :=
  (ambientFSForm_contDiff c).contMDiff.comp (real_inclusion_contMDiff a)

end restriction

#check_explicit ambientFSForm
#check_explicit ambientGamma
#check_explicit ambientPhysicalForm
#check_explicit ambientLargeGamma
#check_explicit ambientLargePhysicalForm

end SymplecticPacking.BranchSmall.RawQuadric
