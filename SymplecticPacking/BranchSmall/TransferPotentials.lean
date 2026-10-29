import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.Forms.Basic
import SymplecticPacking.HighDim.Comparator.Isotopy
import OAI.Geometry.BallPacking.Models.RationalSlack

/-!
# Potentials and holomorphic graph identities for the vector transfer

These derivative-based identities are independent of trajectory existence and of the
three stage pullback theorems in TransferMapForm.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall
open Set Manifold
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold
variable {q : ℕ}

namespace VT

variable {q : ℕ}

/-! ### Smoothness of the potentials -/

theorem wsq_contDiff' : ContDiff ℝ ∞ (wsq (q := q)) := by
  unfold wsq
  apply ContDiff.sum
  intro j _
  have : (fun w : Fin q → ℂ => Complex.normSq (w j)) =
      fun w => (w j).re * (w j).re + (w j).im * (w j).im := by
    funext w; exact Complex.normSq_apply _
  rw [this]
  have hre : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  have him : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  exact (hre.mul hre).add (him.mul him)

theorem nsq_contDiff' : ContDiff ℝ ∞ (nsq (q := q)) := by
  unfold nsq
  have h1 : ContDiff ℝ ∞ (fun z : Affine q => Complex.normSq z.1) := by
    have : (fun z : Affine q => Complex.normSq z.1) =
        fun z => z.1.re * z.1.re + z.1.im * z.1.im := by
      funext z; exact Complex.normSq_apply _
    rw [this]
    have hre : ContDiff ℝ ∞ (fun z : Affine q => z.1.re) := Complex.reCLM.contDiff.comp contDiff_fst
    have him : ContDiff ℝ ∞ (fun z : Affine q => z.1.im) := Complex.imCLM.contDiff.comp contDiff_fst
    exact (hre.mul hre).add (him.mul him)
  exact h1.add (wsq_contDiff'.comp contDiff_snd)

theorem bundlePot_contDiff (b : ℝ) : ContDiff ℝ ∞ (bundlePot (q := q) b) := by
  unfold bundlePot
  have hn : ContDiff ℝ ∞ (fun y : Tot q => 1 + nsq y.1) :=
    contDiff_const.add (nsq_contDiff'.comp contDiff_fst)
  refine (hn.log fun y => (one_add_nsq_pos y.1).ne').add (contDiff_const.mul ?_)
  have hu : ContDiff ℝ ∞ (fun y : Tot q => 1 + wsq y.2 / (1 + nsq y.1) ^ 2) :=
    contDiff_const.add ((wsq_contDiff'.comp contDiff_snd).div (hn.pow 2)
      fun y => (pow_pos (one_add_nsq_pos y.1) 2).ne')
  refine hu.log fun y => ?_
  have := wsq_nonneg y.2
  have := pow_pos (one_add_nsq_pos y.1) 2
  positivity

/-! ### The ball chart: `C^* ω₀ = dd^c log(1 + |z|²)` -/

theorem nsq_eq_phaseSq (z : Affine q) : nsq z = phaseSq (affinePhase q z) := by
  simp only [nsq, wsq, phaseSq, phaseDot_apply, Fintype.sum_option, affinePhase_none,
    affinePhase_some, Complex.normSq_apply]

theorem logPot_eq : (fun z : Affine q => Real.log (1 + nsq z)) =
    fun z => Real.log (1 + phaseSq (affinePhase q z)) := by
  funext z; rw [nsq_eq_phaseSq]

theorem hasFDerivAt_logPot (z : Affine q) :
    HasFDerivAt (fun z : Affine q => Real.log (1 + nsq z))
      ((1 + phaseSq (affinePhase q z))⁻¹ •
        (((2 : ℝ) • phaseDot (affinePhase q z)).comp (affinePhase q))) z := by
  rw [logPot_eq]
  have h1 : HasFDerivAt (fun z : Affine q => phaseSq (affinePhase q z))
      (((2 : ℝ) • phaseDot (affinePhase q z)).comp (affinePhase q)) z :=
    (phaseSq_hasFDerivAt (affinePhase q z)).comp z (affinePhase q).hasFDerivAt
  have h2 := h1.const_add 1
  have hpos : 0 < 1 + phaseSq (affinePhase q z) := by
    have := phaseSq_nonneg (affinePhase q z); linarith
  exact h2.log hpos.ne'

theorem dcForm_logPot :
    dcForm (fun z : Affine q => Real.log (1 + nsq z)) = ambientFSPrimitive (1 / Real.pi) := by
  funext z
  apply ContinuousLinearMap.ext
  intro ξ
  have hpos : 0 < 1 + phaseSq (affinePhase q z) := by
    have := phaseSq_nonneg (affinePhase q z); linarith
  simp only [dcForm, ambientFSPrimitive, affineFSPrimitive, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, cxJ_apply, smul_eq_mul, (hasFDerivAt_logPot z).fderiv]
  rw [affinePhase_I, phaseDot_J_right]
  have hπ := Real.pi_pos
  field_simp
  ring

theorem ddcForm_logPot (z v w : Affine q) :
    ddcForm (fun z : Affine q => Real.log (1 + nsq z)) z v w =
      affineFSForm (1 / Real.pi) (affinePhase q z) (affinePhase q v) (affinePhase q w) := by
  unfold ddcForm
  rw [dcForm_logPot, ambientFSPrimitive_exterior]
  rfl

theorem returnPot_zero (a : Fin q → ℂ) (b : ℝ) :
    returnPot a b 0 = fun z : Affine q => Real.log (1 + nsq z) := by
  funext z
  simp [returnPot]

/-- **Ball chart** (lem:pre-fs): `C^* ω₀ = ω_FS = dd^c log(1 + |z|²)`. -/
theorem chart_form (a : Fin q → ℂ) (b : ℝ) (z v w : Affine q) :
    successorStandardForm q (fderiv ℝ (affineRadialTarget q (1 / Real.pi)) z v)
        (fderiv ℝ (affineRadialTarget q (1 / Real.pi)) z w) =
      ddcForm (returnPot a b 0) z v w := by
  rw [successorStandardForm_apply,
    affineRadialTarget_pullback a 0 (one_div_pos.2 Real.pi_pos).le z v w,
    normalAmbientForm_apply, returnPot_zero, ddcForm_logPot]
  ring

/-! ### The graph: `Ω_b|X₁ = pr^* ω_1` -/

/-- The graph map `z ↦ (z, F(z))` onto `X₁`. -/
def graphMap (a : Fin q → ℂ) (z : Affine q) : Tot q := (z, equations a z)

theorem graphMap_hasFDerivAt (a : Fin q → ℂ) (z : Affine q) :
    HasFDerivAt (graphMap a)
      ((ContinuousLinearMap.id ℝ (Affine q)).prod ((jacobian z).restrictScalars ℝ)) z :=
  (hasFDerivAt_id z).prodMk ((equations_hasFDerivAt a z).restrictScalars ℝ)

theorem graphMap_fderiv (a : Fin q → ℂ) (z u : Affine q) :
    fderiv ℝ (graphMap a) z u = (u, jacobian z u) := by
  rw [(graphMap_hasFDerivAt a z).fderiv]
  rfl

theorem graphMap_contDiff (a : Fin q → ℂ) : ContDiff ℝ ∞ (graphMap a) :=
  contDiff_id.prodMk ((equations_contDiff a).restrict_scalars ℝ)

theorem bundlePot_graphMap (a : Fin q → ℂ) (b : ℝ) :
    (fun z => bundlePot b (graphMap a z)) = returnPot a b 1 := by
  funext z
  simp [bundlePot, returnPot, graphPot, graphMap]

theorem pull1_dcForm_graphMap (a : Fin q → ℂ) (b : ℝ) :
    SymplecticPacking.Forms.pull1 (graphMap a) (dcForm (bundlePot b)) =
      dcForm (returnPot a b 1) := by
  funext z
  apply ContinuousLinearMap.ext
  intro ξ
  have hΦ := (bundlePot_contDiff (q := q) b).differentiable (by simp) (graphMap a z)
  have hg := (graphMap_hasFDerivAt a z).differentiableAt
  have hc : fderiv ℝ (returnPot a b 1) z =
      (fderiv ℝ (bundlePot b) (graphMap a z)).comp (fderiv ℝ (graphMap a) z) := by
    rw [← bundlePot_graphMap a b]
    exact fderiv_comp (g := bundlePot b) (f := graphMap a) z hΦ hg
  have hJ : fderiv ℝ (graphMap a) z (Complex.I • ξ) =
      Complex.I • fderiv ℝ (graphMap a) z ξ := by
    rw [graphMap_fderiv, graphMap_fderiv, map_smul]
    rfl
  simp only [SymplecticPacking.Forms.pull1_apply, dcForm, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, cxJ_apply, smul_eq_mul, hc, hJ]

/-- **The graph** (prop:vtr-return (a)): at a point of `X₁ = {W = F(z)}` and on vectors tangent
to `X₁`, `Ω_b = pr^* ω_1`. -/
theorem graph_form (a : Fin q → ℂ) (b : ℝ) {y : Tot q} (hy : y.2 = equations a y.1)
    {u u' : Tot q} (hu : u.2 = jacobian y.1 u.1) (hu' : u'.2 = jacobian y.1 u'.1) :
    bundleForm b y u u' = ddcForm (returnPot a b 1) y.1 u.1 u'.1 := by
  have hyg : y = graphMap a y.1 := Prod.ext rfl hy
  have hug : u = fderiv ℝ (graphMap a) y.1 u.1 := by
    rw [graphMap_fderiv]; exact Prod.ext rfl hu
  have hug' : u' = fderiv ℝ (graphMap a) y.1 u'.1 := by
    rw [graphMap_fderiv]; exact Prod.ext rfl hu'
  have hdc : DifferentiableAt ℝ (dcForm (bundlePot (q := q) b)) (graphMap a y.1) := by
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (bundlePot (q := q) b)) :=
      (bundlePot_contDiff b).fderiv_right (m := ∞) (by simp)
    have h2 : ContDiff ℝ ∞ (dcForm (bundlePot (q := q) b)) := by
      unfold dcForm
      exact (h1.clm_comp contDiff_const).const_smul _
    exact h2.differentiable (by simp) _
  have key := SymplecticPacking.Forms.pull2_d1_apply (x := y.1)
    ((graphMap_contDiff a).contDiffAt.of_le (by simp)) hdc
  rw [pull1_dcForm_graphMap] at key
  have k := congrArg (fun L => L u.1 u'.1) key
  simp only [SymplecticPacking.Forms.pull2_apply] at k
  change ddcForm (returnPot a b 1) y.1 u.1 u'.1 =
    ddcForm (bundlePot b) (graphMap a y.1) _ _ at k
  rw [k, ← hug, ← hug', ← hyg]
  rfl

end VT

end SymplecticPacking.BranchSmall
