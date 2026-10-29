import SymplecticPacking.BranchSmall.ReturnPotential
import OAI.Geometry.BallPacking.BallMaps.QuadricRelativeShellFlow

/-!
# Homogeneous identities for the Moser return

The difference of two degree-two Hopf primitives is invariant under a variable
complex gauge. On the affine chart it is the difference of the normal
ambient primitives, hence the covector defining `returnField`.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set Function Filter Topology Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

section gauge
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The mixed Hopf primitive evaluated along a complex coordinate map. -/
def mixedPrimitiveAlong (P : (ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (G : E → (ι → ℂ)) (x v : E) : ℝ :=
  (1 - 2 * d) * hopfPrimitive c (complexCartesian (G x))
    (fderiv ℝ (fun y => complexCartesian (G y)) x v) +
  d * hopfPrimitive c (complexCartesian (P (G x)))
    (fderiv ℝ (fun y => complexCartesian (P (G y))) x v)

/-- The angular gauge correction cancels from the difference of mixed primitives. -/
theorem mixedPrimitiveAlong_difference_gauge
    {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℝ ∞ P)
    (hPn : ∀ z, z ≠ 0 → P z ≠ 0)
    (hPs : ∀ (ζ : ℂ) z, P (ζ • z) = ζ ^ 2 • P z)
    {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x ≠ 0) (hGx : G x ≠ 0) (c d : ℝ) (v : E) :
    mixedPrimitiveAlong P c d (fun y => S y • G y) x v -
        mixedPrimitiveAlong P c 0 (fun y => S y • G y) x v =
      mixedPrimitiveAlong P c d G x v - mixedPrimitiveAlong P c 0 G x v := by
  have hGc : complexCartesian (G x) ≠ 0 := fun h =>
    hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPc : complexCartesian (P (G x)) ≠ 0 := fun h =>
    hPn _ hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPG : DifferentiableAt ℝ (fun y => P (G y)) x :=
    (hP.differentiable (by simp) (G x)).comp x hG
  have he : (fun y => P (S y • G y)) = fun y => S y ^ 2 • P (G y) := funext fun y => hPs _ _
  dsimp only [mixedPrimitiveAlong]
  simp_rw [hPs]
  rw [
    hopfPrimitive_variable_gauge hS hG hSx hGc,
    hopfPrimitive_variable_power_gauge hS hPG hSx hPc]
  norm_num
  ring

end gauge

section affine
variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixedPrimitiveAlong_affine (a : Fin m → ℂ) (c d t : ℝ)
    {Z : E → Affine m} {x : E} (hZ : DifferentiableAt ℝ Z x) (v : E) :
    mixedPrimitiveAlong (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (affineComplex m (Z y))) x v =
      normalAmbientPrimitive a c d t (Z x) (fderiv ℝ Z x v) := by
  have hAc : DifferentiableAt ℝ (fun y => affineComplex m (Z y)) x :=
    ((affineComplex m).restrictScalars ℝ).differentiableAt.comp x hZ
  have hPc : DifferentiableAt ℝ (fun y => normalPolynomial a t (Z y)) x :=
    (((normalPolynomial_smooth a t).restrict_scalars ℝ).differentiable (by simp) _).comp x hZ
  have he : (fun y => homogeneousPolynomial a t (complexAffineLift (affineComplex m (Z y)))) =
      fun y => complexAffineLift (normalPolynomial a t (Z y)) := by
    funext y
    have h₁ : complexAffineLift (affineComplex m (Z y)) =
        (fun i => match i with | none => 1 | some j => affineComplex m (Z y) j) := by
      funext i; cases i <;> rfl
    have h₂ : complexAffineLift (normalPolynomial a t (Z y)) =
        (fun i => match i with | none => 1 | some j => normalPolynomial a t (Z y) j) := by
      funext i; cases i <;> rfl
    rw [h₁, h₂]
    exact homogeneousPolynomial_affine a t (Z y)
  dsimp only [mixedPrimitiveAlong]
  simp_rw [show ∀ y, homogeneousPolynomial a t (complexAffineLift (affineComplex m (Z y))) =
    complexAffineLift (normalPolynomial a t (Z y)) from congrFun he]
  rw [affineFSPrimitive_hopf_pullback hAc, affineFSPrimitive_hopf_pullback hPc]
  simp only [normalAmbientPrimitive, Pi.add_apply, add_apply, Pi.smul_apply,
    smul_apply, smul_eq_mul, primitivePullback, ContinuousLinearMap.comp_apply,
    ambientFSPrimitive, complexCartesian_affineComplex]
  have hD (u : E) : fderiv ℝ (fun y => affinePhase m (Z y)) x u =
      affinePhase m (fderiv ℝ Z x u) := by
    exact congrArg (fun L => L u) ((affinePhase m).hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  have hDP (u : E) : fderiv ℝ (fun y => complexCartesian (normalPolynomial a t (Z y))) x u =
      fderiv ℝ (fun y => complexCartesian (normalPolynomial a t y)) (Z x) (fderiv ℝ Z x u) :=
    congrArg (fun L => L u) (fderiv_comp x
      ((normalPolynomialCartesian_smooth a t).differentiable (by simp) _) hZ)
  rw [hD, hDP]



theorem homogeneousAlong_fderiv (a : Fin m → ℂ) (t : ℝ)
    {G : E → HomogeneousInput m} {x : E} (hG : DifferentiableAt ℝ G x) (v : E) :
    fderiv ℝ (fun y => complexCartesian (homogeneousPolynomial a t (G y))) x v =
      fderiv ℝ (homogeneousCartesian a t) (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x v) := by
  have hC : DifferentiableAt ℝ (fun y => complexCartesian (G y)) x :=
    (complexCartesian (ι := Option (Option (Fin m)))).differentiableAt.comp x hG
  have he : homogeneousCartesian a t ∘ (fun y => complexCartesian (G y)) =
      (fun y => complexCartesian (homogeneousPolynomial a t (G y))) := by
    funext y
    simp only [Function.comp_apply, homogeneousCartesian, ContinuousLinearEquiv.symm_apply_apply]
  have hd := fderiv_comp x ((homogeneousCartesian_smooth a t).differentiable (by simp) _) hC
  rw [he] at hd
  exact congrArg (fun L => L v) hd

theorem mixedPrimitiveAlong_real (a : Fin m → ℂ) (c d t : ℝ)
    {G : E → HomogeneousInput m} {x : E} (hG : DifferentiableAt ℝ G x) (v : E) :
    mixedPrimitiveAlong (homogeneousPolynomial a t) c d G x v =
      mixedHopfPrimitive (homogeneousCartesian a t) c d (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x v) := by
  simp only [mixedPrimitiveAlong, mixedHopfPrimitive, Pi.add_apply, add_apply, Pi.smul_apply,
    smul_apply, smul_eq_mul, primitivePullback, ContinuousLinearMap.comp_apply,
    homogeneousCartesian, ContinuousLinearEquiv.symm_apply_apply]
  rw [homogeneousAlong_fderiv a t hG]

theorem mixedHopfCurvatureAlong_real (a : Fin m → ℂ) (c d t : ℝ)
    {G : E → HomogeneousInput m} {x : E} (hG : DifferentiableAt ℝ G x)
    (hGx : G x ≠ 0) (v w : E) :
    mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d G x v w =
      mixedHopfForm (homogeneousCartesian a t) c d (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x v)
        (fderiv ℝ (fun y => complexCartesian (G y)) x w) := by
  have hz : complexCartesian (G x) ≠ 0 := fun he =>
    hGx (complexCartesian.injective (he.trans (map_zero _).symm))
  rw [mixedHopfForm_eq (homogeneousCartesian_smooth a t).contDiffAt hz
    (homogeneousCartesian_nonzero a t hz)]
  simp only [mixedHopfCurvaturePullback, hopfCurvaturePullback, add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.bilinearComp_apply,
    homogeneousCartesian, ContinuousLinearEquiv.symm_apply_apply]
  rw [homogeneousAlong_fderiv a t hG, homogeneousAlong_fderiv a t hG]

def returnQuotient (m : ℕ) (z : HomogeneousInput m) : Affine m :=
  (affineComplexEquiv m).symm (complexAffineQuotient z)

theorem returnQuotient_contDiffAt {z : HomogeneousInput m} (hz : z none ≠ 0) :
    ContDiffAt ℝ ∞ (returnQuotient m) z :=
  (affineComplexEquiv m).symm.contDiff.contDiffAt.comp z (complexAffineQuotient_smoothAt hz)

theorem mixedPrimitiveAlong_quotient (a : Fin m → ℂ) (c d t : ℝ)
    {G : E → HomogeneousInput m} {x : E} (hG : DifferentiableAt ℝ G x)
    (hGn : ∀ y, G y none ≠ 0) (v : E) :
    normalAmbientPrimitive a c d t (returnQuotient m (G x))
        (fderiv ℝ (fun y => returnQuotient m (G y)) x v) -
      normalAmbientPrimitive a c 0 t (returnQuotient m (G x))
        (fderiv ℝ (fun y => returnQuotient m (G y)) x v) =
      mixedPrimitiveAlong (homogeneousPolynomial a t) c d G x v -
        mixedPrimitiveAlong (homogeneousPolynomial a t) c 0 G x v := by
  let S : E → ℂ := fun y => (G y none)⁻¹
  have hc : ContDiff ℝ ∞ (fun y : HomogeneousInput m => y none) := contDiff_apply ℝ ℂ none
  have hcoord : DifferentiableAt ℝ (fun y => G y none) x :=
    (hc.differentiable (by simp) (G x)).comp x hG
  have hS : DifferentiableAt ℝ S x := hcoord.inv (hGn x)
  have hGx : G x ≠ 0 := fun he => hGn x (congrFun he none)
  have hg := mixedPrimitiveAlong_difference_gauge
    ((homogeneousPolynomial_smooth a t).restrict_scalars ℝ)
    (fun z hz => homogeneousPolynomial_nonzero a t hz)
    (homogeneousPolynomial_homogeneous a t) hS hG (inv_ne_zero (hGn x)) hGx c d v
  have he : (fun y => S y • G y) =
      fun y => complexAffineLift (affineComplex m (returnQuotient m (G y))) := by
    funext y
    have hA : affineComplex m (returnQuotient m (G y)) = complexAffineQuotient (G y) := by
      rw [← affineComplexEquiv_apply, returnQuotient, ContinuousLinearEquiv.apply_symm_apply]
    rw [hA]
    exact (complexAffineLift_quotient (hGn y)).symm
  rw [he] at hg
  have hQ : DifferentiableAt ℝ (fun y => returnQuotient m (G y)) x :=
    ((returnQuotient_contDiffAt (hGn x)).differentiableAt (by simp)).comp x hG
  rw [mixedPrimitiveAlong_affine a c d t hQ, mixedPrimitiveAlong_affine a c 0 t hQ] at hg
  exact hg

theorem mixedHopfCurvature_quotient (a : Fin m → ℂ) (c d t : ℝ)
    {G : E → HomogeneousInput m} {x : E} (hG : DifferentiableAt ℝ G x)
    (hGn : ∀ y, G y none ≠ 0) (v w : E) :
    normalAmbientForm a c d t (returnQuotient m (G x))
      (fderiv ℝ (fun y => returnQuotient m (G y)) x v)
      (fderiv ℝ (fun y => returnQuotient m (G y)) x w) =
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d G x v w := by
  have hQ : DifferentiableAt ℝ (fun y => returnQuotient m (G y)) x :=
    ((returnQuotient_contDiffAt (hGn x)).differentiableAt (by simp)).comp x hG
  have hq : DifferentiableAt ℝ (fun y => complexAffineQuotient (G y)) x :=
    ((complexAffineQuotient_smoothAt (hGn x)).differentiableAt (by simp)).comp x hG
  have hP := (homogeneousPolynomial_smooth a t).restrict_scalars ℝ
  have hn : ∀ z : HomogeneousInput m, z ≠ 0 → homogeneousPolynomial a t z ≠ 0 :=
    fun z hz => homogeneousPolynomial_nonzero a t hz
  have hs := homogeneousPolynomial_homogeneous a t
  have h1 := mixedHopf_affine_pullback a c d t hQ v w
  have h2 := mixedHopfCurvaturePullback_sphereLift hP hn hs hq c d v w
  have h3 := mixedHopfCurvaturePullback_chart_normalize hP hn hs hG hGn c d v w
  have he : (fun y => complexAffineLift (affineComplex m (returnQuotient m (G y)))) =
      fun y => complexAffineLift (complexAffineQuotient (G y)) := by
    funext y
    congr 1
    rw [← affineComplexEquiv_apply, returnQuotient, ContinuousLinearEquiv.apply_symm_apply]
  rw [he] at h1
  exact h1.symm.trans (h2.symm.trans h3)


/-- The affine primitive difference is exactly the defining return covector. -/
theorem normalAmbientPrimitive_difference (a : Fin m → ℂ) (b : ℝ) (z v : Affine m) :
    normalAmbientPrimitive a (1 / Real.pi) b 1 z v -
      normalAmbientPrimitive a (1 / Real.pi) 0 1 z v = b * dcForm (graphPot a) z v := by
  have hf : ContDiff ℝ ∞ (fun z : Affine m => Real.log (1 + nsq z)) :=
    (contDiff_const.add nsq_contDiff').log fun z => (one_add_nsq_pos z).ne'
  have hg : ContDiff ℝ ∞ (graphPot a) := by
    unfold graphPot
    have he : ContDiff ℝ ∞ (equations a) := (equations_contDiff a).restrict_scalars ℝ
    have hq : ContDiff ℝ ∞ (fun z : Affine m => wsq (equations a z) / (1 + nsq z) ^ 2) :=
      (wsq_contDiff'.comp he).div ((contDiff_const.add nsq_contDiff').pow 2)
        fun z => (pow_pos (one_add_nsq_pos z) 2).ne'
    refine (contDiff_const.add hq).log fun z => ?_
    have := div_nonneg (wsq_nonneg (equations a z)) (pow_pos (one_add_nsq_pos z) 2).le
    linarith
  have he : dcForm (returnPot a b 1) = dcForm (fun z => Real.log (1 + nsq z)) + b • dcForm (graphPot a) := by
    unfold returnPot
    simp only [one_mul]
    rw [dcForm_add (hf.differentiable (by simp)) ((hg.differentiable (by simp)).const_mul b),
      dcForm_const_mul (hg.differentiable (by simp))]
  have h0 : dcForm (returnPot a b 0) = dcForm (fun z => Real.log (1 + nsq z)) := by
    congr 1
    funext z
    unfold returnPot
    ring
  rw [returnPot_dc, one_mul] at he
  rw [returnPot_dc, zero_mul] at h0
  rw [he, h0]
  simp only [Pi.add_apply, add_apply, Pi.smul_apply, smul_apply, smul_eq_mul]
  ring

/-- Local test maps only certify the germ; all homogeneous and affine maps stay explicit. -/
theorem exists_homogeneous_testMap (z : HomogeneousInput m) (hz : z none ≠ 0) :
    ∃ G : HomogeneousInput m → HomogeneousInput m, ContDiff ℝ ∞ G ∧
      (∀ y, G y none ≠ 0) ∧ G =ᶠ[𝓝 z] id := by
  have hU : IsOpen {y : HomogeneousInput m | y none ≠ 0} :=
    (continuous_apply none).isOpen_preimage _ isOpen_ne
  exact exists_smooth_local_identity (hU.mem_nhds hz)

theorem returnQuotient_primitive_difference (a : Fin m → ℂ) (c d t : ℝ)
    (z v : HomogeneousInput m) (hz : z none ≠ 0) :
    normalAmbientPrimitive a c d t (returnQuotient m z) (fderiv ℝ (returnQuotient m) z v) -
      normalAmbientPrimitive a c 0 t (returnQuotient m z) (fderiv ℝ (returnQuotient m) z v) =
      mixedHopfPrimitive (homogeneousCartesian a t) c d (complexCartesian z) (complexCartesian v) -
        mixedHopfPrimitive (homogeneousCartesian a t) c 0 (complexCartesian z) (complexCartesian v) := by
  obtain ⟨G, hG, hGn, hGe⟩ := exists_homogeneous_testMap z hz
  have hGz : G z = z := hGe.self_of_nhds
  have hQ : (fun y => returnQuotient m (G y)) =ᶠ[𝓝 z] returnQuotient m := by
    filter_upwards [hGe] with y hy
    rw [hy, id_eq]
  have hC : (fun y => complexCartesian (G y)) =ᶠ[𝓝 z]
      (complexCartesian (ι := Option (Option (Fin m)))) := by
    filter_upwards [hGe] with y hy
    rw [hy, id_eq]
  have h := mixedPrimitiveAlong_quotient a c d t (hG.differentiable (by simp) z) hGn v
  rw [mixedPrimitiveAlong_real a c d t (hG.differentiable (by simp) z),
    mixedPrimitiveAlong_real a c 0 t (hG.differentiable (by simp) z),
    hQ.fderiv_eq, hC.fderiv_eq, ContinuousLinearEquiv.fderiv, hGz] at h
  exact h

theorem returnQuotient_curvature (a : Fin m → ℂ) (c d t : ℝ)
    (z v w : HomogeneousInput m) (hz : z none ≠ 0) :
    normalAmbientForm a c d t (returnQuotient m z)
      (fderiv ℝ (returnQuotient m) z v) (fderiv ℝ (returnQuotient m) z w) =
      mixedHopfForm (homogeneousCartesian a t) c d (complexCartesian z)
        (complexCartesian v) (complexCartesian w) := by
  obtain ⟨G, hG, hGn, hGe⟩ := exists_homogeneous_testMap z hz
  have hGz : G z = z := hGe.self_of_nhds
  have hG0 : G z ≠ 0 := fun he => hGn z (congrFun he none)
  have hQ : (fun y => returnQuotient m (G y)) =ᶠ[𝓝 z] returnQuotient m := by
    filter_upwards [hGe] with y hy
    rw [hy, id_eq]
  have hC : (fun y => complexCartesian (G y)) =ᶠ[𝓝 z]
      (complexCartesian (ι := Option (Option (Fin m)))) := by
    filter_upwards [hGe] with y hy
    rw [hy, id_eq]
  have h := mixedHopfCurvature_quotient a c d t (hG.differentiable (by simp) z) hGn v w
  rw [mixedHopfCurvatureAlong_real a c d t (hG.differentiable (by simp) z) hG0,
    hQ.fderiv_eq, hC.fderiv_eq, ContinuousLinearEquiv.fderiv, hGz] at h
  exact h


/-- The homogeneous symplectization field solves the projective mixed-form equation. -/
theorem homogeneousReturn_mixed_contraction (a : Fin m → ℂ) (t : ℝ) {c b s : ℝ}
    (hc : 0 < c) (hb0 : 0 ≤ s * b) (hb : s * b < 1 / 2)
    (z : PlanePhase (Option (Option (Fin m)))) (hz : z ≠ 0)
    (v : PlanePhase (Option (Option (Fin m)))) :
    mixedHopfForm (homogeneousCartesian a t) c (s * b) z
      (homogeneousConeField (homogeneousCartesian a t) c b s z) v =
      -(mixedHopfPrimitive (homogeneousCartesian a t) c b z v -
        mixedHopfPrimitive (homogeneousCartesian a t) c 0 z v) := by
  let F := homogeneousCartesian a t
  let H := homogeneousConeField F c b s z
  let α := mixedHopfPrimitive F c (s * b) z
  let C := mixedHopfForm F c (s * b) z
  have hF : ContDiff ℝ ∞ F := homogeneousCartesian_smooth a t
  have hFz : F z ≠ 0 := homogeneousCartesian_nonzero a t hz
  have hD : ∀ z, fderiv ℝ F z z = (2 : ℝ) • F z := homogeneousCartesian_euler a t
  have hJ : ∀ z v, fderiv ℝ F z (phaseJ v) = phaseJ (fderiv ℝ F z v) := homogeneousCartesian_J a t
  have hDJ : fderiv ℝ F z (phaseJ z) = (2 : ℝ) • phaseJ (F z) := by
    rw [hJ, hD, map_smul]
  have hi := homogeneousConePrimitive_nondegenerate hF.contDiffAt hz hFz (hD z) (hJ z) hc hb0 hb
  have he (w) : euclideanExteriorOneForm (homogeneousConePrimitive F c (s * b)) z H w =
      -(homogeneousConePrimitive F c b z w - homogeneousConePrimitive F c 0 z w) := by
    change (euclideanExteriorOneForm (homogeneousConePrimitive F c (s * b)) z)
      (-(euclideanExteriorOneForm (homogeneousConePrimitive F c (s * b)) z).inverse _) w = _
    rw [map_neg, hi.self_apply_inverse]
    rfl
  have hpr (d : ℝ) : mixedHopfPrimitive F c d z z = 0 := by
    simp only [mixedHopfPrimitive, Pi.add_apply, add_apply, Pi.smul_apply, smul_apply,
      smul_eq_mul, primitivePullback, ContinuousLinearMap.comp_apply, hD z, map_smul,
      hopfPrimitive_radial, mul_zero, add_zero]
  have hdot : phaseDot z H = 0 := by
    have hh := he (phaseJ z)
    rw [homogeneousConePrimitive_circle_contraction hF.contDiffAt hz hFz hDJ] at hh
    simp only [homogeneousConePrimitive, smul_apply, smul_eq_mul,
      mixedHopfPrimitive_circle hz hFz hDJ c b,
      mixedHopfPrimitive_circle hz hFz hDJ c 0, sub_self, neg_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc.ne'
  have hCr (w) : C w z = 0 := by
    change mixedHopfForm F c (s * b) z w z = _
    rw [mixedHopfForm_skew, mixedHopfForm_radial hF.contDiffAt hz hFz (hD z), neg_zero]
  have hα : α H = 0 := by
    have hh := he z
    rw [homogeneousConePrimitive_exterior hF.contDiffAt hz hFz,
      radialSymplectization_apply, hdot] at hh
    simp only [homogeneousConePrimitive, smul_apply, smul_eq_mul, hpr, mul_zero, sub_zero, neg_zero] at hh
    change 2 * (0 - α H * phaseSq z) + phaseSq z * C H z = 0 at hh
    rw [hCr] at hh
    have := phaseSq_pos hz
    nlinarith
  have hh := he v
  rw [homogeneousConePrimitive_exterior hF.contDiffAt hz hFz, radialSymplectization_apply] at hh
  change 2 * (phaseDot z H * α v - α H * phaseDot z v) + phaseSq z * C H v =
    -(phaseSq z * mixedHopfPrimitive F c b z v - phaseSq z * mixedHopfPrimitive F c 0 z v) at hh
  rw [hdot, hα] at hh
  have hρ := (phaseSq_pos hz).ne'
  apply (mul_left_cancel₀ hρ)
  change phaseSq z * C H v = _
  nlinarith [hh]


theorem returnQuotient_fderiv_surjective (z : HomogeneousInput m) (hz : z none ≠ 0) :
    Function.Surjective (fderiv ℝ (returnQuotient m) z) := by
  let L : Affine m → HomogeneousInput m := fun x => z none • complexAffineLift (affineComplex m x)
  have hA : ContDiff ℝ ∞ (fun x : Affine m => complexAffineLift (affineComplex m x)) :=
    complexAffineLift_smooth.comp ((affineComplex m).restrictScalars ℝ).contDiff
  have hL : ContDiff ℝ ∞ L := (contDiff_const (c := z none)).smul hA
  have he : returnQuotient m ∘ L = id := by
    funext x
    dsimp only [Function.comp_apply, returnQuotient, L]
    rw [complexAffineQuotient_smul _ hz, complexAffineQuotient_lift, ← affineComplexEquiv_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hLz : L (returnQuotient m z) = z := by
    have hA : affineComplex m (returnQuotient m z) = complexAffineQuotient z := by
      rw [← affineComplexEquiv_apply, returnQuotient, ContinuousLinearEquiv.apply_symm_apply]
    dsimp only [L]
    rw [hA, complexAffineLift_quotient hz, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have hd := fderiv_comp (returnQuotient m z)
    ((returnQuotient_contDiffAt (show L (returnQuotient m z) none ≠ 0 by rwa [hLz])).differentiableAt (by simp))
    (hL.differentiable (by simp) _)
  rw [he, fderiv_id, hLz] at hd
  intro v
  refine ⟨fderiv ℝ L (returnQuotient m z) v, ?_⟩
  exact (congrArg (fun K => K v) hd).symm

/-- The explicit affine return field is the derivative of the quotient applied to the
explicit homogeneous symplectization field. No existence-selected map enters this identity. -/
theorem returnField_eq_homogeneous (a : Fin m → ℂ) {b s : ℝ}
    (hb0 : 0 ≤ s * b) (hb : s * b < 1 / 2)
    (z : HomogeneousInput m) (hz : z none ≠ 0) :
    returnField a b s (returnQuotient m z) =
      fderiv ℝ (returnQuotient m) z
        (complexCartesian.symm (homogeneousConeField (homogeneousCartesian a 1)
          (1 / Real.pi) b s (complexCartesian z))) := by
  let H : HomogeneousInput m := complexCartesian.symm
    (homogeneousConeField (homogeneousCartesian a 1) (1 / Real.pi) b s (complexCartesian z))
  let Y : Affine m := fderiv ℝ (returnQuotient m) z H
  have hz0 : z ≠ 0 := fun he => hz (congrFun he none)
  have hzc : complexCartesian z ≠ 0 := fun he =>
    hz0 (complexCartesian.injective (he.trans (map_zero _).symm))
  have hc : 0 < 1 / Real.pi := one_div_pos.mpr Real.pi_pos
  have hY (v : Affine m) : ddcForm (returnPot a b s) (returnQuotient m z) Y v =
      -b * dcForm (graphPot a) (returnQuotient m z) v := by
    obtain ⟨w, hw⟩ := returnQuotient_fderiv_surjective z hz v
    rw [← hw, returnPot_ddc]
    change normalAmbientForm a (1 / Real.pi) (s * b) 1 (returnQuotient m z)
      (fderiv ℝ (returnQuotient m) z H) (fderiv ℝ (returnQuotient m) z w) = _
    rw [returnQuotient_curvature a (1 / Real.pi) (s * b) 1 z H w hz]
    change mixedHopfForm (homogeneousCartesian a 1) (1 / Real.pi) (s * b) (complexCartesian z)
      (complexCartesian (complexCartesian.symm
        (homogeneousConeField (homogeneousCartesian a 1) (1 / Real.pi) b s (complexCartesian z)))) _ = _
    rw [ContinuousLinearEquiv.apply_symm_apply,
      homogeneousReturn_mixed_contraction a 1 hc hb0 hb _ hzc,
      ← returnQuotient_primitive_difference a (1 / Real.pi) b 1 z w hz,
      normalAmbientPrimitive_difference]
    ring
  have hi := normalAmbientForm_isInvertible a hc hb0 hb 1 (returnQuotient m z)
  have hu : ∃! Y : Affine m, ∀ v, ddcForm (returnPot a b s) (returnQuotient m z) Y v =
      -b * dcForm (graphPot a) (returnQuotient m z) v := by
    refine ⟨Y, hY, ?_⟩
    intro Y' hY'
    apply hi.injective
    apply ContinuousLinearMap.ext
    intro v
    rw [← returnPot_ddc a b s]
    exact (hY' v).trans (hY v).symm
  simp only [returnField, dif_pos hu]
  exact hu.unique (SymplecticPacking.Explicit.the_spec hu) hY


/-- The same exact Moser field for the scaled equations `F/t`. -/
def normalReturnField (a : Fin m → ℂ) (b t : ℝ) (z : Affine m) : Affine m :=
  -(normalAmbientForm a (1 / Real.pi) b t z).inverse
    (normalAmbientPrimitive a (1 / Real.pi) b t z - normalAmbientPrimitive a (1 / Real.pi) 0 t z)

theorem normalReturnField_eq_homogeneous (a : Fin m → ℂ) (t : ℝ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (z : HomogeneousInput m) (hz : z none ≠ 0) :
    normalReturnField a b t (returnQuotient m z) =
      fderiv ℝ (returnQuotient m) z
        (complexCartesian.symm (homogeneousConeField (homogeneousCartesian a t)
          (1 / Real.pi) b 1 (complexCartesian z))) := by
  let H : HomogeneousInput m := complexCartesian.symm
    (homogeneousConeField (homogeneousCartesian a t) (1 / Real.pi) b 1 (complexCartesian z))
  let Y : Affine m := fderiv ℝ (returnQuotient m) z H
  have hz0 : z ≠ 0 := fun he => hz (congrFun he none)
  have hzc : complexCartesian z ≠ 0 := fun he =>
    hz0 (complexCartesian.injective (he.trans (map_zero _).symm))
  have hc : 0 < 1 / Real.pi := one_div_pos.mpr Real.pi_pos
  have hY (v : Affine m) : normalAmbientForm a (1 / Real.pi) b t (returnQuotient m z) Y v =
      -(normalAmbientPrimitive a (1 / Real.pi) b t (returnQuotient m z) v -
        normalAmbientPrimitive a (1 / Real.pi) 0 t (returnQuotient m z) v) := by
    obtain ⟨w, hw⟩ := returnQuotient_fderiv_surjective z hz v
    rw [← hw]
    change normalAmbientForm a (1 / Real.pi) b t (returnQuotient m z)
      (fderiv ℝ (returnQuotient m) z H) (fderiv ℝ (returnQuotient m) z w) = _
    rw [returnQuotient_curvature a (1 / Real.pi) b t z H w hz]
    change mixedHopfForm (homogeneousCartesian a t) (1 / Real.pi) b (complexCartesian z)
      (complexCartesian (complexCartesian.symm
        (homogeneousConeField (homogeneousCartesian a t) (1 / Real.pi) b 1 (complexCartesian z)))) _ = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have hh := homogeneousReturn_mixed_contraction a t hc
      (by simpa only [one_mul] using hb0) (by simpa only [one_mul] using hb) (s := 1)
      (complexCartesian z) hzc (complexCartesian w)
    simp only [one_mul] at hh
    rw [hh, ← returnQuotient_primitive_difference a (1 / Real.pi) b t z w hz]
  have hi := normalAmbientForm_isInvertible a hc hb0 hb t (returnQuotient m z)
  apply hi.injective
  apply ContinuousLinearMap.ext
  intro v
  change normalAmbientForm a (1 / Real.pi) b t (returnQuotient m z)
    (-(normalAmbientForm a (1 / Real.pi) b t (returnQuotient m z)).inverse _) v = _
  rw [map_neg, hi.self_apply_inverse]
  exact (hY v).symm

end affine
end SymplecticPacking.BranchSmall.VT
