import SymplecticPacking.BranchSmall.TransportAnalytic
import SymplecticPacking.BranchSmall.ConeRadial
import SymplecticPacking.BranchSmall.ScaledReturnGrowth

/-!
# Positive-parameter graph coordinates for horizontal transport
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {q : ℕ}

def graphTube (a : Fin q → ℂ) (t : ℝ) (z : Affine q) : Tot q :=
  (z, (t : ℂ)⁻¹ • equations a z)

theorem graphTube_contDiff (a : Fin q → ℂ) (t : ℝ) : ContDiff ℝ ∞ (graphTube a t) :=
  (contDiff_id.prodMk ((equations_contDiff a).const_smul (t : ℂ)⁻¹)).restrict_scalars ℝ

theorem graphTube_fderiv (a : Fin q → ℂ) (t : ℝ) (z v : Affine q) :
    fderiv ℝ (graphTube a t) z v = (v, (t : ℂ)⁻¹ • jacobian z v) := by
  have hh := (hasFDerivAt_id (𝕜 := ℂ) z).prodMk ((equations_hasFDerivAt a z).const_smul (t : ℂ)⁻¹)
  change HasFDerivAt (graphTube a t) _ z at hh
  rw [hh.restrictScalars ℝ |>.fderiv]
  rfl

theorem graphTube_parameter_contDiff (a : Fin q → ℂ) {T : ℝ → ℝ}
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine q => graphTube a (T p.1) p.2) := by
  have hI : ContDiff ℝ ∞ (fun p : ℝ × Affine q => ((T p.1 : ℝ) : ℂ)⁻¹) :=
    (Complex.ofRealCLM.contDiff.comp (hT.comp contDiff_fst)).inv
      (fun p => Complex.ofReal_ne_zero.mpr (hT0 p.1))
  exact contDiff_snd.prodMk (hI.smul (((equations_contDiff a).restrict_scalars ℝ).comp contDiff_snd))

theorem graphTube_primitive (a : Fin q → ℂ) (b t : ℝ) :
    primitivePullback (dcForm (bundlePot b)) (graphTube a t) =
      normalAmbientPrimitive a (1 / Real.pi) b t := by
  have he : bundlePhaseCoordinates ∘ graphTube a t = normalConeCoordinates a t := by
    funext z
    rfl
  rw [bundlePot_dc, primitivePullback_comp (conePrimitive (1 / Real.pi) b)
    bundlePhaseCoordinates.contDiff (graphTube_contDiff a t), he, ← normalAmbientPrimitive_eq_cone]

theorem graphTube_form (a : Fin q → ℂ) (b t : ℝ) (z v w : Affine q) :
    bundleForm b (graphTube a t z) (fderiv ℝ (graphTube a t) z v) (fderiv ℝ (graphTube a t) z w) =
      normalAmbientForm a (1 / Real.pi) b t z v w := by
  have hLam := dcForm_contDiff_of (bundlePot_contDiff (q := q) b)
  have hh := primitivePullback_exterior hLam (graphTube_contDiff a t) z
  rw [graphTube_primitive] at hh
  exact (congrArg (fun L : Affine q →L[ℝ] Affine q →L[ℝ] ℝ => L v w) hh).symm

def radialCoefficient (y : Tot q) : ℝ :=
  2 * (1 + nsq y.1) ^ 2 / ((1 + nsq y.1) ^ 2 + wsq y.2)

theorem radialCoefficient_contDiff : ContDiff ℝ ∞ (radialCoefficient (q := q)) := by
  have hD : ContDiff ℝ ∞ (fun y : Tot q => (1 + nsq y.1) ^ 2) :=
    (contDiff_const.add (nsq_contDiff'.comp contDiff_fst)).pow 2
  exact (contDiff_const.mul hD).div (hD.add (wsq_contDiff'.comp contDiff_snd))
    (fun y => (add_pos_of_pos_of_nonneg (sq_pos_of_pos (one_add_nsq_pos y.1)) (wsq_nonneg y.2)).ne')

theorem radialCoefficient_nonneg (y : Tot q) : 0 ≤ radialCoefficient y := by
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos (one_add_nsq_pos y.1)) (wsq_nonneg y.2)).le

theorem radialCoefficient_le_two (y : Tot q) : radialCoefficient y ≤ 2 := by
  have hD : 0 < (1 + nsq y.1) ^ 2 + wsq y.2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (one_add_nsq_pos y.1)) (wsq_nonneg y.2)
  rw [radialCoefficient, div_le_iff₀ hD]
  nlinarith [wsq_nonneg y.2]

theorem bundleForm_radial_contraction (b : ℝ) (y k : Tot q) :
    bundleForm b y ((0 : Affine q), y.2) k = radialCoefficient y *
      (dcForm (bundlePot b) y k - ambientFSPrimitive (1 / Real.pi) y.1 k.1) := by
  have hR : bundlePhaseCoordinates ((0 : Affine q), y.2) = (0, complexCartesian y.2) := by
    apply Prod.ext
    · exact map_zero (affinePhase q)
    · rfl
  unfold bundleForm ddcForm
  rw [bundlePot_dc, primitivePullback_exterior (conePrimitive_smooth _ _) bundlePhaseCoordinates.contDiff,
    bundlePhaseCoordinates.fderiv]
  change euclideanExteriorOneForm (conePrimitive (1 / Real.pi) b) (bundlePhaseCoordinates y)
    (bundlePhaseCoordinates (0, y.2)) (bundlePhaseCoordinates k) = _
  rw [hR]
  change euclideanExteriorOneForm (conePrimitive (1 / Real.pi) b) (bundlePhaseCoordinates y)
    (0, (bundlePhaseCoordinates y).2) (bundlePhaseCoordinates k) = _
  rw [conePrimitive_radial_contraction]
  simp only [primitivePullback, bundlePhaseCoordinates.fderiv, ContinuousLinearMap.comp_apply]
  have hn : phaseSq (affinePhase q y.1) = nsq y.1 := (nsq_eq_phaseSq y.1).symm
  have hw : phaseSq (complexCartesian y.2) = wsq y.2 := complexCartesian_sq y.2
  simp only [bundlePhaseCoordinates, prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearEquiv.coe_coe, coneDenominator] at hn hw ⊢
  rw [hn, hw]
  rfl

theorem normalReturnField_contraction (a : Fin q → ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (t : ℝ) (z v : Affine q) :
    normalAmbientForm a (1 / Real.pi) b t z (normalReturnField a b t z) v =
      -(normalAmbientPrimitive a (1 / Real.pi) b t z v - ambientFSPrimitive (1 / Real.pi) z v) := by
  have hi := normalAmbientForm_isInvertible a (one_div_pos.mpr Real.pi_pos) hb0 hb t z
  have he : normalAmbientPrimitive a (1 / Real.pi) 0 t = ambientFSPrimitive (1 / Real.pi) := by
    simp only [normalAmbientPrimitive, mul_zero, sub_zero, one_smul, zero_smul, add_zero]
  unfold normalReturnField
  rw [map_neg, hi.self_apply_inverse, he]
  rfl

/-- In positive graph coordinates, horizontal transport is the normal Moser field
multiplied by a bounded scalar and `-1/t`. -/
theorem transportField_graphTube_base (a : Fin q → ℂ) {b t : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (ht : t ≠ 0) (z : Affine q) :
    (transportField a b t (graphTube a t z)).1 =
      (-(radialCoefficient (graphTube a t z) / t)) • normalReturnField a b t z := by
  let y := graphTube a t z
  let V := transportField a b t y
  let R : Tot q := (0, y.2)
  have hTc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hV := transportField_spec_of_time_ne a hb0 hb ht y
  have hsplit : fderiv ℝ (graphTube a t) z V.1 = V + (t⁻¹ : ℝ) • R := by
    rw [graphTube_fderiv]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, R, smul_zero, add_zero]
    · funext j
      have hj := congrFun hV.1 j
      change jacobian z V.1 j - (t : ℂ) * V.2 j = y.2 j at hj
      change (t : ℂ)⁻¹ * jacobian z V.1 j = V.2 j + (t⁻¹ : ℝ) • y.2 j
      rw [Complex.real_smul, Complex.ofReal_inv]
      field_simp [hTc]
      linear_combination hj
  have hker (v : Affine q) :
      jacobian y.1 (fderiv ℝ (graphTube a t) z v).1 -
        (t : ℂ) • (fderiv ℝ (graphTube a t) z v).2 = 0 := by
    rw [graphTube_fderiv]
    simp only [y, graphTube, smul_smul, mul_inv_cancel₀ hTc, one_smul, sub_self]
  have hpair (v : Affine q) :
      normalAmbientForm a (1 / Real.pi) b t z V.1 v = t⁻¹ * radialCoefficient y *
        (normalAmbientPrimitive a (1 / Real.pi) b t z v - ambientFSPrimitive (1 / Real.pi) z v) := by
    rw [← graphTube_form a b t z V.1 v, hsplit, map_add, add_apply,
      hV.2 _ (hker v), zero_add, map_smul, smul_apply, smul_eq_mul]
    rw [show R = ((0 : Affine q), y.2) from rfl, bundleForm_radial_contraction]
    have hprim := congrArg (fun L : Affine q →L[ℝ] ℝ => L v)
      (congrFun (graphTube_primitive a b t) z)
    simp only [primitivePullback, comp_apply] at hprim
    rw [hprim, graphTube_fderiv]
    change t⁻¹ * (radialCoefficient y *
      (normalAmbientPrimitive a (1 / Real.pi) b t z v - ambientFSPrimitive (1 / Real.pi) z v)) = _
    ring
  have hi := normalAmbientForm_isInvertible a (one_div_pos.mpr Real.pi_pos) hb0.le hb t z
  apply hi.injective
  apply ContinuousLinearMap.ext
  intro v
  change normalAmbientForm a (1 / Real.pi) b t z V.1 v = _
  rw [hpair, map_smul, smul_apply, smul_eq_mul, normalReturnField_contraction a hb0.le hb]
  ring

/-- A graph curve is determined by its base velocity when the graph parameter is nonzero. -/
theorem transport_velocity_of_graph (a : Fin q → ℂ) {b t : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (ht : t ≠ 0) {γ : ℝ → Tot q} {v : Tot q}
    (hd : HasDerivAt γ v t)
    (hg : ∀ᶠ s in 𝓝 t, equations a (γ s).1 = (s : ℂ) • (γ s).2)
    (hv : v.1 = (transportField a b t (γ t)).1) :
    v = transportField a b t (γ t) := by
  have h1 := (ContinuousLinearMap.fst ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivAt t hd
  have h2 := (ContinuousLinearMap.snd ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivAt t hd
  have he := ((equations_hasFDerivAt a (γ t).1).restrictScalars ℝ).comp_hasDerivAt t h1
  have hc := (hasDerivAt_id t).ofReal_comp
  have hdG := he.sub (hc.smul h2)
  have hG : (fun s : ℝ => equations a (γ s).1 - (s : ℂ) • (γ s).2) =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [hg] with s hs
    exact sub_eq_zero.mpr hs
  have hz := (hasDerivAt_const t (0 : Fin q → ℂ)).congr_of_eventuallyEq hG
  have hlin := hdG.unique hz
  simp only [ContinuousLinearMap.coe_restrictScalars', Complex.ofReal_one, one_smul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply, id_eq] at hlin
  have hV := (transportField_spec_of_time_ne a hb0 hb ht (γ t)).1
  apply Prod.ext hv
  funext j
  have hj := congrFun hlin j
  have hVj := congrFun hV j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hj hVj
  rw [hv] at hj
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht)
  linear_combination hVj - hj

end SymplecticPacking.BranchSmall.VT
