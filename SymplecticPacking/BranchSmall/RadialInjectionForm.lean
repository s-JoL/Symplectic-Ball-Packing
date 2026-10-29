import SymplecticPacking.BranchSmall.BundlePotential

/-!
# Exact radial identification of the bundle primitive

The explicit injection is locally the radial cone bridge. Pulling back the cone
primitive and taking its exterior derivative gives the normal model form.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold

variable {q : ℕ}

@[simp] theorem complexCartesian_toC (w : PlanePhase (Fin q)) : complexCartesian (toC w) = w := by
  ext j <;> rfl

theorem wsq_toC_phaseSq (w : PlanePhase (Fin q)) : wsq (toC w) = phaseSq w := by
  unfold wsq
  rw [← complexCartesian_sq, complexCartesian_toC]

theorem radialInj_phaseCoordinates {b : ℝ} (z : Affine q) (w : PlanePhase (Fin q))
    (hw : phaseSq w < b / Real.pi) :
    bundlePhaseCoordinates (radialInj b z (toC w)) =
      normalRadial (b / Real.pi) (affinePhase q z, w) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd : Real.sqrt (b / Real.pi - phaseSq w) ≠ 0 :=
    (Real.sqrt_pos.mpr (sub_pos.mpr hw)).ne'
  have hs : Real.sqrt (b - Real.pi * phaseSq w) =
      Real.sqrt Real.pi * Real.sqrt (b / Real.pi - phaseSq w) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    field_simp
  have hfactor : (1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq (toC w)) =
      (1 + phaseSq (affinePhase q z)) * (Real.sqrt (b / Real.pi - phaseSq w))⁻¹ := by
    rw [wsq_toC_phaseSq, hs, nsq_eq_phaseSq]
    field_simp
  apply Prod.ext
  · rfl
  · change complexCartesian (fun j =>
      (((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq (toC w)) : ℝ) : ℂ) * toC w j) = _
    have hsmul : (fun j =>
        (((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq (toC w)) : ℝ) : ℂ) * toC w j) =
        ((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq (toC w))) • toC w := by
      ext j; exact Complex.real_smul.symm
    rw [hsmul, map_smul, complexCartesian_toC, hfactor]
    change _ = (1 + phaseSq (affinePhase q z)) • fsAffineMap (b / Real.pi) w
    rw [fsAffineMap, smul_smul]

section curve

variable (a : Fin q → ℂ) [Fact (Function.Injective a)] [Fact (∀ j, a j ≠ 0)]

def affineConeInclusion (x : ConeSpace a) : Tot q := (x.1.val, x.2)

theorem affineConeInclusion_contMDiff :
    ContMDiff 𝓘(ℝ, ConeModel q) 𝓘(ℝ, Tot q) ∞ (affineConeInclusion a) :=
  ((real_inclusion_contMDiff a).comp flatProduct_fst_smooth).prodMk_space flatProduct_snd_smooth

theorem affineConeInclusion_primitive (b : ℝ) (x : ConeSpace a) :
    centralConePrimitive a (1 / Real.pi) b x =
      (dcForm (bundlePot b) (affineConeInclusion a x)).comp
        (manifoldMapDifferential (E := Tot q) (F := ConeModel q) (affineConeInclusion a) x) := by
  rw [bundlePot_dc]
  have h := movingPrimitivePullback_comp_eq
    (α := conePrimitive (1 / Real.pi) b)
    (g := fun p : ℝ × ConeSpace a => centralConeCoordinates a p.2)
    (A := bundlePhaseCoordinates) (h := affineConeInclusion a)
    (t := 0) (x := x) (bundlePhaseCoordinates (q := q)).contDiff
    (affineConeInclusion_contMDiff a) (Eventually.of_forall fun _ => rfl)
  exact h

/-- The concrete radial map, before restricting to the named quadric model. -/
def radialCurveMap (b : ℝ) (x : NormalSpace a) : Tot q := radialInj b x.1.val (toC x.2)

theorem radialCurveMap_form {b : ℝ} (hb : 0 < b) (x : NormalSpace a)
    (hx : phaseSq x.2 < b / Real.pi) (v w : NormalModel q) :
    bundleForm b (radialCurveMap a b x)
      (mfderiv 𝓘(ℝ, NormalModel q) 𝓘(ℝ, Tot q) (radialCurveMap a b) x v)
      (mfderiv 𝓘(ℝ, NormalModel q) 𝓘(ℝ, Tot q) (radialCurveMap a b) x w) =
      globalHorizontalCoupling phaseArea (normalHorizontalPrimitive a 2 ∘ planeMoments) x v w := by
  obtain ⟨Ξ, hΞ, D, hD, hxD, hDd, _, he⟩ := exists_compact_radial_bridge a hb
    (K := {x}) isCompact_singleton (fun y hy => by simpa only [mem_singleton_iff.mp hy] using hx)
  have hxD : x ∈ D := hxD (mem_singleton x)
  let g : NormalSpace a → Tot q := affineConeInclusion a ∘ Ξ
  have hg : ContMDiff 𝓘(ℝ, NormalModel q) 𝓘(ℝ, Tot q) ∞ g :=
    (affineConeInclusion_contMDiff a).comp hΞ
  have heg : g =ᶠ[𝓝 x] radialCurveMap a b := by
    filter_upwards [hD.mem_nhds hxD] with y hy
    have heq := he hy
    have hr := radialInj_phaseCoordinates y.1.val y.2 (hDd y hy)
    have hcoord : bundlePhaseCoordinates (g y) = bundlePhaseCoordinates (radialCurveMap a b y) := by
      exact heq.trans hr.symm
    apply Prod.ext
    · exact affinePhase_injective q (congrArg Prod.fst hcoord)
    · exact complexCartesian.injective (congrArg Prod.snd hcoord)
  have hprim : manifoldPullbackOneForm (fun _ : ℝ => dcForm (bundlePot b)) g 0 =ᶠ[𝓝 x]
      normalCouplingPrimitive a := by
    filter_upwards [hD.mem_nhds hxD] with y hy
    have hc := cone_radial_primitive a hb hΞ (hDd y hy)
      (he.eventuallyEq_of_mem (hD.mem_nhds hy))
    have hcomp := manifoldMapDifferential_comp
      ((affineConeInclusion_contMDiff a).mdifferentiable (by simp) (Ξ y))
      (hΞ.mdifferentiable (by simp) y)
    change manifoldMapDifferential (E := Tot q) (F := NormalModel q) g y = _ at hcomp
    change (dcForm (bundlePot b) (g y)).comp
      (manifoldMapDifferential (E := Tot q) (F := NormalModel q) g y) = _
    rw [hcomp, ← ContinuousLinearMap.comp_assoc]
    change ((dcForm (bundlePot b) (affineConeInclusion a (Ξ y))).comp
      (manifoldMapDifferential (E := Tot q) (F := ConeModel q) (affineConeInclusion a) (Ξ y))).comp
        (manifoldMapDifferential (E := ConeModel q) (F := NormalModel q) Ξ y) = _
    rw [← affineConeInclusion_primitive]
    exact hc
  have hdc : ContDiff ℝ ∞ (dcForm (bundlePot (q := q) b)) := by
    unfold dcForm
    exact (((bundlePot_contDiff b).fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const).const_smul _
  have hext := manifold_pullback_exterior (α := dcForm (bundlePot b))
    (fun c => by
      rw [show chartOneForm (dcForm (bundlePot (q := q) b)) c = dcForm (bundlePot b) from
        funext (vector_chartOneForm _ c)]
      exact hdc.contDiffOn) hg x
  rw [manifoldExteriorOneForm_congr_germ hprim, normalCouplingPrimitive_exterior] at hext
  have hext' := congrArg (fun L => L v w) hext
  simp only [manifoldPullbackTwoForm, vector_exteriorOneForm, manifoldMapDifferential] at hext'
  change _ = bundleForm b (g x)
    (mfderiv 𝓘(ℝ, NormalModel q) 𝓘(ℝ, Tot q) g x v)
    (mfderiv 𝓘(ℝ, NormalModel q) 𝓘(ℝ, Tot q) g x w) at hext'
  rw [heg.eq_of_nhds, heg.mfderiv_eq] at hext'
  exact hext'.symm

end curve
end SymplecticPacking.BranchSmall.VT
