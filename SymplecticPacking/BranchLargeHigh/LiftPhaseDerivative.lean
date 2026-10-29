import SymplecticPacking.BranchLargeHigh.LiftPhaseSmooth
import SymplecticPacking.BranchLargeHigh.FibrePoincare

/-!
# Exactness of the lifted Liouville defect

The closed difference between the transfer's Liouville pullback and the normal
coupling primitive has zero restriction on the zero section. Its relative radial
Poincaré primitive is exactly the phase used in ChartLift.
-/

noncomputable section
namespace SymplecticPacking.BranchLargeHigh.Two

open Set Filter Topology Manifold ContinuousLinearMap
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold

variable {q : ℕ}

abbrev Source (q : ℕ) := RealModel × Fibre (q + 2)

def curveProduct (g : RealModel → Surface q) : Source q → Surface q × Fibre (q + 2) :=
  flatProductMap g

theorem curveProduct_contMDiff {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) :
    ContMDiff 𝓘(ℝ,Source q) 𝓘(ℝ,Source q) ∞ (curveProduct g) := by
  intro x
  exact flatProductMap_smoothAt hg.contMDiffAt

def localTransfer (h₂ : ℝ) (g : RealModel → Surface q) : Source q → Ambient (q + 3) :=
  BranchSmall.vectorTransfer q h₂ (transferHeight h₂) ∘ curveProduct g

def localCanonical (g : RealModel → Surface q) : Source q → Source q →L[ℝ] ℝ :=
  fun p => euclideanPullbackOneForm (fun _ : ℝ => normalCouplingPrimitive (parameters q))
    (curveProduct g) (0, p)

def localDefect (h₂ : ℝ) (g : RealModel → Surface q) : Source q → Source q →L[ℝ] ℝ :=
  primitivePullback (ambientPrimitive (q + 2)) (localTransfer h₂ g) - localCanonical g

def localTransferDomain (b : ℝ) (g : RealModel → Surface q) : Set (Source q) :=
  curveProduct g ⁻¹' BranchSmall.transferDomain q b

theorem localTransferDomain_isOpen (b : ℝ) {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) :
    IsOpen (localTransferDomain b g) :=
  (BranchSmall.transferDomain_isOpen q b).preimage (curveProduct_contMDiff hg).continuous

theorem localTransfer_contDiffOn {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) :
    ContDiffOn ℝ ∞ (localTransfer h₂ g) (localTransferDomain (transferHeight h₂) g) := by
  have hhb : h₂ < transferHeight h₂ := by unfold transferHeight; linarith
  have hspec := BranchSmall.vectorTransfer_spec q hh hhb (LiftSmooth.transferHeight_lt hh2)
  exact (hspec.1.comp (curveProduct_contMDiff hg).contMDiffOn (fun _ hp => hp)).contDiffOn

theorem localCanonical_contDiff {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) : ContDiff ℝ ∞ (localCanonical g) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hh := euclideanPullbackOneForm_contDiffAt
    (α := fun _ : ℝ => normalCouplingPrimitive (parameters q)) (g := curveProduct g) (p := (0, p))
    (normalCouplingPrimitive_smooth (parameters q)) ((curveProduct_contMDiff hg).contMDiffAt (x := p))
  exact hh.comp p (contDiff_const.prodMk contDiff_id).contDiffAt

theorem localLiouville_contDiffOn {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) :
    ContDiffOn ℝ ∞ (primitivePullback (ambientPrimitive (q + 2)) (localTransfer h₂ g))
      (localTransferDomain (transferHeight h₂) g) := by
  exact ((ambientPrimitive_contDiff _).comp_contDiffOn (localTransfer_contDiffOn hh hh2 hg)).clm_comp
    ((localTransfer_contDiffOn hh hh2 hg).fderiv_of_isOpen (m := ∞)
      (localTransferDomain_isOpen _ hg) (by simp))

theorem localDefect_contDiffOn {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) :
    ContDiffOn ℝ ∞ (localDefect h₂ g) (localTransferDomain (transferHeight h₂) g) :=
  (localLiouville_contDiffOn hh hh2 hg).sub (localCanonical_contDiff hg).contDiffOn

theorem localDefect_closed {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g)
    (p : Source q) (hp : p ∈ localTransferDomain (transferHeight h₂) g) :
    euclideanExteriorOneForm (localDefect h₂ g) p = 0 := by
  have hP := (localTransfer_contDiffOn hh hh2 hg).contDiffAt
    ((localTransferDomain_isOpen _ hg).mem_nhds hp)
  have hL := (localLiouville_contDiffOn hh hh2 hg).contDiffAt
    ((localTransferDomain_isOpen _ hg).mem_nhds hp)
  have hC := (localCanonical_contDiff hg).contDiffAt (x := p)
  rw [localDefect, euclideanExteriorOneForm_sub (hL.differentiableAt (by simp))
    (hC.differentiableAt (by simp)), primitivePullback_exterior_at (ambientPrimitive_contDiff _).contDiffAt hP,
    ambientPrimitive_exterior]
  have hc := euclidean_manifold_pullback_exterior
    (fun c y hy => ((normalCouplingPrimitive_smooth (parameters q)).spatial_smooth 0 c hy).contDiffWithinAt)
    ((curveProduct_contMDiff hg).contMDiffAt (x := p))
  change euclideanExteriorOneForm (localCanonical g) p = _ at hc
  rw [hc, normalCouplingPrimitive_exterior]
  have hhb : h₂ < transferHeight h₂ := by unfold transferHeight; linarith
  have hspec := BranchSmall.vectorTransfer_spec q hh hhb (LiftSmooth.transferHeight_lt hh2)
  have hφ : MDifferentiableAt 𝓘(ℝ,Source q) 𝓘(ℝ,Ambient (q + 3))
      (BranchSmall.vectorTransfer q h₂ (transferHeight h₂)) (curveProduct g p) :=
    ((hspec.1 _ hp).contMDiffAt ((BranchSmall.transferDomain_isOpen q _).mem_nhds hp)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp p hφ ((curveProduct_contMDiff hg).mdifferentiable (by simp) p)
  rw [mfderiv_eq_fderiv] at hchain
  change fderiv ℝ (localTransfer h₂ g) p = _ at hchain
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [sub_apply, zero_apply, sub_eq_zero, ContinuousLinearMap.bilinearComp_apply]
  rw [hchain]
  exact hspec.2.2.1 (curveProduct g p) hp _ _

theorem curveFSPrimitive_along_map {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) (c : ℝ) (z v : RealModel) :
    curveFSPrimitive (parameters q) c (g z)
      (manifoldMapDifferential (E := RealModel) (F := RealModel) g z v) =
      ambientFSPrimitive c (g z).val (fderiv ℝ (fun z => (g z).val) z v) := by
  have hi : ContDiff ℝ ∞ (fun z => (g z).val) :=
    ((real_inclusion_contMDiff (parameters q)).comp hg).contDiff
  have hp := mfderiv_comp z ((phaseInclusion_smooth (parameters q)).mdifferentiable (by simp) (g z))
    (hg.mdifferentiable (by simp) z)
  rw [mfderiv_eq_fderiv] at hp
  have he : phaseInclusion (parameters q) ∘ g = (affinePhase (q + 2)) ∘ (fun z => (g z).val) := rfl
  rw [he, fderiv_comp z (affinePhase (q + 2)).differentiableAt (hi.differentiable (by simp) z),
    (affinePhase (q + 2)).fderiv] at hp
  have hv := congrArg (fun L => L v) hp
  change affineFSPrimitive c (affinePhase (q + 2) (g z).val)
    (manifoldMapDifferential (E := PlanePhase (Option (Fin (q + 2)))) (F := RealModel)
      (phaseInclusion (parameters q)) (g z)
      (manifoldMapDifferential (E := RealModel) (F := RealModel) g z v)) = _
  change affinePhase (q + 2) (fderiv ℝ (fun z => (g z).val) z v) =
    mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin (q + 2))))
      (phaseInclusion (parameters q)) (g z) (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) g z v) at hv
  have hv' : manifoldMapDifferential (E := PlanePhase (Option (Fin (q + 2)))) (F := RealModel)
      (phaseInclusion (parameters q)) (g z)
      (manifoldMapDifferential (E := RealModel) (F := RealModel) g z v) =
      affinePhase (q + 2) (fderiv ℝ (fun z => (g z).val) z v) := by
    convert! hv.symm using 1
  exact (congrArg (affineFSPrimitive c (affinePhase (q + 2) (g z).val)) hv').trans rfl

theorem curveProduct_differential {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) (p u : Source q) :
    manifoldMapDifferential (E := Source q) (F := Source q) (flatProductMap g) p u =
      (manifoldMapDifferential (E := RealModel) (F := RealModel) g p.1 u.1, u.2) := by
  have hd := flatProductMap_derivative (hg.contMDiffAt (x := p.1)) (V := Fibre (q + 2))
  have hv := congrArg (fun L => L u) hd
  convert! hv using 1

theorem localCanonical_zero {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) (z v : RealModel) :
    localCanonical g (z, 0) (v, 0) =
      ambientFSPrimitive (1 / Real.pi) (g z).val (fderiv ℝ (fun z => (g z).val) z v) := by
  change normalCouplingPrimitive (parameters q) (flatProductMap g (z, 0))
    (manifoldMapDifferential (E := Source q) (F := Source q) (flatProductMap g) (z, 0) (v, 0)) = _
  rw [curveProduct_differential hg, normalCouplingPrimitive_apply]
  change 1 / 2 * phaseArea (0 : Fibre (q + 2)) 0 +
    (1 - 2 * Real.pi * phaseSq (0 : Fibre (q + 2))) *
      curveFSPrimitive (parameters q) (1 / Real.pi) (g z)
        (manifoldMapDifferential (E := RealModel) (F := RealModel) g z v) = _
  simp only [map_zero, zero_apply, mul_zero, phaseSq, phaseDot_apply, Pi.zero_apply,
    Prod.fst_zero, Prod.snd_zero, add_zero, Finset.sum_const_zero, sub_zero, one_mul, zero_add]
  exact curveFSPrimitive_along_map hg _ z v

theorem localCanonical_radial {g : RealModel → Surface q}
    (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g) (p : Source q) (t : ℝ) :
    localCanonical g (fibreScale t p) (fibreRadial p) = 0 := by
  change normalCouplingPrimitive (parameters q) (flatProductMap g (fibreScale t p))
    (manifoldMapDifferential (E := Source q) (F := Source q) (flatProductMap g)
      (fibreScale t p) (fibreRadial p)) = _
  rw [curveProduct_differential hg, normalCouplingPrimitive_apply]
  change 1 / 2 * phaseArea (t • p.2) p.2 +
    (1 - 2 * Real.pi * phaseSq (t • p.2)) *
      curveFSPrimitive (parameters q) (1 / Real.pi) (g p.1)
        (manifoldMapDifferential (E := RealModel) (F := RealModel) g p.1 0) = 0
  simp only [map_smul, smul_apply, smul_eq_mul, phaseArea_self, map_zero,
    mul_zero, add_zero]

theorem localDefect_zero {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g)
    (z v : RealModel) : localDefect h₂ g (z, 0) (v, 0) = 0 := by
  let Z : RealModel →L[ℝ] Source q := (ContinuousLinearMap.id ℝ RealModel).prod 0
  have hz : (z, (0 : Fibre (q + 2))) ∈ localTransferDomain (transferHeight h₂) g := by
    change (∑ j, planeMoments (0 : Fibre (q + 2)) j) < transferHeight h₂
    simpa only [planeMoments, radialArea, radiusSq, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, mul_zero, Finset.sum_const_zero] using
      LiftSmooth.transferHeight_pos hh
  have hL := ((localTransfer_contDiffOn hh hh2 hg).contDiffAt
    ((localTransferDomain_isOpen _ hg).mem_nhds hz)).differentiableAt (by simp)
  have hi : ContDiff ℝ ∞ (fun z => (g z).val) :=
    ((real_inclusion_contMDiff (parameters q)).comp hg).contDiff
  have he : localTransfer h₂ g ∘ Z = affineRadialTarget (q + 2) (1 / Real.pi) ∘ (fun z => (g z).val) := by
    funext z
    exact basePhi_zero q h₂ (g z)
  have hd := fderiv_comp z hL Z.differentiableAt
  rw [he, fderiv_comp z ((affineRadialTarget_smooth (q + 2) (1 / Real.pi)).differentiable (by simp) ((g z).val))
    (hi.differentiable (by simp) z)] at hd
  have hv := congrArg (fun L => L v) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, Z,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hv
  have hval : localTransfer h₂ g (z, 0) = affineRadialTarget (q + 2) (1 / Real.pi) (g z).val :=
    basePhi_zero q h₂ (g z)
  change primitivePullback (ambientPrimitive (q + 2)) (localTransfer h₂ g) (z, 0) (v, 0) -
    localCanonical g (z, 0) (v, 0) = 0
  rw [primitivePullback, ContinuousLinearMap.comp_apply, hval, ← hv,
    affineRadialTarget_primitive, localCanonical_zero hg]
  exact sub_self _


theorem localTransferDomain_segment {b : ℝ} (g : RealModel → Surface q)
    {p : Source q} (hp : p ∈ localTransferDomain b g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fibreScale t p ∈ localTransferDomain b g := by
  change BranchSmall.totalMoment (t • p.2) < b
  rw [show t • p.2 = fun i => t • p.2 i from rfl, BranchSmall.totalMoment_smul]
  exact (mul_le_of_le_one_left (BranchSmall.totalMoment_nonneg p.2)
    (by nlinarith [ht.1, ht.2] : t ^ 2 ≤ 1)).trans_lt hp

theorem localDefect_radialPotential {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g)
    {p : Source q} (hp : p ∈ localTransferDomain (transferHeight h₂) g) :
    fibreRadialPotential (localDefect h₂ g) p = liftPhase q h₂ (g p.1) p.2 := by
  rw [liftPhase, zeroPhase_eq_zero, zero_add]
  unfold fibreRadialPotential radialPhase lineAction
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hL := ((localTransfer_contDiffOn hh hh2 hg).contDiffAt
    ((localTransferDomain_isOpen _ hg).mem_nhds (localTransferDomain_segment g hp ht))).differentiableAt (by simp)
  have hin : HasDerivAt (fun s : ℝ => fibreScale s p) (fibreRadial p) t := by
    simpa only [fibreScale_apply, fibreRadial_apply, one_smul, id_eq] using
      (hasDerivAt_const t p.1).prodMk ((hasDerivAt_id t).smul_const p.2)
  have hd := (hL.hasFDerivAt.comp_hasDerivAt t hin).deriv
  change localDefect h₂ g (fibreScale t p) (fibreRadial p) = _
  rw [localDefect, Pi.sub_apply, sub_apply, localCanonical_radial hg, sub_zero]
  change ambientPrimitive (q + 2) (localTransfer h₂ g (fibreScale t p))
    (fderiv ℝ (localTransfer h₂ g) (fibreScale t p) (fibreRadial p)) = _
  rw [ambientPrimitive_apply, ← hd]
  rfl

theorem localLiftPhase_hasFDerivAt {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {g : RealModel → Surface q} (hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g)
    {p : Source q} (hp : p ∈ localTransferDomain (transferHeight h₂) g) :
    HasFDerivAt (fun p : Source q => liftPhase q h₂ (g p.1) p.2) (localDefect h₂ g p) p := by
  have h := fibreRadialPotential_hasFDerivAt (localTransferDomain_isOpen _ hg)
    (localDefect_contDiffOn hh hh2 hg) (localDefect_closed hh hh2 hg) p
    (fun _ ht => localTransferDomain_segment g hp ht) (localDefect_zero hh hh2 hg p.1)
  apply h.congr_of_eventuallyEq
  filter_upwards [(localTransferDomain_isOpen _ hg).mem_nhds hp] with p hp
  exact (localDefect_radialPotential hh hh2 hg hp).symm


/-- A globally smooth test parametrization with invertible derivative at a prescribed point.
Only its germ is used; it does not enter the explicit transfer or phase definitions. -/
theorem exists_curve_testMap (b : Surface q) :
    ∃ (g : RealModel → Surface q) (z : RealModel),
      ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g ∧ g z = b ∧
        Function.Surjective (manifoldMapDifferential (E := RealModel) (F := RealModel) g z) := by
  let e := extChartAt 𝓘(ℝ,RealModel) b
  let z := e b
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source b)
  obtain ⟨r, hr, hrU, hre⟩ := exists_smooth_local_identity
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,RealModel)) b).mem_nhds hz)
  let g : RealModel → Surface q := e.symm ∘ r
  have hg : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ g :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).comp_contMDiff hr.contMDiff hrU
  have hrz : r z = z := hre.self_of_nhds
  have hgz : g z = b := by
    change e.symm (r z) = b
    rw [hrz]
    exact e.left_inv (mem_extChartAt_source b)
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,RealModel)) b).mem_nhds (hrU z))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z hi (hr.contMDiff.mdifferentiable (by simp) z)
  have hdr : mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) r z = ContinuousLinearMap.id ℝ RealModel := by
    rw [mfderiv_eq_fderiv, hre.fderiv_eq, fderiv_id]
  have hinv : (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) e.symm z).IsInvertible := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,RealModel)) hz
  refine ⟨g, z, hg, hgz, ?_⟩
  have hD : manifoldMapDifferential (E := RealModel) (F := RealModel) g z =
      mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) e.symm z := by
    change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) (e.symm ∘ r) z = _
    rw [hd, hdr, hrz]
    rfl
  rw [hD]
  exact hinv.bijective.surjective


/-- The phase differentiates to the Liouville defect of the normal transfer. -/
theorem liftPhase_differential {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    (y : Surface q × Fibre (q + 2)) (hy : y ∈ BranchSmall.transferDomain q (transferHeight h₂))
    (t : Source q) :
    manifoldMapDifferential (E := ℝ) (F := Source q)
      (fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2) y t =
    lamAmb (basePhi q h₂ y.1 y.2)
      (manifoldMapDifferential (E := Ambient (q + 3)) (F := Source q)
        (BranchSmall.vectorTransfer q h₂ (transferHeight h₂)) y t) -
      normalCouplingPrimitive (parameters q) y t := by
  obtain ⟨g, z, hg, hgz, hsur⟩ := exists_curve_testMap y.1
  obtain ⟨v, hv⟩ := hsur t.1
  let p : Source q := (z, y.2)
  let u : Source q := (v, t.2)
  have hpoint : curveProduct g p = y := by
    change (g z, y.2) = y
    rw [hgz]
  have hp : p ∈ localTransferDomain (transferHeight h₂) g := by
    change curveProduct g p ∈ BranchSmall.transferDomain q (transferHeight h₂)
    rwa [hpoint]
  have hD : manifoldMapDifferential (E := Source q) (F := Source q) (curveProduct g) p u = t := by
    rw [show curveProduct g = flatProductMap g from rfl, curveProduct_differential hg]
    change (manifoldMapDifferential (E := RealModel) (F := RealModel) g z v, t.2) = t
    rw [hv]
  have hφ := LiftSmooth.liftPhase_contMDiffOn_aux (q := q) hh hh2
  have hφd := (hφ y hy).contMDiffAt
    ((BranchSmall.transferDomain_isOpen q _).mem_nhds hy)
  have hφd' := hφd.mdifferentiableAt (by simp)
  rw [← hpoint] at hφd'
  have hc := mfderiv_comp p hφd' ((curveProduct_contMDiff hg).mdifferentiable (by simp) p)
  rw [mfderiv_eq_fderiv] at hc
  have hchain : fderiv ℝ (fun p : Source q => liftPhase q h₂ (g p.1) p.2) p u =
      manifoldMapDifferential (E := ℝ) (F := Source q)
        (fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2)
        (curveProduct g p) (manifoldMapDifferential (E := Source q) (F := Source q) (curveProduct g) p u) := by
    convert! congrArg (fun L => L u) hc using 1
  have hhb : h₂ < transferHeight h₂ := by unfold transferHeight; linarith
  have hspec := BranchSmall.vectorTransfer_spec q hh hhb (LiftSmooth.transferHeight_lt hh2)
  have hTd := ((hspec.1 y hy).contMDiffAt
    ((BranchSmall.transferDomain_isOpen q _).mem_nhds hy)).mdifferentiableAt (by simp)
  rw [← hpoint] at hTd
  have ht := mfderiv_comp p hTd ((curveProduct_contMDiff hg).mdifferentiable (by simp) p)
  rw [mfderiv_eq_fderiv] at ht
  have hTchain : fderiv ℝ (localTransfer h₂ g) p u =
      manifoldMapDifferential (E := Ambient (q + 3)) (F := Source q)
        (BranchSmall.vectorTransfer q h₂ (transferHeight h₂)) (curveProduct g p)
        (manifoldMapDifferential (E := Source q) (F := Source q) (curveProduct g) p u) := by
    convert! congrArg (fun L => L u) ht using 1
  have he := congrArg (fun L : Source q →L[ℝ] ℝ => L u)
    (localLiftPhase_hasFDerivAt hh hh2 hg hp).fderiv
  change fderiv ℝ (fun p : Source q => liftPhase q h₂ (g p.1) p.2) p u =
    primitivePullback (ambientPrimitive (q + 2)) (localTransfer h₂ g) p u - localCanonical g p u at he
  rw [hchain, primitivePullback, ContinuousLinearMap.comp_apply, hTchain, ambientPrimitive_apply] at he
  change _ = lamAmb (BranchSmall.vectorTransfer q h₂ (transferHeight h₂) (curveProduct g p)) _ -
    normalCouplingPrimitive (parameters q) (curveProduct g p)
      (manifoldMapDifferential (E := Source q) (F := Source q) (curveProduct g) p u) at he
  rw [hD, hpoint] at he
  exact he

end SymplecticPacking.BranchLargeHigh.Two
