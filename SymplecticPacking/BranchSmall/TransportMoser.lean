import SymplecticPacking.BranchSmall.TransportConservation
import SymplecticPacking.BranchSmall.TransportTrajectory
import SymplecticPacking.BranchSmall.TransferPotentials
import SymplecticPacking.Forms.Cartan
import OAI.Geometry.BallPacking.Annuli.AnnularMean

/-!
# Exact transport of the bundle form

Exact preservation of the bundle form by horizontal transport.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open SymplecticPacking.Forms
open SymplecticPacking.Return (CSField flow sigT)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff

set_option maxHeartbeats 1600000

variable {q : ℕ}

theorem transportField_orthogonal (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (s : ℝ) {y : Tot q} (hy : y ∈ goodSet q) (v : Tot q)
    (hv : jacobian y.1 v.1 - (s : ℂ) • v.2 = 0) :
    bundleForm b y (transportField a b s y) v = 0 := by
  have hex := transportField_existsUnique a hb0 hb s hy
  unfold transportField
  rw [dif_pos hex]
  exact (SymplecticPacking.Explicit.the_spec hex).2 v hv


section families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tangent_of_graph {a : Fin q → ℂ} {s : ℝ} {f : E → Tot q} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hgraph : ∀ x, equations a (f x).1 = (s : ℂ) • (f x).2) (v : E) :
    jacobian (f x).1 (fderiv ℝ f x v).1 - (s : ℂ) • (fderiv ℝ f x v).2 = 0 := by
  have he := ((equations_hasFDerivAt a (f x).1).restrictScalars ℝ).comp x hf.fst.hasFDerivAt
  have hm := hf.snd.hasFDerivAt.const_smul (s : ℂ)
  have hd := he.sub hm
  have hfun : (fun y => equations a (f y).1 - (s : ℂ) • (f y).2) = fun _ => 0 :=
    funext fun y => sub_eq_zero.mpr (hgraph y)
  have heq := hd.fderiv
  change fderiv ℝ (fun y => equations a (f y).1 - (s : ℂ) • (f y).2) x = _ at heq
  rw [hfun] at heq
  have hz : fderiv ℝ (fun _ : E => (0 : Fin q → ℂ)) x = 0 :=
    (hasFDerivAt_const (0 : Fin q → ℂ) x).fderiv
  rw [hz] at heq
  have hv := congrArg (fun L : E →L[ℝ] (Fin q → ℂ) => L v) heq
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, hf.hasFDerivAt.fst.fderiv,
    hf.hasFDerivAt.snd.fderiv, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd'] using hv.symm

/-- Horizontal transport preserves the form on any smooth family of starting points
on the central fibre. This statement uses a cutoff flow only to compare with
the already defined interval transport. -/
theorem transport_family_pullback (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {W : ℝ → Tot q → Tot q} {O : Set (Tot q)} (hW : CSField W)
    (hO : O ⊆ goodSet q) (hVW : AgreesOn (transportField a b) W O)
    {r : E → Tot q} (hr : ContDiff ℝ ∞ r) (hzero : ∀ x, equations a (r x).1 = 0)
    (hstays : ∀ x, StaysIn W O (r x)) :
    pull2 (fun x => flow W 1 (r x)) (bundleForm b) = pull2 r (bundleForm b) := by
  let σ : ℝ → ℝ := sigT 1
  let φ : ℝ → E → Tot q := fun t x => flow W (σ t) (r x)
  have hσ (t : ℝ) : σ t ∈ Icc (0 : ℝ) 1 := SymplecticPacking.Return.sigT_mem (by norm_num) t
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2) := hW.family_smooth 1 hr
  have hgraph : ∀ t x, equations a (φ t x).1 = (σ t : ℂ) • (φ t x).2 := by
    intro t x
    apply graph_along_trajectory a hb0 hb (γ := fun s => flow W s (r x))
      (by rw [hW.flow_zero]; exact hzero x)
      (fun s hs => hO (hstays x s hs)) ?_ (hσ t)
    intro s hs
    rw [hVW s hs _ (hstays x s hs)]
    exact (hW.flow_hasDerivAt (r x) s).hasDerivWithinAt
  have hkey := pull2_d1_const_univ
    (φ := φ) (V := fun t y => deriv σ t • W (σ t) y)
    (dcForm_contDiff_of (bundlePot_contDiff b)) hφ
    (hW.family_hasDerivAt 1 r) (by
      intro t
      funext x
      apply ContinuousLinearMap.ext
      intro v
      have ht := tangent_of_graph
        ((hφ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x)
        (hgraph t) v
      have ho := transportField_orthogonal a hb0 hb (σ t)
        (hO (hstays x (σ t) (hσ t))) _ ht
      rw [hVW (σ t) (hσ t) _ (hstays x (σ t) (hσ t))] at ho
      change bundleForm b (φ t x) (W (σ t) (φ t x)) (fderiv ℝ (φ t) x v) = 0 at ho
      simp only [pull1_apply, contract_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Pi.zero_apply, ContinuousLinearMap.zero_apply]
      change deriv σ t * bundleForm b (φ t x) (W (σ t) (φ t x))
        (fderiv ℝ (φ t) x v) = 0
      rw [ho, mul_zero]) 1
  ext x v w
  have hp := congrArg (fun A : Form2 E => A x v w) hkey
  simpa only [pull2_apply, φ, σ, SymplecticPacking.Return.sigT_one,
    SymplecticPacking.Return.sigT_zero, hW.flow_zero, bundleForm, VT.ddcForm,
    SymplecticPacking.Forms.d1, euclideanExteriorOneForm] using hp

end families

/-- A smooth global test family through a central point, with differential equal to
the identity on its central tangent space. Its range can be confined to any prescribed
neighbourhood. The normal chart is used only in this proof. -/
theorem exists_central_retraction {a : Fin q → ℂ} (ha : Function.Injective a)
    (ha0 : ∀ j, a j ≠ 0) {y : Tot q} (hy : equations a y.1 = 0)
    {U : Set (Tot q)} (hU : U ∈ 𝓝 y) :
    ∃ r : Tot q → Tot q, ContDiff ℝ ∞ r ∧ (∀ x, r x ∈ U) ∧
      (∀ x, equations a (r x).1 = 0) ∧ r y = y ∧
      ∀ v : Tot q, jacobian y.1 v.1 = 0 → fderiv ℝ r y v = v := by
  obtain ⟨e, hey⟩ := exists_normalChart_at ha ha0 (⟨y.1, hy⟩ : locus a)
  let C : Tot q →L[ℝ] ℂ := ((curveCoordinate e.coordinate).restrictScalars ℝ).comp
    (ContinuousLinearMap.fst ℝ (Affine q) (Fin q → ℂ))
  let P : Tot q → Affine q := fun x => (C x, 0)
  let R : Tot q → Tot q := fun x => (e.ambient.symm (P x), x.2)
  have hP : ContDiff ℝ ∞ P := C.contDiff.prodMk contDiff_const
  have hPy : P y = e.ambient y.1 := by
    rw [NormalChart.ambient_apply, hy]
    rfl
  have hPyT : P y ∈ e.ambient.target := by
    rw [hPy]
    exact e.ambient.map_source hey
  have hRy : R y = y := by
    simp only [R, hPy, e.ambient.left_inv hey, Prod.mk.eta]
  have hR (x : Tot q) (hx : P x ∈ e.ambient.target) : ContDiffAt ℝ ∞ R x := by
    have hi := (e.smooth_inverse.contDiffAt (e.ambient.open_target.mem_nhds hx)).restrict_scalars ℝ
    exact (hi.comp x hP.contDiffAt).prodMk contDiffAt_snd
  have hV : ({x | P x ∈ e.ambient.target} ∩ R ⁻¹' U) ∈ 𝓝 y := by
    apply inter_mem
    · exact hP.continuous.continuousAt.preimage_mem_nhds (e.ambient.open_target.mem_nhds hPyT)
    · exact (hR y hPyT).continuousAt.preimage_mem_nhds (by simpa only [hRy] using hU)
  obtain ⟨s, hs, hsV, hse⟩ := exists_smooth_local_identity hV
  let r : Tot q → Tot q := R ∘ s
  have hr : ContDiff ℝ ∞ r := contDiff_iff_contDiffAt.mpr fun x =>
    (hR (s x) (hsV x).1).comp x hs.contDiffAt
  have hre : r =ᶠ[𝓝 y] R := by
    filter_upwards [hse] with x hx
    simp only [r, Function.comp_apply, hx, id_eq]
  refine ⟨r, hr, fun x => (hsV x).2, fun x => ?_, ?_, ?_⟩
  · exact e.inverse_on_slice (hsV x).1
  · exact hre.self_of_nhds.trans hRy
  · intro v hv
    rw [hre.fderiv_eq]
    have hi : DifferentiableAt ℝ (e.ambient.symm : Affine q → Affine q) (P y) :=
      (e.smooth_inverse.contDiffAt (e.ambient.open_target.mem_nhds hPyT)).restrict_scalars ℝ
        |>.differentiableAt (by simp)
    have hPC : HasFDerivAt P (C.prod 0) y := C.hasFDerivAt.prodMk (hasFDerivAt_const 0 y)
    have hDR := (hi.hasFDerivAt.comp y hPC).prodMk (hasFDerivAt_snd (p := y))
    have hnorm := (normalCoordinates_hasFDerivAt a e.coordinate y.1).restrictScalars ℝ
    have hi' : DifferentiableAt ℝ (e.ambient.symm : Affine q → Affine q)
        (normalCoordinates a e.coordinate y.1) := by
      simpa only [hPy, e.coe_eq] using hi
    have hcomp := hi'.hasFDerivAt.comp y.1 hnorm
    have hid : (fun z => e.ambient.symm (normalCoordinates a e.coordinate z)) =ᶠ[𝓝 y.1] id := by
      filter_upwards [e.ambient.open_source.mem_nhds hey] with z hz
      simpa only [e.coe_eq, id_eq] using e.ambient.left_inv hz
    have hder := hid.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (e.ambient.symm ∘ normalCoordinates a e.coordinate) y.1 =
      fderiv ℝ id y.1 at hder
    rw [fderiv_id, hcomp.fderiv] at hder
    have hleft := congrArg (fun L : Affine q →L[ℝ] Affine q => L v.1) hder
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, hv] at hleft
    change fderiv ℝ (fun x : Tot q => ((e.ambient.symm ∘ P) x, x.2)) y v = v
    rw [hDR.fderiv]
    apply Prod.ext
    · change fderiv ℝ (e.ambient.symm : Affine q → Affine q) (P y) (C v, 0) = v.1
      simpa only [hPy, e.coe_eq, C, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_fst'] using hleft
    · rfl

theorem transport_form_of_control {a : Fin q → ℂ} (ha : Function.Injective a)
    (ha0 : ∀ j, a j ≠ 0) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {y : Tot q} (hy0 : equations a y.1 = 0)
    {W : ℝ → Tot q → Tot q} {O : Set (Tot q)} (hW : CSField W) (hO : IsOpen O)
    (hOg : O ⊆ goodSet q) (hVW : AgreesOn (transportField a b) W O)
    (hy : StaysIn W O y) (u v : Tot q)
    (hu : jacobian y.1 u.1 = 0) (hv : jacobian y.1 v.1 = 0) :
    (fderiv ℝ (transport a b) y u).2 =
        jacobian (transport a b y).1 (fderiv ℝ (transport a b) y u).1 ∧
      bundleForm b (transport a b y) (fderiv ℝ (transport a b) y u)
        (fderiv ℝ (transport a b) y v) = bundleForm b y u v := by
  obtain ⟨r, hr, hstays, hr0, hry, hdr⟩ := exists_central_retraction ha ha0 hy0
    (staysIn_eventually hW hO hy)
  let F : Tot q → Tot q := fun x => flow W 1 (r x)
  have hF : ContDiff ℝ ∞ F := (hW.flow_slice_smooth 1).comp hr
  have hτ : transport a b =ᶠ[𝓝 y] (fun x => flow W 1 x) := by
    filter_upwards [staysIn_eventually hW hO hy] with x hx
    exact flowI_one_eq_flow hW hO hVW hx
  have hτd := hτ.fderiv_eq (𝕜 := ℝ)
  have hτy := hτ.self_of_nhds
  have hFy : F y = transport a b y := by
    exact (congrArg (flow W 1) hry).trans hτy.symm
  have hFd (w : Tot q) (hw : jacobian y.1 w.1 = 0) :
      fderiv ℝ F y w = fderiv ℝ (transport a b) y w := by
    rw [show F = (flow W 1) ∘ r from rfl,
      fderiv_comp y ((hW.flow_slice_smooth 1).differentiable (by simp) _) (hr.differentiable (by simp) y)]
    rw [ContinuousLinearMap.comp_apply, hry, hdr w hw, hτd]
  have hFgraph (x : Tot q) : equations a (F x).1 = (F x).2 := by
    have hh := graph_along_trajectory a hb0 hb (γ := fun s => flow W s (r x))
      (by rw [hW.flow_zero]; exact hr0 x) (fun s hs => hOg (hstays x s hs)) (by
        intro s hs
        rw [hVW s hs _ (hstays x s hs)]
        exact (hW.flow_hasDerivAt (r x) s).hasDerivWithinAt) (s := 1) ⟨by norm_num, le_rfl⟩
    simpa only [Complex.ofReal_one, one_smul] using hh
  have ht := tangent_of_graph (hF.differentiable (by simp) y)
    (a := a) (s := 1) (by simpa only [Complex.ofReal_one, one_smul] using hFgraph) u
  have hforms := transport_family_pullback a hb0 hb hW hOg hVW hr hr0 hstays
  have he := congrArg (fun A : Form2 (Tot q) => A y u v) hforms
  simp only [pull2_apply] at he
  change bundleForm b (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) =
    bundleForm b (r y) (fderiv ℝ r y u) (fderiv ℝ r y v) at he
  rw [hFy, hFd u hu, hFd v hv, hry, hdr u hu, hdr v hv] at he
  rw [hFy, hFd u hu, Complex.ofReal_one, one_smul] at ht
  exact ⟨(sub_eq_zero.mp ht).symm, he⟩

theorem transport_form_all (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2)))
    (hx1 : x.1 ∈ locus (parameters m)) (hx2 : Real.pi * wsq (toC x.2) < b)
    (u v : Tot (m + 2))
    (hu : jacobian (radialInj b x.1 (toC x.2)).1 u.1 = 0)
    (hv : jacobian (radialInj b x.1 (toC x.2)).1 v.1 = 0) :
    (fderiv ℝ (transport (parameters m) b) (radialInj b x.1 (toC x.2)) u).2 =
        jacobian (transport (parameters m) b (radialInj b x.1 (toC x.2))).1
          (fderiv ℝ (transport (parameters m) b) (radialInj b x.1 (toC x.2)) u).1 ∧
      bundleForm b (transport (parameters m) b (radialInj b x.1 (toC x.2)))
          (fderiv ℝ (transport (parameters m) b) (radialInj b x.1 (toC x.2)) u)
          (fderiv ℝ (transport (parameters m) b) (radialInj b x.1 (toC x.2)) v) =
        bundleForm b (radialInj b x.1 (toC x.2)) u v := by
  obtain ⟨γ, hγ0, hγO, hγ⟩ := transport_trajectory m hb0 hb x hx1 hx2
  obtain ⟨W, O, hW, hO, hOg, hVW, hy⟩ := localControl_within_of_contDiffOn
    (isOpen_goodSet (m + 2)) (transportField_contDiffOn (parameters m) hb0 hb) hγ0 hγO hγ
  have hx0 : equations (parameters m) x.1 = 0 := by
    simpa only [locus, Set.mem_preimage, Set.mem_singleton_iff] using hx1
  exact transport_form_of_control (parameters_injective m).out (parameters_nonzero m).out
    (y := radialInj b x.1 (toC x.2)) hb0 hb
    (by simpa only [radialInj_fst] using hx0) hW hO hOg hVW hy u v hu hv

end SymplecticPacking.BranchSmall.VT
