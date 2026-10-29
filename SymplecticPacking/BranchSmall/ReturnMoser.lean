import SymplecticPacking.BranchSmall.ReturnControl
import SymplecticPacking.Forms.Cartan
import OAI.Geometry.BallPacking.Annuli.AnnularMean

/-!
# Moser transport for the interval flow

Local exact Moser transport for the interval flow.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open SymplecticPacking.Forms
open SymplecticPacking.Return (CSField flow sigT)
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

section localMoser

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- An exact Moser equation on `[0,1]`, together with local control of the field,
gives the endpoint pullback at the controlled initial point. Cutoffs occur only in this
proof; the map in the conclusion is the originally defined interval flow. -/
theorem localControl_affine_moser {α β : Form1 E}
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) {V : ℝ → E → E} {y : E}
    (hc : LocalControl V y)
    (heq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z,
      d1 (fun x => α x + s • β x) z (V s z) = -β z) (v w : E) :
    d1 (fun x => α x + β x) (flowI V 0 y 1)
      (fderiv ℝ (fun x => flowI V 0 x 1) y v)
      (fderiv ℝ (fun x => flowI V 0 x 1) y w) = d1 α y v w := by
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := hc
  obtain ⟨r, hr, hrange, hre⟩ := exists_smooth_local_identity (staysIn_eventually hW hO hy)
  let σ : ℝ → ℝ := sigT 1
  let φ : ℝ → E → E := fun t x => flow W (σ t) (r x)
  let Λ : ℝ → Form1 E := fun t x => α x + σ t • β x
  have hσ (t : ℝ) : σ t ∈ Icc (0 : ℝ) 1 := SymplecticPacking.Return.sigT_mem (by norm_num) t
  have hΛ : ContDiff ℝ ∞ (fun p : ℝ × E => Λ p.1 p.2) :=
    (hα.comp contDiff_snd).add
      (((SymplecticPacking.Return.sigT_contDiff 1).comp contDiff_fst).smul (hβ.comp contDiff_snd))
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2) := hW.family_smooth 1 hr
  have hvelocity : ∀ t x, HasDerivAt (fun s => φ s x)
      (deriv σ t • W (σ t) (φ t x)) t := hW.family_hasDerivAt 1 r
  have hzero : ∀ t, pull1 (φ t)
      (contract (fun z => deriv σ t • W (σ t) z) (d1 (Λ t)) + dtForm Λ t) = 0 := by
    intro t
    funext x
    apply ContinuousLinearMap.ext
    intro u
    have hin : φ t x ∈ O := hrange x (σ t) (hσ t)
    have hcon := congrArg (fun L : E →L[ℝ] ℝ => L (fderiv ℝ (φ t) x u))
      (heq (σ t) (hσ t) (φ t x))
    rw [hVW (σ t) (hσ t) (φ t x) hin] at hcon
    have hd : HasDerivAt (fun s => Λ s (φ t x)) (deriv σ t • β (φ t x)) t :=
      ((SymplecticPacking.Return.sigT_hasDerivAt 1 t).smul_const (β (φ t x))).const_add _
    simp only [pull1_apply, Pi.add_apply, ContinuousLinearMap.add_apply, contract_apply,
      dtForm, hd.deriv, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul,
      Pi.zero_apply, ContinuousLinearMap.zero_apply] 
    change deriv σ t * d1 (Λ t) (φ t x) (W (σ t) (φ t x)) (fderiv ℝ (φ t) x u) +
      deriv σ t * β (φ t x) (fderiv ℝ (φ t) x u) = 0
    change d1 (Λ t) (φ t x) (W (σ t) (φ t x)) (fderiv ℝ (φ t) x u) =
      -β (φ t x) (fderiv ℝ (φ t) x u) at hcon
    rw [hcon]
    ring
  have hkey := pull2_d1_const_of_dt_univ hΛ hφ hvelocity hzero 1
  have hkey' := congrArg (fun A : Form2 E => A y v w) hkey
  have hend : (fun x => flowI V 0 x 1) =ᶠ[𝓝 y] (fun x => flow W 1 (r x)) := by
    filter_upwards [staysIn_eventually hW hO hy, hre] with x hx hrx
    rw [flowI_one_eq_flow hW hO hVW hx, hrx]
    rfl
  have hry : r y = y := hre.self_of_nhds
  have hdr : fderiv ℝ r y = ContinuousLinearMap.id ℝ E := by
    rw [hre.fderiv_eq, fderiv_id]
  have hendd := hend.fderiv_eq (𝕜 := ℝ)
  have hendy := hend.self_of_nhds
  have hendy' : flowI V 0 y 1 = flow W 1 y := by simpa only [hry] using hendy
  simpa only [pull2_apply, φ, Λ, σ, SymplecticPacking.Return.sigT_one,
    SymplecticPacking.Return.sigT_zero, hW.flow_zero, zero_smul, one_smul, add_zero,
    hry, hdr, ContinuousLinearMap.id_apply, ← hendy', ← hendd] using hkey'

end localMoser

open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

theorem returnField_contraction (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : Affine (m + 2)) :
    ddcForm (returnPot (parameters m) b s) z (returnField (parameters m) b s z) =
      (-b) • dcForm (graphPot (parameters m)) z := by
  have hinj := returnForm_injective m hb0 hb hs z
  obtain ⟨e, he⟩ := exists_equiv_of_injective hinj
  have hex : ∃! Y : Affine (m + 2), ∀ v,
      ddcForm (returnPot (parameters m) b s) z Y v = -b * dcForm (graphPot (parameters m)) z v := by
    let c := (-b) • dcForm (graphPot (parameters m)) z
    refine ⟨e.symm c, ?_, ?_⟩
    · intro v
      have hh : ddcForm (returnPot (parameters m) b s) z (e.symm c) = c := by
        rw [← he]
        exact e.apply_symm_apply c
      exact congrArg (fun L : Affine (m + 2) →L[ℝ] ℝ => L v) hh
    · intro Y hY
      apply hinj
      have hh : ddcForm (returnPot (parameters m) b s) z Y = c :=
        ContinuousLinearMap.ext hY
      rw [hh, ← he]
      exact (e.apply_symm_apply c).symm
  unfold returnField
  rw [dif_pos hex]
  exact ContinuousLinearMap.ext (SymplecticPacking.Explicit.the_spec hex)

theorem returnPot_dc_affine {q : ℕ} (a : Fin q → ℂ) (b s : ℝ) :
    dcForm (returnPot a b s) = dcForm (fun z : Affine q => Real.log (1 + nsq z)) +
      (s * b) • dcForm (graphPot a) := by
  unfold returnPot
  rw [dcForm_add (fsPot_contDiff.differentiable (by simp))
    ((graphPot_contDiff a).differentiable (by simp) |>.const_mul (s * b)),
    dcForm_const_mul ((graphPot_contDiff a).differentiable (by simp))]

theorem return_reversed_primitive {q : ℕ} (a : Fin q → ℂ) (b s : ℝ) :
    (fun z => dcForm (returnPot a b 1) z + s • ((-b) • dcForm (graphPot a) z)) =
      dcForm (returnPot a b (1 - s)) := by
  rw [returnPot_dc_affine a b 1, returnPot_dc_affine a b (1 - s)]
  funext z
  apply ContinuousLinearMap.ext
  intro v
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Correctness of the reversed return flow at any controlled point. The only
global input is local control of that already defined field, supplied separately by
the trajectory/growth analysis. -/
theorem returnInv_form_of_control (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (z v w : Affine (m + 2))
    (hc : LocalControl (revField (returnField (parameters m) b)) z) :
    ddcForm (returnPot (parameters m) b 0) (returnInv (parameters m) b z)
      (fderiv ℝ (returnInv (parameters m) b) z v)
      (fderiv ℝ (returnInv (parameters m) b) z w) =
      ddcForm (returnPot (parameters m) b 1) z v w := by
  let α := dcForm (returnPot (parameters m) b 1)
  let β := fun z : Affine (m + 2) => (-b) • dcForm (graphPot (parameters m)) z
  have hα : ContDiff ℝ ∞ α := by
    apply dcForm_contDiff_of
    unfold returnPot
    exact fsPot_contDiff.add (contDiff_const.mul (graphPot_contDiff _))
  have hβ : ContDiff ℝ ∞ β := (dcForm_contDiff_of (graphPot_contDiff _)).const_smul (-b)
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      d1 (fun x => α x + s • β x) x (revField (returnField (parameters m) b) s x) = -β x := by
    intro s hs x
    rw [show (fun x => α x + s • β x) = dcForm (returnPot (parameters m) b (1 - s)) from
      return_reversed_primitive _ b s]
    change ddcForm (returnPot (parameters m) b (1 - s)) x
      (-returnField (parameters m) b (1 - s) x) = -β x
    rw [map_neg, returnField_contraction m hb0 hb ⟨by linarith [hs.2], by linarith [hs.1]⟩]
  have h := localControl_affine_moser hα hβ hc heq v w
  have hback : (fun x => flowI (revField (returnField (parameters m) b)) 0 x 1) =ᶠ[𝓝 z]
      returnInv (parameters m) b := by
    obtain ⟨W, O, hW, hO, hVW, hz⟩ := hc
    filter_upwards [staysIn_eventually hW hO hz] with x hx
    exact (flowI_one_eq_flow hW hO hVW hx).trans
      (flowI_back_eq_flow hW hO hVW hx).symm
  have hv := hback.fderiv_eq (𝕜 := ℝ)
  have hx := hback.self_of_nhds
  change flowI (revField (returnField (parameters m) b)) 0 z 1 =
    returnInv (parameters m) b z at hx
  have hform : (fun x => α x + β x) = dcForm (returnPot (parameters m) b 0) := by
    simpa only [one_smul, sub_self] using return_reversed_primitive (parameters m) b 1
  rw [hform, hx, hv] at h
  exact h

theorem returnInv_form_all (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (z v w : Affine (m + 2)) :
    ddcForm (returnPot (parameters m) b 0) (returnInv (parameters m) b z)
      (fderiv ℝ (returnInv (parameters m) b) z v)
      (fderiv ℝ (returnInv (parameters m) b) z w) =
      ddcForm (returnPot (parameters m) b 1) z v w :=
  returnInv_form_of_control m hb0 hb z v w (return_control_all m hb0 hb z)

end SymplecticPacking.BranchSmall.VT
