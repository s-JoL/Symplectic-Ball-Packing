import OAI.Geometry.BallPacking.BallMaps.CubicBubbleSeparated
import OAI.Geometry.BallPacking.Annuli.AnnularMean

/-!
# The relative radial Poincaré formula

A closed one-form on a fibrewise star shaped neighbourhood is recovered by
integrating its vertical component, provided its restriction to the zero section
vanishes. Localized parameter differentiation keeps the statement local.
-/

noncomputable section
namespace SymplecticPacking.BranchLargeHigh.Two

open Set Filter Topology MeasureTheory ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

section integral
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem hasFDerivAt_integral_near_segment {W : Set (ℝ × P)} (hW : IsOpen W)
    {f : ℝ × P → ℝ} (hf : ContDiffOn ℝ ∞ f W) {p : P}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, (t, p) ∈ W) :
    HasFDerivAt (fun q => ∫ t in (0 : ℝ)..1, f (t, q))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q => f (t, q)) p) p := by
  let K := Icc (0 : ℝ) 1 ×ˢ ({p} : Set P)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKW : K ⊆ W := by rintro ⟨t, q⟩ ⟨ht, rfl⟩; exact hp t ht
  obtain ⟨χ, _, _, _, _, _, hg, _, hge⟩ := exists_smooth_compact_extension hK hW hKW hf
  let g : ℝ × P → ℝ := fun z => χ z * f z
  have hg : ContDiff ℝ ∞ g := hg
  obtain ⟨O, hO, hKO, hOg⟩ := mem_nhdsSet_iff_exists.mp hge
  obtain ⟨u, v, _, hv, hIu, hpv, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hO hKO
  have hpv : p ∈ v := hpv (mem_singleton p)
  have hval : (fun q => ∫ t in (0 : ℝ)..1, f (t, q)) =ᶠ[𝓝 p]
      fun q => ∫ t in (0 : ℝ)..1, g (t, q) := by
    filter_upwards [hv.mem_nhds hpv] with q hq
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hOg (huv ⟨hIu ht, hq⟩)).symm
  have hD : (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q => g (t, q)) p) =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun q => f (t, q)) p := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hnear : (fun q => g (t, q)) =ᶠ[𝓝 p] fun q => f (t, q) := by
      filter_upwards [hv.mem_nhds hpv] with q hq
      exact hOg (huv ⟨hIu ht, hq⟩)
    exact hnear.fderiv_eq
  exact ((hasFDerivAt_fixed_integral hg p).congr_of_eventuallyEq hval).congr_fderiv hD

theorem continuousOn_fderiv_slice {W : Set (ℝ × P)} (hW : IsOpen W)
    {f : ℝ × P → ℝ} (hf : ContDiffOn ℝ ∞ f W) {p : P}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, (t, p) ∈ W) :
    ContinuousOn (fun t => fderiv ℝ (fun q => f (t, q)) p) (Icc (0 : ℝ) 1) := by
  have hd : ContinuousOn (fun t => (fderiv ℝ f (t, p)).comp (ContinuousLinearMap.inr ℝ ℝ P))
      (Icc (0 : ℝ) 1) :=
    (((hf.fderiv_of_isOpen (m := ∞) hW (by simp)).continuousOn.comp
      ((continuous_id.prodMk continuous_const).continuousOn) hp).clm_comp continuousOn_const)
  apply hd.congr
  intro t ht
  have hin : HasFDerivAt (fun q : P => (t, q)) (ContinuousLinearMap.inr ℝ ℝ P) p := by
    convert! (hasFDerivAt_const t p).prodMk (hasFDerivAt_id p) using 1
  exact ((hf.contDiffAt (hW.mem_nhds (hp t ht))).differentiableAt (by simp)
    |>.hasFDerivAt.comp p hin).fderiv

end integral

section radial
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fibreScale (t : ℝ) : (E × F) →L[ℝ] (E × F) :=
  (ContinuousLinearMap.fst ℝ E F).prod (t • ContinuousLinearMap.snd ℝ E F)

def fibreRadial : (E × F) →L[ℝ] (E × F) :=
  (0 : (E × F) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E F)

@[simp] theorem fibreScale_apply (t : ℝ) (p : E × F) : fibreScale t p = (p.1, t • p.2) := rfl
@[simp] theorem fibreRadial_apply (p : E × F) : fibreRadial p = (0, p.2) := rfl

def fibreRadialPotential (β : (E × F) → (E × F) →L[ℝ] ℝ) (p : E × F) : ℝ :=
  ∫ t in (0 : ℝ)..1, β (fibreScale t p) (fibreRadial p)

theorem fibreRadialIntegrand_hasFDerivAt {β : (E × F) → (E × F) →L[ℝ] ℝ}
    (t : ℝ) (p : E × F) (hβ : DifferentiableAt ℝ β (fibreScale t p)) :
    HasFDerivAt (fun q => β (fibreScale t q) (fibreRadial q))
      (((fderiv ℝ β (fibreScale t p)).flip (fibreRadial p)).comp (fibreScale t) +
        (β (fibreScale t p)).comp fibreRadial) p := by
  have hd := (hβ.hasFDerivAt.comp p (fibreScale (E := E) (F := F) t).hasFDerivAt).clm_apply (fibreRadial (E := E) (F := F)).hasFDerivAt
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change β (fibreScale t p) (fibreRadial v) +
    fderiv ℝ β (fibreScale t p) (fibreScale t v) (fibreRadial p) = _
  simp only [add_apply, ContinuousLinearMap.comp_apply, flip_apply]
  ring

set_option maxHeartbeats 800000 in
theorem fibreRadialPotential_hasFDerivAt [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {O : Set (E × F)} (hO : IsOpen O)
    {β : (E × F) → (E × F) →L[ℝ] ℝ} (hβ : ContDiffOn ℝ ∞ β O)
    (hclosed : ∀ z ∈ O, euclideanExteriorOneForm β z = 0)
    (p : E × F) (hp : ∀ t ∈ Icc (0 : ℝ) 1, fibreScale t p ∈ O)
    (hzero : ∀ a : E, β (p.1, 0) (a, 0) = 0) :
    HasFDerivAt (fibreRadialPotential β) (β p) p := by
  let H : ℝ × (E × F) → E × F := fun z => fibreScale z.1 z.2
  have hH : ContDiff ℝ ∞ H :=
    contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd)
  let G : ℝ × (E × F) → ℝ := fun z => β (H z) (fibreRadial z.2)
  have hW : IsOpen (H ⁻¹' O) := hO.preimage hH.continuous
  have hG : ContDiffOn ℝ ∞ G (H ⁻¹' O) :=
    (hβ.comp hH.contDiffOn (fun _ hz => hz)).clm_apply
      ((fibreRadial (E := E) (F := F)).contDiff.comp contDiff_snd).contDiffOn
  have hpW : ∀ t ∈ Icc (0 : ℝ) 1, (t, p) ∈ H ⁻¹' O := hp
  have hDcont := continuousOn_fderiv_slice hW hG hpW
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun q => G (t, q)) p) volume 0 1 :=
    hDcont.intervalIntegrable_of_Icc zero_le_one
  have hstrand (v : E × F) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => β (fibreScale s p) (fibreScale s v))
        (fderiv ℝ (fun q => G (t, q)) p v) t := by
    have hb := (hβ.contDiffAt (hO.mem_nhds (hp t ht))).differentiableAt (by simp)
    have hHp : HasDerivAt (fun s => fibreScale s p) (fibreRadial p) t := by
      simpa only [fibreScale_apply, fibreRadial_apply, one_smul, id_eq] using
        (hasDerivAt_const t p.1).prodMk ((hasDerivAt_id t).smul_const p.2)
    have hHv : HasDerivAt (fun s => fibreScale s v) (fibreRadial v) t := by
      simpa only [fibreScale_apply, fibreRadial_apply, one_smul, id_eq] using
        (hasDerivAt_const t v.1).prodMk ((hasDerivAt_id t).smul_const v.2)
    have hd := (hb.hasFDerivAt.comp_hasDerivAt t hHp).clm_apply hHv
    have hsym : fderiv ℝ β (fibreScale t p) (fibreRadial p) (fibreScale t v) =
        fderiv ℝ β (fibreScale t p) (fibreScale t v) (fibreRadial p) := by
      have hh := congrArg (fun L : (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ =>
        L (fibreRadial p) (fibreScale t v)) (hclosed _ (hp t ht))
      simpa only [euclideanExteriorOneForm, sub_apply, flip_apply, zero_apply, sub_eq_zero] using hh
    apply hd.congr_deriv
    change _ = fderiv ℝ (fun q => β (fibreScale t q) (fibreRadial q)) p v
    rw [(fibreRadialIntegrand_hasFDerivAt t p hb).fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, flip_apply]
    rw [hsym]
    rfl
  have he : (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q => G (t, q)) p) = β p := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.intervalIntegral_apply hint]
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hstrand v t (by simpa only [uIcc_of_le zero_le_one] using ht))
      ((hDcont.clm_apply continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
    simpa only [fibreScale_apply, one_smul, zero_smul, hzero, sub_zero, Prod.mk.eta] using hi
  exact (hasFDerivAt_integral_near_segment hW hG hpW).congr_fderiv he

end radial
end SymplecticPacking.BranchLargeHigh.Two
