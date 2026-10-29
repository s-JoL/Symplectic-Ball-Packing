import SymplecticPacking.HighDim.Comparator.PlanarJointIntegral
import SymplecticPacking.HighDim.Comparator.PlanarDensityExtension

/-!
# Density normalization with arbitrary finite-dimensional parameters

The density may have a parameter-dependent positive constant germ.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen.JointDensity

open Set Filter Topology Complex
open scoped ContDiff Real

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def family (J : P → ℂ → ℝ) (p : P) : ℝ → ℂ → ℝ := fun _ => J p

structure Hyp (J : P → ℂ → ℝ) (j : P → ℝ) (U : Set P) (ρ : ℝ) : Prop where
  openU : IsOpen U
  smooth : ContDiffOn ℝ ∞ (Function.uncurry J) (U ×ˢ univ)
  j_smooth : ContDiffOn ℝ ∞ j U
  pos : ∀ p ∈ U, ∀ w, 0 < J p w
  flat : ∀ p ∈ U, ∀ w, ‖w‖ ≤ ρ → J p w = j p
  j_pos : ∀ p ∈ U, 0 < j p
  ρ_pos : 0 < ρ
  proper : ∀ p ∈ U, Tendsto (Inner.Acal (family J p) 0) atTop atTop

variable {J : P → ℂ → ℝ} {j : P → ℝ} {U : Set P} {ρ : ℝ} (H : Hyp J j U ρ)
include H

lemma slice_smooth {p : P} (hp : p ∈ U) : ContDiff ℝ ∞ (J p) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  exact (H.smooth.contDiffAt ((H.openU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp w
    (contDiffAt_const.prodMk contDiffAt_id)

lemma scalar_hyp {p : P} (hp : p ∈ U) : Inner.FlatDensity (family J p) (-1) 2 (j p) ρ where
  smooth := ((slice_smooth H) hp).comp contDiff_snd
  pos := fun _ _ => H.pos p hp
  flat := fun _ _ => H.flat p hp
  j_pos := H.j_pos p hp
  ρ₀_pos := H.ρ_pos
  tendsto := fun _ _ => H.proper p hp

lemma jcirc_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ => Inner.Jcirc (family J q.1) 0 q.2) (U ×ˢ univ) := by
  intro q hq
  simp_rw [Inner.Jcirc_eq_unit]
  apply ContDiffAt.contDiffWithinAt
  apply fixed_integral_at (H.openU.prod isOpen_univ) (p₀ := q) (hp₀ := hq)
    (f := fun r : ℝ × (P × ℂ) => J r.2.1 (Inner.Rot (2 * Real.pi * r.1) r.2.2))
  intro r hr
  have hJ : ContDiffAt ℝ ∞ (Function.uncurry J)
      (r.2.1, Inner.Rot (2 * Real.pi * r.1) r.2.2) :=
    H.smooth.contDiffAt ((H.openU.prod isOpen_univ).mem_nhds ⟨hr.1, mem_univ _⟩)
  exact (hJ.comp r (contDiffAt_snd.fst.prodMk
    (Inner.contDiff_Rot.contDiffAt.comp r
      ((contDiffAt_const.mul contDiffAt_fst).prodMk contDiffAt_snd.snd)))).contDiffWithinAt

lemma bfun_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ => Inner.Bfun (family J q.1) 0 q.2) (U ×ˢ univ) := by
  intro q hq
  simp_rw [Inner.Bfun_eq_unit]
  apply ContDiffAt.contDiffWithinAt
  apply fixed_integral_at (H.openU.prod isOpen_univ) (p₀ := q) (hp₀ := hq)
    (f := fun r : ℝ × (P × ℂ) => (2 * Real.pi * r.1 - Real.pi) * J r.2.1 (Inner.Rot (2 * Real.pi * r.1) r.2.2))
  intro r hr
  have hJ : ContDiffAt ℝ ∞ (Function.uncurry J)
      (r.2.1, Inner.Rot (2 * Real.pi * r.1) r.2.2) :=
    H.smooth.contDiffAt ((H.openU.prod isOpen_univ).mem_nhds ⟨hr.1, mem_univ _⟩)
  exact ((contDiffAt_const.mul contDiffAt_fst |>.sub contDiffAt_const).mul
    (hJ.comp r (contDiffAt_snd.fst.prodMk (Inner.contDiff_Rot.contDiffAt.comp r
      ((contDiffAt_const.mul contDiffAt_fst).prodMk contDiffAt_snd.snd))))).contDiffWithinAt

lemma jbar_at {p : P} (hp : p ∈ U) (E : ℝ) :
    ContDiffAt ℝ ∞ (fun q : P × ℝ => Inner.Jbar (family J q.1) 0 q.2) (p, E) := by
  by_cases hE : 0 < E
  · have h1 : ContDiffAt ℝ ∞ (fun q : P × ℝ => (Real.sqrt q.2 : ℂ)) (p, E) :=
      ofRealCLM.contDiff.contDiffAt.comp (p, E)
        ((Real.contDiffAt_sqrt hE.ne').comp (p, E) contDiffAt_snd)
    exact ((jcirc_smooth H).contDiffAt ((H.openU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp
      (p, E) (contDiffAt_fst.prodMk h1)
  · have hρ : 0 < ρ ^ 2 := sq_pos_of_pos H.ρ_pos
    have hnear : ∀ᶠ q : P × ℝ in 𝓝 (p, E), q.1 ∈ U ∧ q.2 < ρ ^ 2 :=
      (H.openU.prod isOpen_Iio).mem_nhds ⟨hp, show E < ρ ^ 2 by linarith [not_lt.mp hE]⟩
    have hj := (H.j_smooth.contDiffAt (H.openU.mem_nhds hp)).comp (p, E) contDiffAt_fst
    apply hj.congr_of_eventuallyEq
    filter_upwards [hnear] with q hq
    exact Inner.Jbar_eq_of_le (H.flat q.1 hq.1) hq.2.le H.ρ_pos.le

lemma acal_smooth : ContDiffOn ℝ ∞ (fun q : P × ℝ => Inner.Acal (family J q.1) 0 q.2) (U ×ˢ univ) := by
  intro q hq
  simp_rw [Inner.Acal_eq_unit]
  apply ContDiffAt.contDiffWithinAt
  have hi : ContDiffAt ℝ ∞ (fun q : P × ℝ => ∫ t in (0 : ℝ)..1,
      Inner.Jbar (family J q.1) 0 (q.2 * t)) q := by
    apply fixed_integral_at (H.openU.prod isOpen_univ) (hp₀ := hq)
      (f := fun r : ℝ × (P × ℝ) => Inner.Jbar (family J r.2.1) 0 (r.2.2 * r.1))
    intro r hr
    exact (((jbar_at H) hr.1 (r.2.2 * r.1)).comp r
      (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.mul contDiffAt_fst))).contDiffWithinAt
  exact contDiffAt_const.mul (contDiffAt_snd.mul hi)

lemma einv_smooth : ContDiffOn ℝ ∞ (fun q : P × ℝ => Inner.Einv (family J q.1) 0 q.2) (U ×ˢ univ) := by
  apply invR_joint_smooth (G := fun p E => Inner.Acal (family J p) 0 E) H.openU
  · intro p hp E
    exact (acal_smooth H).contDiffAt ((H.openU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  · intro p hp
    exact (Inner.Acal_strictMono ((scalar_hyp H) hp) (by constructor <;> norm_num)).injective
  · intro p hp
    exact (Inner.Acal_bijective ((scalar_hyp H) hp) (by constructor <;> norm_num)).2
  · intro p hp E
    rw [(Inner.Acal_hasDerivAt ((scalar_hyp H) hp) (by constructor <;> norm_num) E).deriv]
    exact (Inner.Acal_deriv_pos ((scalar_hyp H) hp) (by constructor <;> norm_num) E).ne'

lemma trot_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ => Inner.Trot (family J q.1) 0 q.2) (U ×ˢ univ) := by
  simp_rw [Inner.Trot_eq]
  intro q hq
  have hc := (jcirc_smooth H).contDiffAt ((H.openU.prod isOpen_univ).mem_nhds hq)
  have hb := (bfun_smooth H).contDiffAt ((H.openU.prod isOpen_univ).mem_nhds hq)
  have hpos : 0 < Inner.Jcirc (family J q.1) 0 q.2 :=
    Inner.Jcirc_pos ((slice_smooth H) hq.1).continuous (H.pos q.1 hq.1) q.2
  have hh := Inner.contDiff_Rot.contDiffAt.comp q ((hb.div hc hpos.ne').prodMk contDiffAt_snd)
  exact hh.contDiffWithinAt

lemma trotInv_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ => Inner.TrotInv (family J q.1) 0 q.2) (U ×ˢ univ) := by
  apply param_inverse_smooth (G := fun p w => Inner.Trot (family J p) 0 w)
    (inv := fun p w => Inner.TrotInv (family J p) 0 w) H.openU (trot_smooth H)
  · intro p hp
    exact (Inner.Trot_bijective ((slice_smooth H) hp).continuous (H.pos p hp)).1
  · intro p hp w
    apply Inner.injective_of_det_ne_zero
    rw [Inner.Trot_det ((scalar_hyp H) hp).smooth (H.pos p hp)]
    exact (div_pos (H.pos p hp w) (Inner.Jbar_pos ((slice_smooth H) hp).continuous (H.pos p hp) _)).ne'
  · intro p hp w
    exact Inner.Trot_TrotInv ((scalar_hyp H) hp) (by constructor <;> norm_num) w

lemma darea_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ => Inner.Darea (family J q.1) 0 q.2) (U ×ˢ univ) := by
  rintro ⟨p, z⟩ ⟨hp, _⟩
  apply ContDiffAt.contDiffWithinAt
  have hj := (H.j_smooth.contDiffAt (H.openU.mem_nhds hp)).comp (p, z) contDiffAt_fst
  by_cases hz : z = 0
  · have hsqrt := (Real.contDiffAt_sqrt (H.j_pos p hp).ne').comp (p, z) hj
    have hbound : 0 < Real.sqrt (j p) * ρ := mul_pos (Real.sqrt_pos.mpr (H.j_pos p hp)) H.ρ_pos
    have hnear : ∀ᶠ q : P × ℂ in 𝓝 (p, z), q.1 ∈ U ∧ ‖q.2‖ < Real.sqrt (j q.1) * ρ := by
      have hnorm : ContinuousAt (fun q : P × ℂ => ‖q.2‖) (p, z) := continuous_norm.continuousAt.comp continuous_snd.continuousAt
      have hrhs : ContinuousAt (fun q : P × ℂ => Real.sqrt (j q.1) * ρ) (p, z) :=
        hsqrt.continuousAt.mul continuousAt_const
      exact ((continuous_fst.tendsto (p, z)).eventually (H.openU.mem_nhds hp)).and
        (hnorm.eventually_lt hrhs (by simpa only [hz, norm_zero] using hbound))
    have hcast : ContDiffAt ℝ ∞ (fun q : P × ℂ => (Real.sqrt (j q.1) : ℂ)) (p, z) :=
      ofRealCLM.contDiff.contDiffAt.comp (p, z) hsqrt
    have hd : ContDiffAt ℝ ∞ (fun q : P × ℂ => q.2 / (Real.sqrt (j q.1) : ℂ)) (p, z) :=
      contDiffAt_snd.mul (hcast.inv
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (H.j_pos p hp)).ne'))
    apply hd.congr_of_eventuallyEq
    filter_upwards [hnear] with q hq
    exact Inner.Darea_eq_of_const ((scalar_hyp H) hq.1) (by constructor <;> norm_num) hq.2.le
  · have hI : 0 < Real.pi * ‖z‖ ^ 2 := by have := norm_pos_iff.mpr hz; positivity
    have hn : ContDiffAt ℝ ∞ (fun q : P × ℂ => Real.pi * ‖q.2‖ ^ 2) (p, z) :=
      contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (p, z) contDiffAt_snd)
    have hE0 : ContDiffAt ℝ ∞ (fun q : P × ℝ => Inner.Einv (family J q.1) 0 q.2)
        (p, Real.pi * ‖z‖ ^ 2) := (einv_smooth H).contDiffAt ((H.openU.prod isOpen_univ).mem_nhds
      (show (p, Real.pi * ‖z‖ ^ 2) ∈ U ×ˢ (univ : Set ℝ) from ⟨hp, mem_univ _⟩))
    have hE : ContDiffAt ℝ ∞ (fun q : P × ℂ => Inner.Einv (family J q.1) 0 (Real.pi * ‖q.2‖ ^ 2)) (p, z) :=
      ContDiffAt.comp (p, z) (g := fun q : P × ℝ => Inner.Einv (family J q.1) 0 q.2)
        (f := fun q : P × ℂ => (q.1, Real.pi * ‖q.2‖ ^ 2)) hE0 (contDiffAt_fst.prodMk hn)
    have hratio : ContDiffAt ℝ ∞ (fun q : P × ℂ => Real.pi *
        Inner.Einv (family J q.1) 0 (Real.pi * ‖q.2‖ ^ 2) / (Real.pi * ‖q.2‖ ^ 2)) (p, z) :=
      (contDiffAt_const.mul hE).div hn hI.ne'
    have hpos : 0 < Real.pi * Inner.Einv (family J p) 0 (Real.pi * ‖z‖ ^ 2) / (Real.pi * ‖z‖ ^ 2) :=
      div_pos (mul_pos Real.pi_pos (Inner.Einv_pos ((scalar_hyp H) hp) (by constructor <;> norm_num) hI)) hI
    have hroot := (Real.contDiffAt_sqrt hpos.ne').comp (p, z) hratio
    exact (ofRealCLM.contDiff.contDiffAt.comp (p, z) hroot).mul contDiffAt_snd

/-- The complete inverse normalization is jointly smooth, including the zero section. -/
theorem normalize_smooth : ContDiffOn ℝ ∞ (fun q : P × ℂ =>
    Inner.TrotInv (family J q.1) 0 (Inner.Darea (family J q.1) 0 q.2)) (U ×ˢ univ) :=
  (trotInv_smooth H).comp (contDiffOn_fst.prodMk (darea_smooth H)) (fun q hq => ⟨hq.1, mem_univ _⟩)

end SymplecticPacking.HighDim.PlanarGen.JointDensity
