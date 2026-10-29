import SymplecticPacking.HighDim.Comparator.PlanarGen

/-!
# A proper auxiliary density agreeing on a prescribed energy disc

The construction is used only to prove locality of normalization. It leaves the
original planar generator unchanged.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen.DensityExtension

open Set Filter Topology Complex
open scoped ContDiff Real

set_option maxHeartbeats 800000

/-- Radial cutoff equal to one on the disc of radius `R` and zero outside radius `2R`. -/
def cut (R : ℝ) (w : ℂ) : ℝ :=
  1 - Real.smoothTransition ((w.re ^ 2 + w.im ^ 2 - R ^ 2) / (3 * R ^ 2))

/-- Positive constant tail joined smoothly to the original density. -/
def extend (J : ℝ → ℂ → ℝ) (j R : ℝ) (s : ℝ) (w : ℂ) : ℝ :=
  cut R w * J s w + (1 - cut R w) * j

lemma cut_range (R : ℝ) (w : ℂ) : 0 ≤ cut R w ∧ cut R w ≤ 1 := by
  unfold cut
  constructor <;> linarith [Real.smoothTransition.nonneg ((w.re ^ 2 + w.im ^ 2 - R ^ 2) / (3 * R ^ 2)),
    Real.smoothTransition.le_one ((w.re ^ 2 + w.im ^ 2 - R ^ 2) / (3 * R ^ 2))]

lemma cut_smooth (R : ℝ) : ContDiff ℝ ∞ (cut R) := by
  unfold cut
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)).sub contDiff_const |>.div_const _))

lemma cut_one {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ ≤ R) : cut R w = 1 := by
  have hs : w.re ^ 2 + w.im ^ 2 ≤ R ^ 2 := by
    rw [show w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 by simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm w).symm]
    exact pow_le_pow_left₀ (norm_nonneg w) hw 2
  unfold cut
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
  ring

lemma cut_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : 2 * R ≤ ‖w‖) : cut R w = 0 := by
  have hs : (2 * R) ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    rw [show w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 by simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm w).symm]
    exact pow_le_pow_left₀ (by positivity) hw 2
  unfold cut
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith))]
  ring

lemma extend_smooth {J : ℝ → ℂ → ℝ} (hJ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2)) (j R : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => extend J j R p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℂ => cut R p.2) := (cut_smooth R).comp contDiff_snd
  exact (hc.mul hJ).add ((contDiff_const.sub hc).mul contDiff_const)

lemma extend_eq {J : ℝ → ℂ → ℝ} {j R s : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ ≤ R) :
    extend J j R s w = J s w := by simp [extend, cut_one hR hw]

lemma extend_tail {J : ℝ → ℂ → ℝ} {j R s : ℝ} (hR : 0 < R) {w : ℂ} (hw : 2 * R ≤ ‖w‖) :
    extend J j R s w = j := by simp [extend, cut_zero hR hw]

lemma extend_flat {J : ℝ → ℂ → ℝ} {j R ρ : ℝ}
    (hflat : ∀ s (w : ℂ), ‖w‖ ≤ ρ → J s w = j) :
    ∀ s (w : ℂ), ‖w‖ ≤ ρ → extend J j R s w = j := by
  intro s w hw
  unfold extend
  rw [hflat s w hw]
  ring

lemma extend_pos {J : ℝ → ℂ → ℝ} {j R s : ℝ} (hj : 0 < j) (hpos : ∀ w, 0 < J s w) (w : ℂ) :
    0 < extend J j R s w := by
  have hc := cut_range R w
  by_cases h0 : cut R w = 0
  · simp [extend, h0, hj]
  · have hp : 0 < cut R w := lt_of_le_of_ne hc.1 (Ne.symm h0)
    unfold extend
    exact add_pos_of_pos_of_nonneg (mul_pos hp (hpos w)) (mul_nonneg (by linarith) hj.le)

/-- Positivity on the closed time interval extends to a common open time interval. -/
lemma exists_positive_interval {J : ℝ → ℂ → ℝ}
    (hJ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2)) {j R : ℝ} (hj : 0 < j) (hR : 0 < R)
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w, 0 < J s w) :
    ∃ δ > 0, ∀ s ∈ Ioo (-δ) (1 + δ), ∀ w, 0 < extend J j R s w := by
  let K : Set (ℝ × ℂ) := Icc 0 1 ×ˢ Metric.closedBall 0 (2 * R)
  have hc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 _)
  have ho : IsOpen {p : ℝ × ℂ | 0 < extend J j R p.1 p.2} :=
    isOpen_lt continuous_const (extend_smooth hJ j R).continuous
  have hsub : K ⊆ {p : ℝ × ℂ | 0 < extend J j R p.1 p.2} := by
    intro p hp
    exact extend_pos hj (hpos p.1 hp.1) p.2
  obtain ⟨δ, hδ, hd⟩ := hc.exists_thickening_subset_open ho hsub
  refine ⟨δ, hδ, fun s hs w => ?_⟩
  by_cases hw : 2 * R ≤ ‖w‖
  · rw [extend_tail hR hw]
    exact hj
  have hwK : w ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (not_le.mp hw).le
  rcases lt_or_ge s 0 with hsn | hsn
  · apply hd (a := (s, w))
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, w), ⟨⟨le_rfl, zero_le_one⟩, hwK⟩, ?_⟩
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_neg hsn, max_eq_left (by linarith : 0 ≤ -s)]
    linarith [hs.1]
  rcases le_or_gt s 1 with hsl | hsl
  · exact extend_pos hj (hpos s ⟨hsn, hsl⟩) w
  · apply hd (a := (s, w))
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(1, w), ⟨⟨zero_le_one, le_rfl⟩, hwK⟩, ?_⟩
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_pos (sub_pos.mpr hsl), max_eq_left (sub_nonneg.mpr hsl.le)]
    linarith [hs.2]

lemma jbar_continuous {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s)) :
    Continuous (Inner.Jbar J s) := by
  unfold Inner.Jbar
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hc.comp (Inner.contDiff_Rot.continuous.comp (continuous_snd.prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst))))

lemma jbar_tail {J : ℝ → ℂ → ℝ} {j R s : ℝ} (hR : 0 < R)
    (htail : ∀ w, 2 * R ≤ ‖w‖ → J s w = j) {E : ℝ} (hE : 4 * R ^ 2 ≤ E) : Inner.Jbar J s E = j := by
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ 4 * R ^ 2).trans hE
  have hs : 2 * R ≤ Real.sqrt E := (Real.le_sqrt (by positivity) hE0).mpr (by nlinarith)
  unfold Inner.Jbar
  rw [intervalIntegral.integral_congr (g := fun _ => j) (fun φ _ => htail _ (by
    rw [Inner.norm_Rot, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg E)]
    exact hs))]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp

/-- A positive constant density outside a fixed disc gives the proper area inverse. -/
lemma acal_tendsto {J : ℝ → ℂ → ℝ} {j R s : ℝ} (hj : 0 < j) (hR : 0 < R)
    (hc : Continuous (J s)) (htail : ∀ w, 2 * R ≤ ‖w‖ → J s w = j) :
    Tendsto (Inner.Acal J s) atTop atTop := by
  let T := 4 * R ^ 2
  have hJb := jbar_continuous hc
  have heq {E : ℝ} (hE : T ≤ E) : Inner.Acal J s E =
      Real.pi * j * E + (Inner.Acal J s T - Real.pi * j * T) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hJb.intervalIntegrable 0 T)
      (hJb.intervalIntegrable T E)
    unfold Inner.Acal
    rw [← hadd]
    have hh : (∫ t in T..E, Inner.Jbar J s t) = (E - T) * j := by
      rw [intervalIntegral.integral_congr (g := fun _ => j) (fun t ht =>
        by
          apply jbar_tail hR htail
          have ht' : t ∈ Icc T E := by simpa only [uIcc_of_le hE] using ht
          exact ht'.1)]
      simp [smul_eq_mul]
    rw [hh]
    ring
  have ht : Tendsto (fun E : ℝ => Real.pi * j * E + (Inner.Acal J s T - Real.pi * j * T)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (mul_pos Real.pi_pos hj))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with E hE
  exact (heq hE).symm

/-- The auxiliary density satisfies the existing normalization interface. -/
lemma exists_flat_density {J : ℝ → ℂ → ℝ}
    (hJ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => J p.1 p.2)) {j R ρ : ℝ}
    (hj : 0 < j) (hR : 0 < R) (hρ : 0 < ρ)
    (hflat : ∀ s (w : ℂ), ‖w‖ ≤ ρ → J s w = j)
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w, 0 < J s w) :
    ∃ δ > 0, Inner.FlatDensity (extend J j R) (-δ) (1 + δ) j ρ := by
  obtain ⟨δ, hδ, hp⟩ := exists_positive_interval hJ hj hR hpos
  refine ⟨δ, hδ, ⟨extend_smooth hJ j R, hp, fun s _ w hw => extend_flat hflat s w hw,
    hj, hρ, fun s _ => ?_⟩⟩
  exact acal_tendsto hj hR (Inner.contDiff_slice (extend_smooth hJ j R) s).continuous
    (fun _ hw => extend_tail hR hw)

/-- Circle averages only depend on the density inside the prescribed disc. -/
lemma jbar_local {J K : ℝ → ℂ → ℝ} {s R : ℝ} (hR : 0 ≤ R)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) {E : ℝ} (hE : E ≤ R ^ 2) :
    Inner.Jbar J s E = Inner.Jbar K s E := by
  unfold Inner.Jbar
  congr 1
  apply intervalIntegral.integral_congr
  intro φ _
  apply heq
  rw [Inner.norm_Rot, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg E)]
  exact (Real.sqrt_le_left hR).mpr hE

lemma acal_local {J K : ℝ → ℂ → ℝ} {s R : ℝ} (hR : 0 ≤ R)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) {E : ℝ} (hE : E ≤ R ^ 2) :
    Inner.Acal J s E = Inner.Acal K s E := by
  unfold Inner.Acal
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  apply jbar_local hR heq
  rw [uIcc, mem_Icc] at ht
  exact ht.2.trans (max_le (sq_nonneg R) hE)

lemma trot_local {J K : ℝ → ℂ → ℝ} {s R : ℝ} (hR : 0 ≤ R)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) {w : ℂ} (hw : ‖w‖ ≤ R) :
    Inner.Trot J s w = Inner.Trot K s w := by
  have hb : Inner.Bfun J s w = Inner.Bfun K s w := by
    unfold Inner.Bfun
    congr 1
    apply intervalIntegral.integral_congr
    intro φ _
    dsimp only
    rw [heq _ (by simpa only [Inner.norm_Rot] using hw)]
  unfold Inner.Trot
  rw [hb, jbar_local hR heq (pow_le_pow_left₀ (norm_nonneg w) hw 2)]

/-- Positivity suffices for strict monotonicity even when total area is finite. -/
lemma acal_strictMono {J : ℝ → ℂ → ℝ} {s : ℝ} (hc : Continuous (J s))
    (hp : ∀ w, 0 < J s w) : StrictMono (Inner.Acal J s) := by
  apply strictMono_of_hasDerivAt_pos
    (fun E => (((jbar_continuous hc).integral_hasStrictDerivAt 0 E).hasDerivAt).const_mul Real.pi)
  exact fun E => mul_pos Real.pi_pos (Inner.Jbar_pos hc hp E)

/-- The inverse agrees whenever the known preimage lies in the common disc. -/
lemma einv_local {J K : ℝ → ℂ → ℝ} {s R E I : ℝ} (hR : 0 ≤ R)
    (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) (hE : E ≤ R ^ 2)
    (hKI : Inner.Acal K s E = I) : Inner.Einv J s I = E := by
  apply Inner.invR_eq_of_apply_eq (acal_strictMono hc hp).injective
  exact (acal_local hR heq hE).trans hKI

/-- Locality of the entire inverse normalization, including the default branches in its definitions. -/
theorem normalize_local {J K : ℝ → ℂ → ℝ} {s s₁ s₂ j ρ R : ℝ}
    (hK : Inner.FlatDensity K s₁ s₂ j ρ) (hs : s ∈ Ioo s₁ s₂) (hR : 0 ≤ R)
    (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) {z : ℂ}
    (hgate : Real.pi * ‖z‖ ^ 2 < Inner.Acal J s (R ^ 2)) :
    Inner.TrotInv J s (Inner.Darea J s z) = Inner.TrotInv K s (Inner.Darea K s z) ∧
      ‖Inner.TrotInv K s (Inner.Darea K s z)‖ < R := by
  have haeq := acal_local hR heq (le_refl (R ^ 2))
  have hE : Inner.Einv K s (Real.pi * ‖z‖ ^ 2) < R ^ 2 := by
    apply (Inner.Acal_strictMono hK hs).lt_iff_lt.mp
    rw [Inner.Acal_Einv hK hs, ← haeq]
    exact hgate
  have hieq := einv_local hR hc hp heq hE.le (Inner.Acal_Einv hK hs (Real.pi * ‖z‖ ^ 2))
  have hDeq : Inner.Darea J s z = Inner.Darea K s z := by
    unfold Inner.Darea
    rw [hieq]
  have hw : ‖Inner.TrotInv K s (Inner.Darea K s z)‖ < R := by
    have hh := Inner.normalize_circle hK hs z
    nlinarith [norm_nonneg (Inner.TrotInv K s (Inner.Darea K s z))]
  refine ⟨?_, hw⟩
  rw [hDeq]
  apply Inner.TrotInv_eq_of (Inner.Trot_bijective hc hp).1
  rw [trot_local hR heq hw.le]
  exact Inner.Trot_TrotInv hK hs _

/-- The local inverse normalization retains the defining area identity. -/
theorem normalize_acal {J K : ℝ → ℂ → ℝ} {s s₁ s₂ j ρ R : ℝ}
    (hK : Inner.FlatDensity K s₁ s₂ j ρ) (hs : s ∈ Ioo s₁ s₂) (hR : 0 ≤ R)
    (hc : Continuous (J s)) (hp : ∀ w, 0 < J s w)
    (heq : ∀ w, ‖w‖ ≤ R → J s w = K s w) {z : ℂ}
    (hgate : Real.pi * ‖z‖ ^ 2 < Inner.Acal J s (R ^ 2)) :
    Inner.Acal J s (‖Inner.TrotInv J s (Inner.Darea J s z)‖ ^ 2) = Real.pi * ‖z‖ ^ 2 := by
  have hh := normalize_local hK hs hR hc hp heq hgate
  rw [hh.1]
  have hsq : ‖Inner.TrotInv K s (Inner.Darea K s z)‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).mpr hh.2.le
  rw [acal_local hR heq hsq, Inner.normalize_circle hK hs, Inner.Acal_Einv hK hs]

/-- The inverse normalization of a constant density is a linear dilation. -/
theorem normalize_constant {J : ℝ → ℂ → ℝ} {s j : ℝ} (hj : 0 < j)
    (hconst : ∀ w, J s w = j) (z : ℂ) :
    Inner.TrotInv J s (Inner.Darea J s z) = z / (Real.sqrt j : ℂ) := by
  have hc : Continuous (J s) := by convert continuous_const (y := j) using 1; exact funext hconst
  have hp : ∀ w, 0 < J s w := fun w => by rw [hconst]; exact hj
  have hbar (E : ℝ) : Inner.Jbar J s E = j := by
    unfold Inner.Jbar
    simp_rw [hconst]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  have hA (E : ℝ) : Inner.Acal J s E = Real.pi * j * E := by
    unfold Inner.Acal
    simp_rw [hbar]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hInv (I : ℝ) : Inner.Einv J s I = I / (Real.pi * j) := by
    apply Inner.invR_eq_of_apply_eq (acal_strictMono hc hp).injective
    rw [hA]
    field_simp
  have hTi (w : ℂ) : Inner.TrotInv J s w = w := by
    apply Inner.TrotInv_eq_of (Inner.Trot_bijective hc hp).1
    exact Inner.Trot_eq_id_of_const (fun u _ => hconst u) (le_refl ‖w‖)
  rw [hTi]
  by_cases hz : z = 0
  · simp [hz, Inner.Darea]
  have hzpos : 0 < Real.pi * ‖z‖ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz))
  unfold Inner.Darea
  rw [hInv]
  have hratio : Real.pi * (Real.pi * ‖z‖ ^ 2 / (Real.pi * j)) / (Real.pi * ‖z‖ ^ 2) = j⁻¹ := by field_simp
  rw [hratio, Real.sqrt_inv, Complex.ofReal_inv]
  rw [div_eq_inv_mul]

end SymplecticPacking.HighDim.PlanarGen.DensityExtension
