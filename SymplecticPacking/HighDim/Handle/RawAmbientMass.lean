import SymplecticPacking.HighDim.Handle.RawAmbientTransition

/-!
# Invariance of raw coordinate integrals

Intrinsic invariance of the raw coordinate integrals under positive transitions.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
namespace RawAmbientBox
variable (B C : RawAmbientBox E M)

theorem coefficient_zero {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} {K : Set M}
    (hz : ∀ x, x ∉ K → Ω x = 0) {z : Plane} (hn : z ∉ B.box.chart '' K) :
    B.coefficient Ω z = 0 := by
  unfold coefficient
  split_ifs with hzt
  · have hx : B.box.chart.symm z ∉ K :=
      fun hx => hn ⟨_, hx, B.box.chart.right_inv hzt⟩
    simp only [hz _ hx, ContinuousLinearMap.zero_apply]
  · rfl

theorem mass_eq_setIntegral {Ω : M → E →L[ℝ] E →L[ℝ] ℝ} {K : Set M}
    (hz : ∀ x, x ∉ K → Ω x = 0) :
    B.mass Ω = ∫ z in B.box.chart '' K, B.coefficient Ω z := by
  unfold mass
  rw [SymplecticPacking.Explicit.planeVolume_eq_volume]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hn => B.coefficient_zero hz hn)).symm

theorem coefficient_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.chart.source)
    (hz : ∀ x, x ∉ K → Ω x = 0) : ContDiff ℝ ∞ (B.coefficient Ω) := by
  have hKC := hK.image_of_continuousOn (B.box.chart.continuousOn.mono hKB)
  have hF : ContDiffOn ℝ ∞ B.frame B.box.chart.target :=
    hsB.fderiv_of_isOpen B.box.chart.open_target (by simp)
  have hΩc := (hΩ.comp_contMDiffOn hB.inverse).contDiffOn
  have hraw : ContDiffOn ℝ ∞ (fun z => Ω (B.box.chart.symm z)
      (B.frame z (1,0)) (B.frame z (0,1))) B.box.chart.target :=
    (hΩc.clm_apply (hF.clm_apply contDiffOn_const)).clm_apply (hF.clm_apply contDiffOn_const)
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hzt : z ∈ B.box.chart.target
  · apply (hraw.contDiffAt (B.box.chart.open_target.mem_nhds hzt)).congr_of_eventuallyEq
    filter_upwards [B.box.chart.open_target.mem_nhds hzt] with w hw
    exact if_pos hw
  · have hzn : z ∉ B.box.chart '' K := fun hx => by
      obtain ⟨x, hx, rfl⟩ := hx
      exact hzt (B.box.chart.map_source (hKB hx))
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hKC.isClosed.isOpen_compl.mem_nhds hzn] with w hw
    exact B.coefficient_zero hz hw

theorem coefficient_integrable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.chart.source)
    (hz : ∀ x, x ∉ K → Ω x = 0) : Integrable (B.coefficient Ω) :=
  (B.coefficient_smooth hB hsB hΩ hK hKB hz).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro
      (hK.image_of_continuousOn (B.box.chart.continuousOn.mono hKB))
      (fun _ hn => B.coefficient_zero hz hn))

theorem mass_change (hinc : B.inclusion = C.inclusion)
    (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    (hsC : ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {K : Set M}
    (hK : IsCompact K) (hKB : K ⊆ B.box.chart.source) (hKC : K ⊆ C.box.chart.source)
    (hz : ∀ x, x ∉ K → Ω x = 0)
    (hpos : ∀ z ∈ C.box.chart '' K, 0 < (fderiv ℝ (B.transition C) z).det) :
    C.mass Ω = B.mass Ω := by
  have hyt {z : Plane} (hz : z ∈ C.box.chart '' K) : z ∈ C.box.chart.target := by
    obtain ⟨x, hx, rfl⟩ := hz
    exact C.box.chart.map_source (hKC hx)
  have hyK {z : Plane} (hz : z ∈ C.box.chart '' K) : C.box.chart.symm z ∈ K := by
    obtain ⟨x, hx, rfl⟩ := hz
    simpa only [C.box.chart.left_inv (hKC hx)] using hx
  have htr {z : Plane} (hz : z ∈ C.box.chart '' K) :
      z ∈ (C.box.chart.symm.trans B.box.chart).source := ⟨hyt hz, hKB (hyK hz)⟩
  have hgi : InjOn (B.transition C) (C.box.chart '' K) := by
    intro y hy z hz he
    apply C.box.chart.symm.injOn (hyt hy) (hyt hz)
    exact B.box.chart.injOn (hKB (hyK hy)) (hKB (hyK hz)) he
  have him : B.transition C '' (C.box.chart '' K) = B.box.chart '' K := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨C.box.chart.symm y, hyK hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨C.box.chart x, ⟨x, hx, rfl⟩,
        congrArg B.box.chart (C.box.chart.left_inv (hKC hx))⟩
  have hm : MeasurableSet (C.box.chart '' K) :=
    (hK.image_of_continuousOn (C.box.chart.continuousOn.mono hKC)).measurableSet
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (f' := fderiv ℝ (B.transition C))
    (fun z hz => (B.transition_deriv C hinc hsC (hyt hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    hgi (B.coefficient Ω)
  rw [him] at hi
  rw [C.mass_eq_setIntegral hz, B.mass_eq_setIntegral hz, hi]
  apply setIntegral_congr_fun hm
  intro z hz
  change C.coefficient Ω z = |(fderiv ℝ (B.transition C) z).det| *
    B.coefficient Ω (B.transition C z)
  rw [B.coefficient_change C hinc hsB hsC Ω hΩ (htr hz), abs_of_pos (hpos z hz)]

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
