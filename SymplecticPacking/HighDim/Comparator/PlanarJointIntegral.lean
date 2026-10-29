import SymplecticPacking.HighDim.Comparator.PlanarJointInverse

/-!
# Smooth integration for arbitrary finite-dimensional parameters
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric
open scoped ContDiff

/-- Smooth integration is local in the entire parameter vector. -/
theorem fixed_integral_at {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {U : Set P} (hU : IsOpen U) {f : ℝ × P → ℝ}
    (hf : ContDiffOn ℝ ∞ f {q | q.2 ∈ U}) {p₀ : P} (hp₀ : p₀ ∈ U) :
    ContDiffAt ℝ ∞ (fun p : P => ∫ t in (0 : ℝ)..1, f (t, p)) p₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hp₀
  let c : ContDiffBump p₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hO : IsOpen {q : ℝ × P | q.2 ∈ U} := hU.preimage continuous_snd
  have hcs : ContDiff ℝ ∞ (fun q : ℝ × P => c q.2) :=
    (c.contDiff (n := ⊤)).comp contDiff_snd
  have hg : ContDiff ℝ ∞ (fun q : ℝ × P => c q.2 * f q) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2 ∈ U
    · exact hcs.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds hq))
    · have hnot : q.2 ∉ tsupport c := by
        rw [c.tsupport_eq]
        intro hm
        have hr : c.rOut = ε / 2 := rfl
        rw [hr] at hm
        exact hq (hball (lt_of_le_of_lt (mem_closedBall.mp hm) (by linarith)))
      have h1 := notMem_tsupport_iff_eventuallyEq.mp hnot
      have h2 := (continuous_snd.tendsto q).eventually h1
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [h2] with q' hq'
      simp only [Pi.zero_apply] at hq'
      simp [hq']
  have hI := OAI.PackingSufficiencySupport.Hamiltonian.contDiff_fixed_integral hg
  apply hI.contDiffAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ p in 𝓝 p₀, p ∈ closedBall p₀ (ε / 4) :=
    continuous_id.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (by positivity))
  filter_upwards [hnear] with p hp
  rw [intervalIntegral.integral_const_mul, c.one_of_mem_closedBall hp, one_mul]


/-- Differentiating in the fibre variable preserves smooth parameter dependence on an open set. -/
theorem partial_fderiv_smooth {P X Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set P} (hU : IsOpen U) {f : P → X → Y}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q : P × X => fderiv ℝ (f q.1) q.2) (U ×ˢ univ) := by
  have hd := hf.fderiv_of_isOpen (hU.prod isOpen_univ) (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  have hc : ContDiffOn ℝ ∞ (fun q : P × X =>
      (fderiv ℝ (Function.uncurry f) q).comp (ContinuousLinearMap.inr ℝ P X)) (U ×ˢ univ) :=
    hd.clm_comp contDiffOn_const
  apply hc.congr
  intro q hq
  have htotal := (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) q) q := htotal.hasFDerivAt
  have hi : HasFDerivAt (fun x : X => (q.1, x)) (ContinuousLinearMap.inr ℝ P X) q.2 :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2
  have hs := HasFDerivAt.comp q.2 ht hi
  exact hs.fderiv

/-- Scalar fibre derivatives are jointly smooth on an open parameter set. -/
theorem partial_deriv_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} (hU : IsOpen U) {f : P → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q : P × ℝ => deriv (f q.1) q.2) (U ×ˢ univ) :=
  (partial_fderiv_smooth hU hf).clm_apply contDiffOn_const

end SymplecticPacking.HighDim.PlanarGen
