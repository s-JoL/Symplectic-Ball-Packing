import SymplecticPacking.HighDim.Comparator.PlanarJointDensity

/-!
# Local positive proper extensions for parameterized planar densities
-/

noncomputable section
set_option maxHeartbeats 800000
namespace SymplecticPacking.HighDim.PlanarGen.JointDensity

open Set Filter Topology Complex Metric
open scoped ContDiff Real
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def extension (J : P → ℂ → ℝ) (j : P → ℝ) (R : ℝ) (p : P) (w : ℂ) : ℝ :=
  DensityExtension.extend (family J p) (j p) R 0 w

lemma extension_smooth {J : P → ℂ → ℝ} {j : P → ℝ} {U : Set P}
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (U ×ˢ univ)) (hj : ContDiffOn ℝ ∞ j U) (R : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (extension J j R)) (U ×ˢ univ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : P × ℂ => DensityExtension.cut R q.2) (U ×ˢ univ) :=
    ((DensityExtension.cut_smooth R).comp contDiff_snd).contDiffOn
  have hj' : ContDiffOn ℝ ∞ (fun q : P × ℂ => j q.1) (U ×ˢ univ) :=
    hj.comp contDiffOn_fst (fun q hq => hq.1)
  exact (hc.mul hJ).add ((contDiffOn_const.sub hc).mul hj')

/-- A positive slice admits one common open parameter neighbourhood with a proper extension. -/
theorem extension_hyp {J : P → ℂ → ℝ} {j : P → ℝ} {U : Set P} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (U ×ˢ univ)) (hj : ContDiffOn ℝ ∞ j U)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hflat : ∀ p ∈ U, ∀ w, ‖w‖ ≤ ρ → J p w = j p)
    {p₀ : P} (hp₀ : p₀ ∈ U) (hj₀ : 0 < j p₀) (hpos : ∀ w, 0 < J p₀ w) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ U ∧ Hyp (extension J j R) j V ρ := by
  let E := extension J j R
  have hE := extension_smooth hJ hj R
  have hj' : ContinuousOn (fun q : P × ℂ => j q.1) (U ×ˢ univ) :=
    hj.continuousOn.comp continuous_fst.continuousOn (fun q hq => hq.1)
  let O : Set (P × ℂ) := ((U ×ˢ univ) ∩ (fun q : P × ℂ => j q.1) ⁻¹' Ioi 0) ∩
    ((U ×ˢ univ) ∩ (Function.uncurry E) ⁻¹' Ioi 0)
  have ho : IsOpen O := (hj'.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Ioi).inter
    (hE.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Ioi)
  have hsub : ({p₀} : Set P) ×ˢ closedBall (0 : ℂ) (2 * R) ⊆ O := by
    rintro ⟨p, w⟩ ⟨hp, hw⟩
    have hpp : p = p₀ := hp
    subst p
    exact ⟨⟨⟨hp₀, mem_univ _⟩, hj₀⟩,
      ⟨⟨hp₀, mem_univ _⟩, DensityExtension.extend_pos hj₀ hpos w⟩⟩
  obtain ⟨V, W, hV, hW, hpV, hKW, hVW⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_closedBall (0 : ℂ) (2 * R)) ho hsub
  have h0W : (0 : ℂ) ∈ W := hKW (by simpa using (show (0 : ℝ) ≤ 2 * R by positivity))
  have hVU : V ⊆ U := fun p hp => (hVW (a := (p, (0 : ℂ))) ⟨hp, h0W⟩).1.1.1
  have hjV : ∀ p ∈ V, 0 < j p := fun p hp => (hVW (a := (p, (0 : ℂ))) ⟨hp, h0W⟩).1.2
  have hposV : ∀ p ∈ V, ∀ w, 0 < E p w := by
    intro p hp w
    by_cases hw : 2 * R ≤ ‖w‖
    · change 0 < DensityExtension.extend (family J p) (j p) R 0 w
      rw [DensityExtension.extend_tail hR hw]
      exact hjV p hp
    · exact (hVW (a := (p, w)) ⟨hp, hKW (by simpa only [mem_closedBall, dist_zero_right] using (not_le.mp hw).le)⟩).2.2
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry E) (V ×ˢ univ) :=
    hE.mono (fun q hq => ⟨hVU hq.1, hq.2⟩)
  refine ⟨V, hV, hpV (mem_singleton p₀), hVU, ?_⟩
  refine ⟨hV, hsmooth, hj.mono hVU, hposV, ?_, hjV, hρ, ?_⟩
  · intro p hp w hw
    exact DensityExtension.extend_flat (fun _ u hu => hflat p (hVU hp) u hu) 0 w hw
  · intro p hp
    have hslice : Continuous (E p) := by
      apply continuous_iff_continuousAt.mpr
      intro w
      have hpoint : ContinuousAt (Function.uncurry E) (p, w) :=
        hsmooth.continuousOn.continuousAt ((hV.prod isOpen_univ).mem_nhds ⟨hp, mem_univ w⟩)
      have hembed : ContinuousAt (fun u : ℂ => (p, u)) w :=
        continuousAt_const.prodMk continuousAt_id
      exact hpoint.comp hembed
    exact DensityExtension.acal_tendsto (J := family E p) (s := 0)
      (hjV p hp) hR hslice (fun w hw => DensityExtension.extend_tail hR hw)

end SymplecticPacking.HighDim.PlanarGen.JointDensity
