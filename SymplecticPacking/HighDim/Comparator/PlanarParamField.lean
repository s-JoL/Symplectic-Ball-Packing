import SymplecticPacking.HighDim.Comparator.PlanarParamFlow

/-!
# Joint smoothness of the parameterized source-cutoff field

Joint smoothness of the source-cutoff field for a family of ordinary paths.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric Function
open scoped ContDiff
open OAI.PackingSufficiencySupport.Hamiltonian

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]

def varyPath (D : Qhat.PathData) (f : P → ℝ → ℂ → ℂ) (p : P) : Qhat.PathData :=
  { D with path := f p }

variable {D : Qhat.PathData} {f : P → ℝ → ℂ → ℂ} {U : Set P}

/-- The source velocity is a partial derivative of the entire parameter family. -/
theorem varying_ordVel_smooth (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => Qhat.ordVel (varyPath D f q.1.1) q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag) := by
  let Ω : Set ((P × ℝ) × ℂ) := (U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag
  have hΩ : IsOpen Ω := (hU.prod isOpen_univ).prod (Qhat.isOpen_areaDisk _)
  have hd := hf.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hs := hd.clm_apply (contDiffOn_const (c := (((0 : P), (1 : ℝ)), (0 : ℂ))))
  apply hs.congr
  intro q hq
  have hp := (hf.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)
  have he : HasFDerivAt (fun r : ℝ × ℂ => ((q.1.1, r.1), r.2))
      (((0 : (ℝ × ℂ) →L[ℝ] P).prod (ContinuousLinearMap.fst ℝ ℝ ℂ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℂ)) (q.1.2, q.2) :=
    (hasFDerivAt_const q.1.1 _ |>.prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hcomp := hp.hasFDerivAt.comp (q.1.2, q.2) he
  change fderiv ℝ (fun r : ℝ × ℂ => f q.1.1 r.1 r.2) (q.1.2, q.2) (1, 0) = _
  have hder := hcomp.fderiv
  change fderiv ℝ (fun r : ℝ × ℂ => f q.1.1 r.1 r.2) (q.1.2, q.2) = _ at hder
  rw [hder]
  rfl

/-- The ambient field is jointly smooth on the open parameter domain.
The cutoff in the source keeps its support away from the boundary of the path image. -/
theorem varying_ambientField_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.ambientField (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  let Ω : Set ((P × ℝ) × ℂ) := (U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag
  let G : (P × ℝ) × ℂ → (P × ℝ) × ℂ := fun q => (q.1, f q.1.1 q.1.2 q.2)
  have hΩ : IsOpen Ω := (hU.prod isOpen_univ).prod (Qhat.isOpen_areaDisk _)
  have hG : ContDiffOn ℝ ∞ G Ω := contDiffOn_fst.prodMk hf
  have hi : InjOn G Ω := by
    intro a ha b hb he
    have h1 := congrArg (fun z : (P × ℝ) × ℂ => z.1) he
    have h2 := congrArg (fun z : (P × ℝ) × ℂ => z.2) he
    change a.1 = b.1 at h1
    change f a.1.1 a.1.2 a.2 = f b.1.1 b.1.2 b.2 at h2
    apply Prod.ext h1
    apply (hOrd a.1.1 ha.1.1).injOn a.1.2 ha.2
    · exact hb.2
    · change f a.1.1 a.1.2 a.2 = f a.1.1 a.1.2 b.2
      simpa only [h1] using h2
  have hdi : ∀ q ∈ Ω, (fderiv ℝ G q).IsInvertible := by
    intro q hq
    have hfa := (hf.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)
    rw [(hasFDerivAt_fst.prodMk hfa.hasFDerivAt).fderiv]
    apply clockGraph_linear_invertible
    have hin : HasFDerivAt (fun z : ℂ => (q.1, z))
        (ContinuousLinearMap.inr ℝ (P × ℝ) ℂ) q.2 :=
      hasFDerivAt_prodMk_right q.1 q.2
    have hs := hfa.hasFDerivAt.comp q.2 hin
    rw [← hs.fderiv]
    apply Qhat.isInvertible_of_det_ne_zero
    change LinearMap.det (fderiv ℝ ((varyPath D f q.1.1).path q.1.2) q.2 : ℂ →ₗ[ℝ] ℂ) ≠ 0
    rw [(hOrd q.1.1 hq.1.1).det q.1.2 q.2 hq.2]
    exact (lt_of_lt_of_le (pow_pos (hOrd q.1.1 hq.1.1).c_pos 2)
      ((hOrd q.1.1 hq.1.1).gam_ge q.1.2)).ne'
  obtain ⟨himage, hg, hleft, hright⟩ := smooth_inverse_on hΩ hG hi hdi
  let g := invFunOn G Ω
  have hgΩ : ∀ q ∈ G '' Ω, g q ∈ Ω := fun q hq => invFunOn_mem hq
  have hg1 : ∀ q ∈ G '' Ω, (g q).1 = q.1 := by
    intro q hq
    have hh := congrArg (fun z : (P × ℝ) × ℂ => z.1) (hright q hq)
    exact hh
  have hmem : ∀ q : (P × ℝ) × ℂ, q ∈ G '' Ω ↔
      q.1.1 ∈ U ∧ q.2 ∈ f q.1.1 q.1.2 '' Qhat.areaDisk D.pdag := by
    intro q
    constructor
    · rintro ⟨r, hr, he⟩
      have h1 := congrArg (fun z : (P × ℝ) × ℂ => z.1) he
      change r.1 = q.1 at h1
      refine ⟨by simpa only [← h1] using hr.1.1, r.2, hr.2, ?_⟩
      simpa only [G, h1] using congrArg Prod.snd he
    · rintro ⟨hp, z, hz, he⟩
      exact ⟨(q.1, z), ⟨⟨hp, mem_univ _⟩, hz⟩, Prod.ext rfl he⟩
  have hord : ∀ q ∈ G '' Ω,
      Qhat.ordInv (varyPath D f q.1.1) q.1.2 q.2 = (g q).2 := by
    intro q hq
    have h2 : f q.1.1 q.1.2 (g q).2 = q.2 := by
      have hh := congrArg (fun z : (P × ℝ) × ℂ => z.2) (hright q hq)
      change f (g q).1.1 (g q).1.2 (g q).2 = q.2 at hh
      simpa only [hg1 q hq] using hh
    rw [← h2]
    exact Qhat.ordInv_eq (hOrd q.1.1 ((hmem q).mp hq).1)
      (by simpa only [varyPath] using (hgΩ q hq).2)
  have hWon : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.ambientField (varyPath D f q.1.1) q.1.2 q.2) (G '' Ω) := by
    have hχ : ContDiff ℝ ∞ (fun z : ℂ => Qhat.chiCut D (Real.pi * ‖z‖^2)) :=
      (Qhat.chiCut_contDiff D).comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hvel := varying_ordVel_smooth hU hf
    have hs : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
        Qhat.chiCut D (Real.pi * ‖(g q).2‖^2) •
          Qhat.ordVel (varyPath D f q.1.1) q.1.2 (g q).2) (G '' Ω) := by
      refine (hχ.comp_contDiffOn hg.snd).smul ?_
      apply hvel.comp (contDiffOn_fst.prodMk hg.snd)
      intro q hq
      exact ⟨⟨((hmem q).mp hq).1, mem_univ _⟩, (hgΩ q hq).2⟩
    apply hs.congr
    intro q hq
    have hz : q.2 ∈ (varyPath D f q.1.1).path q.1.2 ''
        Qhat.areaDisk (varyPath D f q.1.1).pdag := ((hmem q).mp hq).2
    rw [Qhat.ambientField, if_pos hz, hord q hq]
    rfl
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hqim : q ∈ G '' Ω
  · exact hWon.contDiffAt (himage.mem_nhds hqim)
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q.1.1 hq.1.1
    let Kp := closedBall q.1.1 (ε/2)
    have hKp : IsCompact Kp := isCompact_closedBall _ _
    have hKpU : Kp ⊆ U := fun p hp => hball
      (lt_of_le_of_lt (mem_closedBall.mp hp) (by linarith))
    let Ksrc : Set ((P × ℝ) × ℂ) := (Kp ×ˢ Icc 0 1) ×ˢ Qhat.closedAreaDisk (Qhat.pzero D)
    have hKsub : Ksrc ⊆ Ω := fun r hr =>
      ⟨⟨hKpU hr.1.1, mem_univ _⟩,
        Qhat.closedAreaDisk_pzero_subset (hOrd r.1.1 (hKpU hr.1.1)) hr.2⟩
    let K := G '' Ksrc
    have hK : IsCompact K :=
      ((hKp.prod isCompact_Icc).prod (Qhat.isCompact_closedAreaDisk _)).image_of_continuousOn
        (hG.continuousOn.mono hKsub)
    have hKimage : K ⊆ G '' Ω := image_mono hKsub
    have hqK : q ∉ K := fun h => hqim (hKimage h)
    have hz (r : (P × ℝ) × ℂ) (hp : r.1.1 ∈ Kp) (hr : r ∉ K) :
        Qhat.ambientField (varyPath D f r.1.1) r.1.2 r.2 = 0 := by
      by_cases him : r.2 ∈ f r.1.1 r.1.2 '' Qhat.areaDisk D.pdag
      · obtain ⟨z, hzs, hze⟩ := him
        have hv := hOrd r.1.1 (hKpU hp)
        rw [← hze]
        change Qhat.ambientField (varyPath D f r.1.1) r.1.2
          ((varyPath D f r.1.1).path r.1.2 z) = 0
        rw [Qhat.ambientField_apply hv hzs]
        by_cases hzc : z ∈ Qhat.closedAreaDisk (Qhat.pzero D)
        · have ht : r.1.2 ∉ Icc (0 : ℝ) 1 := fun ht =>
            hr ⟨(r.1, z), ⟨⟨hp, ht⟩, hzc⟩, Prod.ext rfl hze⟩
          have htt : r.1.2 ≤ 0 ∨ 1 ≤ r.1.2 := by
            simp only [mem_Icc, not_and_or, not_le] at ht
            exact ht.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
          rw [Qhat.ordVel_eq_zero hv htt hzs, smul_zero]
        · rw [Qhat.chiCut_eq_zero hv (le_of_lt (not_le.mp hzc)), zero_smul]
      · exact Qhat.ambientField_eq_zero_of_not_mem him
    have hpnear : ∀ᶠ r : (P × ℝ) × ℂ in 𝓝 q, r.1.1 ∈ Kp :=
      (continuous_fst.comp continuous_fst).continuousAt.preimage_mem_nhds
        (closedBall_mem_nhds _ (by positivity))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hpnear, hK.isClosed.isOpen_compl.mem_nhds hqK] with r hp hr
    exact hz r hp hr

end SymplecticPacking.HighDim.PlanarGen

namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric Function
open scoped ContDiff
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]
variable {D : Qhat.PathData} {f : P → ℝ → ℂ → ℂ} {U : Set P}

/-- Joint smoothness of the ambient flow, with its common time and spatial support. -/
theorem varying_ambientFlow_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : P × (ℝ × ℂ) =>
      Qhat.ambientFlow (varyPath D f q.1) q.2.1 q.2.2) (U ×ˢ univ) := by
  apply local_param_flow_smooth hU
    (W := fun p => Qhat.ambientField (varyPath D f p))
    (K := Icc (0 : ℝ) 1 ×ˢ Qhat.closedAreaDisk D.Psupp)
  · apply (varying_ambientField_smooth hU hOrd hf).comp
      ((contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk contDiffOn_snd.snd)
    intro q hq
    exact ⟨⟨hq.1, mem_univ _⟩, mem_univ _⟩
  · intro p hp
    exact Qhat.ambientField_good (hOrd p hp)
  · exact isCompact_Icc.prod (Qhat.isCompact_closedAreaDisk _)
  · intro p hp q hq
    by_cases ht : q.1 ∈ Icc (0 : ℝ) 1
    · have hz : D.Psupp < Real.pi * ‖q.2‖^2 := by
        by_contra hn
        exact hq ⟨ht, le_of_not_gt hn⟩
      exact Qhat.ambientField_eq_zero_of_Psupp_lt (hOrd p hp) hz
    · apply Qhat.ambientField_eq_zero_of_time (hOrd p hp) _
      simp only [mem_Icc, not_and_or, not_le] at ht
      exact ht.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)

end SymplecticPacking.HighDim.PlanarGen
