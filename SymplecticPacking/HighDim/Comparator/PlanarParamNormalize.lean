import SymplecticPacking.HighDim.Comparator.PlanarParamField
import SymplecticPacking.HighDim.Comparator.PlanarJointDensity
import SymplecticPacking.Qhat.Ham

/-!
# Joint smoothness of the parameterized area normalization

Joint area normalization of the parameterized whole-disk flow.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric Function Complex
open scoped ContDiff
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]
variable {D : Qhat.PathData} {f : P → ℝ → ℂ → ℂ} {U : Set P}

/-- Rescaling makes the density identically one on a common neighbourhood of zero. -/
theorem varying_Gphi_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.Gphi (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  have hflow := varying_ambientFlow_smooth hU hOrd hf
  intro q hq
  have hv := hOrd q.1.1 hq.1.1
  have hγpos : 0 < D.gam q.1.2 :=
    (pow_pos hv.c_pos 2).trans_le (hv.gam_ge q.1.2)
  have hγ : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ => D.gam r.1.2) q :=
    hv.gam_smooth.contDiffAt.comp q contDiffAt_fst.snd
  have hroot := (Real.contDiffAt_sqrt hγpos.ne').comp q hγ
  have hscale : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ =>
      (Real.sqrt (D.gam r.1.2))⁻¹ • r.2) q :=
    (hroot.inv (Real.sqrt_pos.mpr hγpos).ne').smul contDiffAt_snd
  have hφ : ContDiffAt ℝ ∞ (fun r : P × (ℝ × ℂ) =>
      Qhat.ambientFlow (varyPath D f r.1) r.2.1 r.2.2)
      (q.1.1, (q.1.2, (Real.sqrt (D.gam q.1.2))⁻¹ • q.2)) :=
    hflow.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hq.1.1, mem_univ _⟩)
  exact (hφ.comp q (contDiffAt_fst.fst.prodMk
    (contDiffAt_fst.snd.prodMk hscale))).contDiffWithinAt

/-- The determinant density depends smoothly on the complete parameter vector. -/
theorem varying_Jhat_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.Jhat (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  have hs := partial_fderiv_smooth (P := P × ℝ) (X := ℂ) (Y := ℂ)
    (f := fun p z => Qhat.Gphi (varyPath D f p.1) p.2 z)
    (hU.prod isOpen_univ) (varying_Gphi_smooth hU hOrd hf)
  exact Qhat.det2_contDiff.comp_contDiffOn hs

/-- The complete whole-disk isotopy is jointly smooth, including the centre of each disk. -/
theorem varying_qhat_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.qhat (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  let J : (P × ℝ) → ℂ → ℝ := fun p => Qhat.Jhat (varyPath D f p.1) p.2
  let V : Set (P × ℝ) := U ×ˢ univ
  by_cases hne : U.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have H : JointDensity.Hyp J (fun _ => 1) V (Qhat.rhoC D) :=
      { openU := hU.prod isOpen_univ
        smooth := varying_Jhat_smooth hU hOrd hf
        j_smooth := contDiffOn_const
        pos := fun p hp w => Qhat.Jhat_pos (hOrd p.1 hp.1) p.2 w
        flat := fun p hp w hw => Qhat.Jhat_flat (hOrd p.1 hp.1) hw
        j_pos := fun _ _ => one_pos
        ρ_pos := by
          simpa only [varyPath, Qhat.rhoC, Qhat.pon] using
            (Qhat.rhoC_pos (D := varyPath D f p₀) (hOrd p₀ hp₀))
        proper := fun p hp => by
          exact Qhat.Acal_tendsto (hOrd p.1 hp.1) p.2 }
    have hn := JointDensity.normalize_smooth H
    have he : (fun q : (P × ℝ) × ℂ =>
        Inner.TrotInv (JointDensity.family J q.1) 0 (Inner.Darea (JointDensity.family J q.1) 0 q.2)) =
      (fun q : (P × ℝ) × ℂ => Inner.TrotInv (Qhat.Jhat (varyPath D f q.1.1)) q.1.2
        (Inner.Darea (Qhat.Jhat (varyPath D f q.1.1)) q.1.2 q.2)) := by
      rfl
    rw [he] at hn
    apply (varying_Gphi_smooth hU hOrd hf).comp (contDiffOn_fst.prodMk hn)
    intro q hq
    exact ⟨hq.1, mem_univ _⟩
  · intro q hq
    exact False.elim (hne ⟨q.1.1, hq.1.1⟩)

end SymplecticPacking.HighDim.PlanarGen
