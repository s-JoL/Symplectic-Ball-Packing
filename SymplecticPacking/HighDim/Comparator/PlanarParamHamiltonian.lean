import SymplecticPacking.HighDim.Comparator.PlanarParamNormalize

/-!
# Joint smoothness of the parameterized whole-disk Hamiltonian

The source primitive and inverse give a jointly smooth whole-disk Hamiltonian.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric Function
open scoped ContDiff
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]
variable {D : Qhat.PathData} {f : P → ℝ → ℂ → ℂ} {U : Set P}

/-- Differentiating the family in time and space preserves smooth dependence. -/
theorem varying_aq_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.aq (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  have hq := varying_qhat_smooth hU hOrd hf
  have huq : ContDiffOn ℝ ∞ (fun q : P × (ℝ × ℂ) => Qhat.uq (varyPath D f q.1) q.2)
      (U ×ˢ univ) := by
    apply hq.comp ((contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk contDiffOn_snd.snd)
    intro q hq
    exact ⟨⟨hq.1, mem_univ _⟩, mem_univ _⟩
  have hd := partial_fderiv_smooth (P := P) (X := ℝ × ℂ) (Y := ℂ)
    (f := fun p r => Qhat.uq (varyPath D f p) r) hU huq
  have hder : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      fderiv ℝ (Qhat.uq (varyPath D f q.1.1)) (q.1.2, q.2))
      ((U ×ˢ univ) ×ˢ univ) := by
    apply hd.comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
    intro q hq
    exact ⟨hq.1.1, mem_univ _⟩
  exact (Qhat.omega2L.contDiff.comp_contDiffOn (hder.clm_apply contDiffOn_const)).clm_comp
    (hder.clm_comp contDiffOn_const)

/-- The radial primitive is smooth in every parameter, by integration on a fixed interval. -/
theorem varying_hq_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.hq (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  apply fixed_integral_at ((hU.prod isOpen_univ).prod isOpen_univ) (p₀ := q) (hp₀ := hq)
    (f := fun r : ℝ × ((P × ℝ) × ℂ) =>
      Qhat.aq (varyPath D f r.2.1.1) r.2.1.2 (r.1 • r.2.2) r.2.2)
  have ha := varying_aq_smooth hU hOrd hf
  apply (ha.comp
    (contDiffOn_snd.fst.prodMk (contDiffOn_fst.smul contDiffOn_snd.snd))
    (fun r hr => ⟨hr.1, mem_univ _⟩)).clm_apply contDiffOn_snd.snd

/-- The inverse uses exactly the unique-preimage definition in the whole-disk construction. -/
theorem varying_qhatInv_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.qhatInv (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  apply param_inverse_smooth (P := P × ℝ) (X := ℂ)
    (G := fun p z => Qhat.qhat (varyPath D f p.1) p.2 z)
    (inv := fun p z => Qhat.qhatInv (varyPath D f p.1) p.2 z)
    (hU.prod isOpen_univ) (varying_qhat_smooth hU hOrd hf)
  · intro p hp
    exact (Qhat.qhat_bijective (hOrd p.1 hp.1) p.2).1
  · intro p hp z
    apply Inner.injective_of_det_ne_zero
    rw [Qhat.qhat_symplectic (hOrd p.1 hp.1)]
    exact one_ne_zero
  · intro p hp z
    exact Qhat.qhat_qhatInv (hOrd p.1 hp.1) p.2 z

/-- The whole-disk Hamiltonian has full finite-dimensional parameter dependence. -/
theorem varying_Qham_smooth (hU : IsOpen U)
    (hOrd : ∀ p ∈ U, Qhat.OrdinaryPath (varyPath D f p))
    (hf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => f q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ Qhat.areaDisk D.pdag)) :
    ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.Qham (varyPath D f q.1.1) q.1.2 q.2) ((U ×ˢ univ) ×ˢ univ) := by
  have hh := varying_hq_smooth (D := D) (f := f) (U := U) hU hOrd hf
  have hi := varying_qhatInv_smooth (D := D) (f := f) (U := U) hU hOrd hf
  have hO : IsOpen (((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℂ))) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have h1 : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.hq (varyPath D f q.1.1) q.1.2
        (Qhat.qhatInv (varyPath D f q.1.1) q.1.2 q.2)) ((U ×ˢ univ) ×ˢ univ) := by
    intro q hq
    have hqi : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ =>
        Qhat.qhatInv (varyPath D f r.1.1) r.1.2 r.2) q :=
      hi.contDiffAt (hO.mem_nhds hq)
    have hm : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ =>
        (r.1, Qhat.qhatInv (varyPath D f r.1.1) r.1.2 r.2)) q :=
      contDiffAt_fst.prodMk hqi
    have hH : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ =>
        Qhat.hq (varyPath D f r.1.1) r.1.2 r.2)
        (q.1, Qhat.qhatInv (varyPath D f q.1.1) q.1.2 q.2) :=
      hh.contDiffAt (hO.mem_nhds ⟨hq.1, mem_univ _⟩)
    exact (hH.comp q hm).contDiffWithinAt
  have h2 : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ =>
      Qhat.hq (varyPath D f q.1.1) q.1.2 (Qhat.zbd D)) ((U ×ˢ univ) ×ˢ univ) := by
    intro q hq
    have hm : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ => (r.1, Qhat.zbd D)) q :=
      contDiffAt_fst.prodMk contDiffAt_const
    have hH : ContDiffAt ℝ ∞ (fun r : (P × ℝ) × ℂ =>
        Qhat.hq (varyPath D f r.1.1) r.1.2 r.2) (q.1, Qhat.zbd D) :=
      hh.contDiffAt (hO.mem_nhds ⟨hq.1, mem_univ _⟩)
    exact (hH.comp q hm).contDiffWithinAt
  have he : (fun q : (P × ℝ) × ℂ => Qhat.Qham (varyPath D f q.1.1) q.1.2 q.2) =
      (fun q : (P × ℝ) × ℂ => -(Qhat.hq (varyPath D f q.1.1) q.1.2
        (Qhat.qhatInv (varyPath D f q.1.1) q.1.2 q.2) -
          Qhat.hq (varyPath D f q.1.1) q.1.2 (Qhat.zbd D))) := by
    funext q
    rfl
  rw [he]
  exact (h1.sub h2).neg

end SymplecticPacking.HighDim.PlanarGen
