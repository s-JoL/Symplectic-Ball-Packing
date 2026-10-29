import SymplecticPacking.HighDim.Handle.RawAmbientBoxPrimitive

/-!
# Smooth parameter dependence of raw box data

Smooth dependence of raw coefficients, their masses, and their coordinate primitives.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function MeasureTheory Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
namespace RawAmbientBox
variable (B : RawAmbientBox E M)

theorem coefficient_family_smooth
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.chart.source)
    (hz : ∀ p x, x ∉ K → Ω p x = 0) :
    ContDiff ℝ ∞ (fun q : P × Plane => B.coefficient (Ω q.1) q.2) := by
  have hid : ContMDiffOn 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (id : P → P) univ := contMDiffOn_id
  have hmap : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane))
      ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) ∞ (Prod.map id B.box.chart.symm)
      (univ ×ˢ B.box.chart.target) := hid.prodMap hB.inverse
  have hcomp := hΩ.comp_contMDiffOn hmap
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
  have hΩc := hcomp.contDiffOn
  have hF : ContDiffOn ℝ ∞ (fun q : P × Plane => B.frame q.2) (univ ×ˢ B.box.chart.target) :=
    (hsB.fderiv_of_isOpen B.box.chart.open_target (by simp)).comp
      contDiffOn_snd (fun q hq => hq.2)
  have hraw : ContDiffOn ℝ ∞ (fun q : P × Plane =>
      Ω q.1 (B.box.chart.symm q.2) (B.frame q.2 (1,0)) (B.frame q.2 (0,1)))
      (univ ×ˢ B.box.chart.target) :=
    (hΩc.clm_apply (hF.clm_apply contDiffOn_const)).clm_apply (hF.clm_apply contDiffOn_const)
  have hKC := hK.image_of_continuousOn (B.box.chart.continuousOn.mono hKB)
  have hext := spatialZeroExtension_smooth B.box.chart.open_target hKC.isClosed
    (show B.box.chart '' K ⊆ B.box.chart.target from fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      exact B.box.chart.map_source (hKB hx)) hraw
    (fun p z hzt hzn => by
      have hx : B.box.chart.symm z ∉ K := fun hx => hzn ⟨_,hx,B.box.chart.right_inv hzt⟩
      simp only [hz p _ hx, zero_apply])
  exact hext

theorem mass_family_smooth
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.chart.source)
    (hz : ∀ p x, x ∉ K → Ω p x = 0) :
    ContDiff ℝ ∞ (fun p => B.mass (Ω p)) := by
  have hKC := hK.image_of_continuousOn (B.box.chart.continuousOn.mono hKB)
  obtain ⟨R,hR⟩ := hKC.isBounded.subset_closedBall (0:Plane)
  simp only [mass,SymplecticPacking.Explicit.planeVolume_eq_volume]
  apply planar_fixed_support_integral_smooth (A := max R 0+1)
    (B.coefficient_family_smooth hB hsB hΩ hK hKB hz)
  intro p x y hxy
  apply B.coefficient_zero (hz p)
  intro hmem
  have hn : max |x| |y| ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using hR hmem
  rcases hxy with hx | hy
  · linarith [le_max_left |x| |y|,le_max_left R 0]
  · linarith [le_max_right |x| |y|,le_max_left R 0]

theorem primitive_family_smooth (hB : B.box.Smooth)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2| →
      f (p,(x,y)) = 0)
    (hmass : ∀ p, (∫ z, f (p,z) ∂SymplecticPacking.Explicit.planeVolume) = 0) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => B.primitive (fun z => f (q.1,z)) q.2) := by
  have hp := formulaTranslatedCovectorOperator_spec B.box.radius_pos B.box.point hf hzero
    (fun p => by simpa only [SymplecticPacking.Explicit.planeVolume_eq_volume] using hmass p)
  have hraw : ContDiff ℝ ∞ (fun q : P × Plane =>
      (formulaTranslatedCovectorOperator B.box.radius B.box.radius_pos B.box.point
        (fun z => f (q.1,z)) q.2).comp B.coordinate) := hp.1.clm_comp contDiff_const
  have hz : ∀ p x, x ∉ B.box.compactCarrier → B.primitive (fun z => f (p,z)) x = 0 := by
    intro p x hx
    apply B.primitive_zero _ _ hx
    intro z hzn
    have hh : B.box.radius < max |z.1-B.box.point.1| |z.2-B.box.point.2| := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,
        Prod.snd_sub,Real.norm_eq_abs,not_le] using hzn
    exact hp.2.1 p z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  have hsnd : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Plane) ∞
      (fun q : P × M => B.box.chart q.2) (univ ×ˢ B.box.chart.source) :=
    hB.forward.comp contMDiffOn_snd (fun q hq => hq.2)
  have hmap : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,P × Plane) ∞
      (fun q : P × M => (q.1,B.box.chart q.2)) (univ ×ˢ B.box.chart.source) :=
    (contMDiffOn_prod_module_iff _).mpr ⟨contMDiffOn_fst,hsnd⟩
  intro q
  by_cases hq : q.2 ∈ B.box.chart.source
  · apply ContMDiffAt.congr_of_eventuallyEq
      (hraw.contMDiff.contMDiffAt.comp q (hmap.contMDiffAt
        ((isOpen_univ.prod B.box.chart.open_source).mem_nhds ⟨mem_univ _,hq⟩)))
    filter_upwards [(isOpen_univ.prod B.box.chart.open_source).mem_nhds ⟨mem_univ q.1,hq⟩] with w hw
    exact if_pos hw.2
  · have hqK : q.2 ∉ B.box.compactCarrier := by
      rintro ⟨z,hz,hze⟩
      rw [← hze] at hq
      exact hq (B.box.chart.map_target (B.box.closed_subset hz))
    apply (contMDiffAt_const (c := (0:E →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_univ.prod B.box.compactCarrier_compact.isClosed.isOpen_compl).mem_nhds
      ⟨mem_univ q.1,hqK⟩] with w hw
    exact hz w.1 w.2 hw.2

theorem formPrimitive_family_smooth
    (hB : B.box.Smooth) (hsB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.box.carrier)
    (hz : ∀ p x, x ∉ K → Ω p x = 0) (hm : ∀ p, B.mass (Ω p) = 0) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => B.formPrimitive (Ω q.1) q.2) := by
  let f : P × Plane → ℝ := fun q => B.coefficient (Ω q.1) q.2
  have hf : ContDiff ℝ ∞ f :=
    B.coefficient_family_smooth hB hsB hΩ hK (fun x hx => (hKB hx).1) hz
  have hzero : ∀ p x y, B.box.radius ≤ |x-B.box.point.1| ∨ B.box.radius ≤ |y-B.box.point.2| →
      f (p,(x,y)) = 0 := fun p x y hh => B.coefficient_face_zero hKB (hz p) x y hh
  have hmass : ∀ p, (∫ z, f (p,z) ∂SymplecticPacking.Explicit.planeVolume) = 0 := hm
  change ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
    (fun q : P × M => B.primitive (fun z => f (q.1,z)) q.2)
  exact B.primitive_family_smooth hB hf hzero hmass

end RawAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
