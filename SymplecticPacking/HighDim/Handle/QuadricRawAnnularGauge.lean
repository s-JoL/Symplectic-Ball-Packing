import SymplecticPacking.HighDim.Handle.QuadricRawAnnularSmooth

/-!
# Smoothness of the native annular gauge covector

Joint smoothness and compact support of the native annular gauge covector.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
open Set Function Filter Manifold
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem spatialGradient_contDiffOn {F : P × Plane → ℝ} {V : Set (P × Plane)}
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F V) :
    ContDiffOn ℝ ∞ (fun q : P × Plane => fderiv ℝ (fun z => F (q.1,z)) q.2) V := by
  intro q hq
  have hD := (hF.contDiffAt (hV.mem_nhds hq)).fderiv_right (m := ∞) (by simp)
  have hJ := hD.clm_comp (contDiffAt_const
    (c := ((0 : Plane →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Plane))))
  apply (hJ.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hV.mem_nhds hq] with z hz
  exact joint_scalar_fderiv_slice ((hF.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))

variable (m : ℕ)

theorem gaugeCovector_zero {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    (δ : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (x : Surface m)
    (hx : x∉(BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band (cutWidth (cutWidth b))) :
    gaugeCovector m b δ p x.val=0 := by
  have hw : (BranchSmall.quadricHandleData m).width=(1:ℝ)/8 := by
    change BranchSmall.explicitCylinderWidth m/2=1/8
    norm_num [BranchSmall.explicitCylinderWidth]
  have hbc : cutWidth b<cutWidth (cutWidth b) := by
    rw [hw] at hbw
    unfold cutWidth
    linarith
  by_cases ht : QuadricRawDensity.nativeSheet m x.val
  · have hxt := (QuadricRawDensity.nativeSheet_iff m x).mp ht
    let z := QuadricRawDual.transverseProjection m x.val
    let r : Plane → ℝ := fun u => Real.log ‖Complex.equivRealProdCLM.symm u‖
    have hrx : r z=((BranchSmall.quadricHandleData m).chart.symm x).1 :=
      congrArg Prod.fst (QuadricRawDual.transverseProjection_symm m x)
    have hn : r z∉Icc (-cutWidth (cutWidth b)) (cutWidth (cutWidth b)) := by
      rw [hrx]
      exact (BranchSmall.quadricHandleData m).off_band_inverse _ hxt hx
    have hnz : Complex.equivRealProdCLM.symm z≠0 := transverseCoordinate_ne_zero m x.property
    have hr : ContinuousAt r z := ((contDiffAt_norm ℝ (n := ∞) hnz).log
      (norm_ne_zero_iff.mpr hnz)).continuousAt.comp Complex.equivRealProdCLM.symm.continuous.continuousAt
    have hloc : coordinateGauge m b δ p =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
      filter_upwards [hr (isClosed_Icc.isOpen_compl.mem_nhds hn)] with u hu
      change intervalPlateau (cutWidth b) (cutWidth (cutWidth b)) (r u) * _=0
      rw [intervalPlateau_zero hbc hu,zero_mul]
    have hd : fderiv ℝ (coordinateGauge m b δ p) z=0 := by
      rw [hloc.fderiv_eq,fderiv_const_apply]
    dsimp only [z] at hd
    simp only [gaugeCovector,if_pos ht,hd,ContinuousLinearMap.zero_comp]
  · exact if_neg ht

theorem gaugeCovector_contMDiff {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => gaugeCovector m b (Γ-N) q.1 q.2.val) := by
  intro q
  by_cases hx : q.2∈(BranchSmall.quadricHandleData m).chart.target
  · let d := transverseDiffeomorph m
    let U := d.source ∩ d ⁻¹' (BranchSmall.quadricHandleData m).chart.target
    have hU : IsOpen U := d.contMDiffOn.continuousOn.isOpen_inter_preimage d.open_source
      (BranchSmall.quadricHandleData m).chart.open_target
    have hxt : q.2∈d.target := by
      rw [transverseDiffeomorph_target]
      exact (QuadricRawDual.transverseCylinder_target m q.2).mp hx.1
    have hz : QuadricRawDual.transverseProjection m q.2.val∈d.source := d.map_target hxt
    have he : d (QuadricRawDual.transverseProjection m q.2.val)=q.2 := d.right_inv hxt
    have hzU : QuadricRawDual.transverseProjection m q.2.val∈U := by
      refine ⟨hz,?_⟩
      change d (QuadricRawDual.transverseProjection m q.2.val)∈(BranchSmall.quadricHandleData m).chart.target
      rw [he]
      exact hx
    have hF : ContDiffOn ℝ ∞ (fun z : P × Plane => coordinateGauge m b (Γ-N) z.1 z.2) (univ ×ˢ U) := by
      intro z hz'
      have h := coordinateGauge_contDiffAt m hbw hΓ hN hcurv z.1 (d z.2) hz'.2.2
      have hp : QuadricRawDual.transverseProjection m (d z.2).val=z.2 := d.left_inv hz'.2.1
      simpa only [hp] using h.contDiffWithinAt
    have hgrad := (spatialGradient_contDiffOn (isOpen_univ.prod hU) hF).contDiffAt
      ((isOpen_univ.prod hU).mem_nhds (show (q.1,QuadricRawDual.transverseProjection m q.2.val)∈univ ×ˢ U from
        ⟨mem_univ _,hzU⟩))
    have hP := (QuadricRawDual.transverseProjection m).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m))
    have hmap : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,P × Plane) ∞
        (fun z : P × Surface m => (z.1,QuadricRawDual.transverseProjection m z.2.val)) :=
      contMDiff_fst.prodMk_space (hP.comp contMDiff_snd)
    have hs := (hgrad.contMDiffAt.comp q hmap.contMDiffAt).clm_comp
      (contMDiffAt_const (c := QuadricRawDual.transverseProjection m))
    apply hs.congr_of_eventuallyEq
    filter_upwards [(isOpen_univ.prod (BranchSmall.quadricHandleData m).chart.open_target).mem_nhds
      (show q∈univ ×ˢ (BranchSmall.quadricHandleData m).chart.target from ⟨mem_univ _,hx⟩)] with z hz'
    exact if_pos ((QuadricRawDensity.nativeSheet_iff m z.2).mpr hz'.2)
  · have hi : annularCutWidth (BranchSmall.quadricHandleData m) b<(BranchSmall.quadricHandleData m).width := by
      dsimp [annularCutWidth]
      linarith
    have ho : cutWidth (cutWidth b)<(BranchSmall.quadricHandleData m).width := by
      simp only [cutWidth_eq m]
      dsimp [annularCutWidth]
      linarith
    have hnot : q.2∉(BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band (cutWidth (cutWidth b)) :=
      fun h => hx ((BranchSmall.quadricHandleData m).image_band_subset_target ho h)
    apply (contMDiffAt_const (c := (0 : Affine (m+2) →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_univ.prod ((BranchSmall.quadricHandleData m).image_band_compact ho).isClosed.isOpen_compl).mem_nhds
      (show q∈univ ×ˢ ((BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band (cutWidth (cutWidth b)))ᶜ from
        ⟨mem_univ _,hnot⟩)] with z hz'
    exact gaugeCovector_zero m hbw (Γ-N) z.1 z.2 hz'.2

end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
