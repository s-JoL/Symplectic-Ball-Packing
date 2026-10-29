import SymplecticPacking.HighDim.Handle.QuadricRawAnnular

/-!
# Smoothness of the native annular gauge

Smoothness of the native annular gauge, proved through its semantic identity.
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
variable (m : ℕ) {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def semanticGauge (b : ℝ) (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (q : P × Surface m) : ℝ :=
  annularCutoff (BranchSmall.quadricHandleData m) (annularCutWidth (BranchSmall.quadricHandleData m) b) q.2 *
    annularPotential (BranchSmall.quadricHandleData m)
      (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p)) q

theorem semanticGauge_smooth {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (semanticGauge m b Γ N) := by
  let H := BranchSmall.quadricHandleData m
  have h0 : (0:ℝ)∈Ioo (-H.width) H.width := ⟨by linarith [H.width_pos],H.width_pos⟩
  have hNat (p : P) (x : Surface m) : ContDiffAt ℝ ∞
      (fun q : P × Plane => chartOneForm (semanticOneForm Subtype.val (N q.1)) x q.2)
      (p,extChartAt 𝓘(ℝ,Plane) x x) :=
    (hN x).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target x)).mem_nhds
      ⟨mem_univ _,mem_extChartAt_target x⟩)
  have hpot := annularPotential_spec
    (Γ := fun p => semanticOneForm Subtype.val (Γ p))
    (N := fun p => semanticOneForm Subtype.val (N p)) isOpen_univ isOpen_Ioo (convex_Ioo _ _) h0 H.chart H.source_eq
    hΓ (fun p _ x _ => hNat p x) (fun p _ x hx => hcurv p x hx)
    H.clock_smooth H.clock_integral H.dual_pullback
  have hi : annularCutWidth H b<H.width := by dsimp [annularCutWidth]; linarith
  have ho : annularCutWidth H (annularCutWidth H b)<H.width := by dsimp [annularCutWidth]; linarith
  have hχ := annularCutoff_smooth H hi
  have hχt : tsupport (annularCutoff H (annularCutWidth H b))⊆H.chart.target :=
    (annularCutoff_support H hi).trans (H.image_band_subset_target ho)
  have hg := manifoldFamily_local_potential_smoothOn isOpen_univ H.chart.open_target hpot.1 hχ hχt
  change ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (semanticGauge m b Γ N) (univ ×ˢ univ) at hg
  rw [univ_prod_univ] at hg
  exact contMDiffOn_univ.mp hg

theorem coordinateGauge_contDiffAt {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x)
    (p : P) (x : Surface m) (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    ContDiffAt ℝ ∞ (fun q : P × Plane => coordinateGauge m b (Γ-N) q.1 q.2)
      (p,QuadricRawDual.transverseProjection m x.val) := by
  let d := transverseDiffeomorph m
  let U := d.source ∩ d ⁻¹' (BranchSmall.quadricHandleData m).chart.target
  have hU : IsOpen U := d.contMDiffOn.continuousOn.isOpen_inter_preimage d.open_source
    (BranchSmall.quadricHandleData m).chart.open_target
  have hxt : x∈d.target := by
    have ht : x∈(transverseCylinder m).target := hx.1
    rw [transverseDiffeomorph_target]
    exact (QuadricRawDual.transverseCylinder_target m x).mp ht
  have hz : QuadricRawDual.transverseProjection m x.val∈d.source := d.map_target hxt
  have he : d (QuadricRawDual.transverseProjection m x.val)=x := d.right_inv hxt
  have hzU : QuadricRawDual.transverseProjection m x.val∈U := by
    refine ⟨hz,?_⟩
    change d (QuadricRawDual.transverseProjection m x.val)∈(BranchSmall.quadricHandleData m).chart.target
    rw [he]
    exact hx
  have hd := d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hz)
  have hmap : ContMDiffAt ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) ∞
      (fun q : P × Plane => (q.1,d q.2)) (p,QuadricRawDual.transverseProjection m x.val) :=
    contMDiffAt_fst.prodMk (hd.comp (p,QuadricRawDual.transverseProjection m x.val) contMDiffAt_snd)
  have hs := (semanticGauge_smooth m hbw hΓ hN hcurv).contMDiffAt.comp _ hmap
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hs
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(isOpen_univ.prod hU).mem_nhds (show (p,QuadricRawDual.transverseProjection m x.val)∈univ ×ˢ U from
    ⟨mem_univ _,hzU⟩)] with q hq
  have hp : QuadricRawDual.transverseProjection m (d q.2).val=q.2 := d.left_inv hq.2.1
  change coordinateGauge m b (Γ-N) q.1 q.2=semanticGauge m b Γ N (q.1,d q.2)
  calc
    _ = coordinateGauge m b (Γ-N) q.1 (QuadricRawDual.transverseProjection m (d q.2).val) :=
      congrArg (coordinateGauge m b (Γ-N) q.1) hp.symm
    _ = _ := coordinateGauge_eq m b Γ N q.1 (d q.2) hq.2.2

end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
