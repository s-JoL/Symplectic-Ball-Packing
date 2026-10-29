import SymplecticPacking.HighDim.Handle.QuadricRawAnnularGauge

/-!
# Semantic identification of the native annular normalization

Exact semantic identification of the native annular normalization formula.
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

theorem semanticGauge_zero {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    (Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ) (p : P) (x : Surface m)
    (hx : x∉(BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band (cutWidth (cutWidth b))) :
    semanticGauge m b Γ N (p,x)=0 := by
  have hi : annularCutWidth (BranchSmall.quadricHandleData m) b<(BranchSmall.quadricHandleData m).width := by
    dsimp [annularCutWidth]
    linarith
  unfold semanticGauge
  rw [annularCutoff_zero (BranchSmall.quadricHandleData m) hi x (by simpa only [cutWidth_eq m] using hx),zero_mul]

theorem gaugeCovector_pullback_inside {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x)
    (p : P) (x : Surface m) (hx : x∈(BranchSmall.quadricHandleData m).chart.target) :
    manifoldScalarDifferential (E := Plane) (fun y => semanticGauge m b Γ N (p,y)) x=
      (gaugeCovector m b (Γ-N) p x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) := by
  have hf : ContDiffAt ℝ ∞ (coordinateGauge m b (Γ-N) p)
      (QuadricRawDual.transverseProjection m x.val) :=
    (coordinateGauge_contDiffAt m hbw hΓ hN hcurv p x hx).comp
    (QuadricRawDual.transverseProjection m x.val) (contDiffAt_const.prodMk contDiffAt_id)
  have hi := (real_inclusion_contMDiff (parameters m)).contMDiffAt (x := x)
  have hP := (QuadricRawDual.transverseProjection m).contDiff.contMDiff.contMDiffAt.comp x hi
  have hD := mfderiv_comp x (hf.contMDiffAt.mdifferentiableAt (by simp)) (hP.mdifferentiableAt (by simp))
  have hD2 := mfderiv_comp x (QuadricRawDual.transverseProjection m).hasFDerivAt.differentiableAt.mdifferentiableAt
    (hi.mdifferentiableAt (by simp))
  have hlocal : (fun y => semanticGauge m b Γ N (p,y)) =ᶠ[𝓝 x]
      coordinateGauge m b (Γ-N) p ∘ ((QuadricRawDual.transverseProjection m) ∘
        (Subtype.val : Surface m → Affine (m+2))) := by
    filter_upwards [(BranchSmall.quadricHandleData m).chart.open_target.mem_nhds hx] with y hy
    exact (coordinateGauge_eq m b Γ N p y hy).symm
  have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (fun y => semanticGauge m b Γ N (p,y)) x =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ)
        (coordinateGauge m b (Γ-N) p ∘ ((QuadricRawDual.transverseProjection m) ∘
          (Subtype.val : Surface m → Affine (m+2)))) x := hlocal.mfderiv_eq
  unfold manifoldScalarDifferential
  rw [hd,hD,hD2,gaugeCovector,if_pos ((QuadricRawDensity.nativeSheet_iff m x).mpr hx)]
  simp only [mfderiv_eq_fderiv,(QuadricRawDual.transverseProjection m).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem gaugeCovector_pullback {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x)
    (p : P) (x : Surface m) :
    manifoldScalarDifferential (E := Plane) (fun y => semanticGauge m b Γ N (p,y)) x=
      (gaugeCovector m b (Γ-N) p x.val).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x) := by
  by_cases hx : x∈(BranchSmall.quadricHandleData m).chart.target
  · exact gaugeCovector_pullback_inside m hbw hΓ hN hcurv p x hx
  · have ho : cutWidth (cutWidth b)<(BranchSmall.quadricHandleData m).width := by
      simp only [cutWidth_eq m]
      dsimp [annularCutWidth]
      linarith
    have hn : x∉(BranchSmall.quadricHandleData m).chart '' AnnularHandleData.band (cutWidth (cutWidth b)) :=
      fun h => hx ((BranchSmall.quadricHandleData m).image_band_subset_target ho h)
    have he : (fun y => semanticGauge m b Γ N (p,y)) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [((BranchSmall.quadricHandleData m).image_band_compact ho).isClosed.isOpen_compl.mem_nhds hn]
        with y hy
      exact semanticGauge_zero m hbw Γ N p y hy
    have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (fun y => semanticGauge m b Γ N (p,y)) x = 0 := by
      calc
        _ = mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) (fun _ : Surface m => (0:ℝ)) x := he.mfderiv_eq
        _ = 0 := mfderiv_const
    rw [manifoldScalarDifferential,hd,gaugeCovector_zero m hbw (Γ-N) p x hn,
      ContinuousLinearMap.zero_comp]

theorem normalize_pullback {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x) (p : P) :
    semanticOneForm (Subtype.val : Surface m → Affine (m+2)) (normalize m b Γ N p)=
      annularNormalizeOf (BranchSmall.quadricHandleData m) b
        (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p)) p := by
  have ha : period m (Γ-N) p=cylinderFormPeriod 0
      (annularDifference (BranchSmall.quadricHandleData m)
        (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p))) p := by
    rw [period_eq,semanticCylinder_difference]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hG := congrArg (fun A : Plane →L[ℝ] ℝ => A v) (gaugeCovector_pullback m hbw hΓ hN hcurv p x)
  have hβ := congrArg (fun A : Plane →L[ℝ] ℝ => A v) (QuadricRawDual.correctedDual_pullback m x)
  change (BranchSmall.quadricHandleData m).dual x v=
    QuadricRawDual.actualDual m x.val
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2)) (Subtype.val : Surface m → Affine (m+2)) x v) at hβ
  change Γ p x _-period m (Γ-N) p*QuadricRawDual.actualDual m x.val _-gaugeCovector m b (Γ-N) p x.val _=
    Γ p x _-cylinderFormPeriod 0 (annularDifference (BranchSmall.quadricHandleData m)
      (fun p => semanticOneForm Subtype.val (Γ p)) (fun p => semanticOneForm Subtype.val (N p))) p*
        (BranchSmall.quadricHandleData m).dual x v-
      manifoldScalarDifferential (E := Plane) (fun y => semanticGauge m b Γ N (p,y)) x v
  rw [ha,hβ,hG]
  rfl

end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
