import SymplecticPacking.HighDim.Handle.QuadricRawAnnularSpec

/-!
# Smoothness of the native annular normalization

Smoothness of the period and of the native annular normalization, and the normalization
specification, proved through the semantic identity of the gauge.
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

theorem period_contDiff
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x) :
    ContDiff ℝ ∞ (period m (Γ-N)) := by
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
  have he : period m (Γ-N)=cylinderFormPeriod 0
      (annularDifference H (fun p => semanticOneForm Subtype.val (Γ p))
        (fun p => semanticOneForm Subtype.val (N p))) := by
    funext p
    rw [period_eq,semanticCylinder_difference]
  rw [he]
  exact contDiffOn_univ.mp hpot.2.1

theorem normalize_contMDiff {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x)
    (hΓraw : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => Γ q.1 q.2)) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => normalize m b Γ N q.1 q.2) := by
  have ha : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × Surface m => period m (Γ-N) q.1) :=
    (period_contDiff m hΓ hN hcurv).contMDiff.comp contMDiff_fst
  have hβ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,Affine (m+2) →L[ℝ] ℝ) ∞
      (fun q : P × Surface m => QuadricRawDual.actualDual m q.2.val) :=
    (QuadricRawDual.actualDual_contMDiff m).comp contMDiff_snd
  exact (hΓraw.sub (ha.smul hβ)).sub (gaugeCovector_contMDiff m hbw hΓ hN hcurv)

theorem normalize_spec {b : ℝ} (hbw : b<(BranchSmall.quadricHandleData m).width)
    {Γ N : P → Surface m → Affine (m+2) →L[ℝ] ℝ}
    (hΓ : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (Γ p)))
    (hN : SmoothOneFormFamily (fun p => semanticOneForm Subtype.val (N p)))
    (hcurv : ∀ p x,x∈(BranchSmall.quadricHandleData m).chart.target →
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x=
        manifoldExteriorOneForm (semanticOneForm Subtype.val (N p)) x) :
    (∀ p x, manifoldExteriorOneForm (semanticOneForm Subtype.val (normalize m b Γ N p)) x=
      manifoldExteriorOneForm (semanticOneForm Subtype.val (Γ p)) x) ∧
    (∀ p x,x∈annularNormalizeRegion (BranchSmall.quadricHandleData m) b →
      semanticOneForm Subtype.val (normalize m b Γ N p) x=semanticOneForm Subtype.val (N p) x) := by
  have hNat (p : P) (x : Surface m) (_ : x∈(BranchSmall.quadricHandleData m).chart.target) :
      ContDiffAt ℝ ∞ (fun q : P × Plane => chartOneForm (semanticOneForm Subtype.val (N q.1)) x q.2)
        (p,extChartAt 𝓘(ℝ,Plane) x x) :=
    (hN x).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target x)).mem_nhds
      ⟨mem_univ _,mem_extChartAt_target x⟩)
  have hs := annularNormalizeOf_spec (BranchSmall.quadricHandleData m) hbw hΓ hNat hcurv
  constructor
  · intro p x
    rw [normalize_pullback m hbw hΓ hN hcurv]
    exact hs.2.2.1 p x
  · intro p x hx
    rw [normalize_pullback m hbw hΓ hN hcurv]
    exact hs.2.2.2 p x hx

end SymplecticPacking.HighDim.ToricPackingStages.QuadricRawAnnular
