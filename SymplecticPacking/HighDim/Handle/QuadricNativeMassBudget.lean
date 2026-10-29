import SymplecticPacking.HighDim.Handle.QuadricNormalizationMassBounds

/-!
# Mass budget of the quadric native model

The native handle mass obeys the collar budget; semantic ratios occur only in this proof.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
attribute [local irreducible] quadricModelRawPresentation quadricNormalizationMass surfaceFormRatio
local instance (m : ℕ) : SigmaCompactSpace (Surface m) := curveSigmaCompact _
variable (m ℓ : ℕ) {n : ℕ}

theorem quadricNormalizationMass_loss_of_tail {c reserve outer : ℝ}
    (hc : 0≤c) (hcb : c≤reserve/(32*(2:ℝ)^(m+2)))
    {Ω : Moments n → Surface m → Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ} (p : Moments n)
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine (m+2) →L[ℝ] Affine (m+2) →L[ℝ] ℝ) ∞ (Ω p))
    (hsk : ∀ x u v,Ω p x u v = -Ω p x v u)
    (hpos : ∀ x∈projectionDomain (parameters m) (quadricFiniteSupportRadius m ℓ:ℝ),
      0<chartTwoForm (semanticTwoForm Subtype.val (Ω p)) x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    (htail : outer-compactSurfaceFormIntegral
      (projectionDomain_compact (parameters m) (exhaustionRadius (parameters m) ℓ-2))
      (semanticTwoForm Subtype.val (Ω p))≤reserve/32) :
    outer-reserve/16≤quadricNormalizationMass m ℓ c Ω p := by
  let Λ := curveFSForm (parameters m) (1/Real.pi)
  let A := semanticTwoForm Subtype.val (Ω p)
  have hsA : ∀ x u v,A x u v = -A x v u := fun x u v => hsk x _ _
  have hpΛ : ∀ b y,y∈(extChartAt 𝓘(ℝ,Plane) b).target → 0<chartTwoForm Λ b y (1,0) (0,1) :=
    fun b y hy => curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) b hy
  have hΛ := curveFSForm_smooth (parameters m) (1/Real.pi)
  have hsΛ := curveFSForm_skew (parameters m) (1/Real.pi)
  have hA : SmoothTwoForm A := semanticTwoForm_smooth (real_inclusion_contMDiff _) hΩ
  have hratio : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × Surface m => surfaceFormRatio Λ A q.2) :=
    surfaceFormRatio_smooth (Λ := Λ) (Ω := fun _ : ℝ => A) hΛ hsΛ hpΛ
      (SmoothTwoFormFamily.const (P := ℝ) hA)
    (fun _ x u v => hsA x u v)
  have hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (surfaceFormRatio Λ A) :=
    hratio.comp ((contMDiff_const (c := (0:ℝ))).prodMk contMDiff_id)
  apply quadricNormalizationMass_loss m ℓ hc hcb p hΩ hsk (surfaceFormRatio Λ A) hκ
    (surface_form_scalar hsA hsΛ hpΛ)
  · intro x hx
    unfold surfaceFormRatio
    change 0≤chartTwoForm A x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) /
      chartTwoForm Λ x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)
    exact div_nonneg (hpos x hx).le (hpΛ x _ (mem_extChartAt_target x)).le
  · exact htail

end SymplecticPacking.HighDim.ToricPackingStages
