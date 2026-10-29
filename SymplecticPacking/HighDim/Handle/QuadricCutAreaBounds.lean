import SymplecticPacking.HighDim.Handle.QuadricCutMass
import SymplecticPacking.HighDim.Handle.RawSurfaceIntrinsicMass

/-!
# Area retained by the quadric collar cutoff

The collar cutoff retains at least the full area of its inner core.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology Manifold

section CutoffIntegral
variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

theorem cutoff_integral_le_outer {K L : Set M} (hK : IsCompact K)
    (hor : PositivePlaneTransitions M) (hKL : K ⊆ L)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsk : ∀ x u v, Λ x u v = -Λ x v u)
    (hpos : ∀ c y, y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0≤chartTwoForm Λ c y (1,0) (0,1))
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ χ)
    (hχ1 : ∀ x, χ x≤1) (hχz : ∀ x,x∉K → χ x=0) :
    partitionFormMass Boxes ρ (fun x => χ x • Λ x) ≤ compactSurfaceFormIntegral hK Λ := by
  rw [compactSurfaceFormIntegral_eq_setIntegral hK hor hKL Boxes ρ hρ hΛ hsk hpos,
    ← integral_partitionAreaMeasure Boxes ρ hρ hΛ hpos hχ]
  calc
    (∫ x,χ x ∂partitionAreaMeasure Boxes ρ Λ) =
        ∫ x in K,χ x ∂partitionAreaMeasure Boxes ρ Λ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hχz).symm
    _ ≤ _ := integral_mono
      (smooth_integrable_partitionAreaMeasure Boxes ρ hρ hΛ hpos hχ).integrableOn
      (smooth_integrable_partitionAreaMeasure Boxes ρ hρ hΛ hpos
        (contMDiff_const (c := (1:ℝ)))).integrableOn
      hχ1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem cutoff_weighted_mass_ge_inner {K L J : Set M} (hK : IsCompact K)
    (hor : PositivePlaneTransitions M) (hKL : K⊆L)
    {I : Type} [Fintype I] (Boxes : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsk : ∀ x u v,Λ x u v = -Λ x v u)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0≤chartTwoForm Λ c y (1,0) (0,1))
    {χ κ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ χ)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ)
    (hχ0 : ∀ x,0≤χ x) (hχ1 : ∀ x∈K,χ x=1)
    (hχz : ∀ x,x∉J → χ x=0) (hκ0 : ∀ x∈J,0≤κ x) :
    compactSurfaceFormIntegral hK (fun x => κ x • Λ x) ≤
      partitionFormMass Boxes ρ (fun x => (χ x*κ x) • Λ x) := by
  have hκΛ := ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hκ).eval 0
  have hs (x : M) (u v : Plane) : (fun x => κ x • Λ x) x u v = -(fun x => κ x • Λ x) x v u := by
    change κ x*Λ x u v = -(κ x*Λ x v u)
    rw [hsk x u v]
    ring
  rw [compactSurfaceFormIntegral_eq_larger_partition hK hor hKL Boxes ρ hρ hκΛ hs,
    ← integral_partitionAreaMeasure_restrict Boxes ρ hρ hΛ hpos hK.measurableSet hκ,
    ← integral_partitionAreaMeasure Boxes ρ hρ hΛ hpos (f := fun x => χ x*κ x) (hχ.mul hκ)]
  calc
    (∫ x in K,κ x ∂partitionAreaMeasure Boxes ρ Λ) =
        ∫ x in K,χ x*κ x ∂partitionAreaMeasure Boxes ρ Λ :=
      setIntegral_congr_fun hK.measurableSet (fun x hx => by rw [hχ1 x hx,one_mul])
    _ ≤ _ := setIntegral_le_integral
      (smooth_integrable_partitionAreaMeasure Boxes ρ hρ hΛ hpos (hχ.mul hκ))
      (Filter.Eventually.of_forall (by
        intro x
        change (0:ℝ)≤χ x*κ x
        by_cases hx : x∈J
        · exact mul_nonneg (hχ0 x) (hκ0 x hx)
        · rw [hχz x hx,zero_mul]))
end CutoffIntegral

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a

end SymplecticPacking.HighDim.ToricPackingStages
