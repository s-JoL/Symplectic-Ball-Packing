import SymplecticPacking.HighDim.Handle.RawCoordinateBox

/-!
# Finite partitions of unity from raw boxes

Fixed finite partitions using explicit chart data.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
namespace RawBoxFamily
variable {M : Type} [TopologicalSpace M] [T2Space M] {I : Type} [Fintype I]
variable (B : I → RawCoordinateBox M)

/-- A finite sum of fixed coordinate weights. -/
def weightSum (x : M) : ℝ := ∑ i, RawCoordinateBox.weight (B i) x

theorem weightSum_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : ∀ i, (B i).Smooth) : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ (weightSum B) :=
  ContMDiff.sum fun i _ => RawCoordinateBox.weight_smooth (B i) (hB i)

theorem weightSum_nonneg (x : M) : 0 ≤ (weightSum B) x :=
  Finset.sum_nonneg fun i _ => RawCoordinateBox.weight_nonneg (B i) x

/-- The additional term keeps the denominator positive off the covered compact set. -/
def partitionDenom (x : M) : ℝ :=
  (weightSum B) x + Real.smoothTransition (1 - (weightSum B) x)

theorem partitionDenom_pos (x : M) : 0 < (partitionDenom B) x := by
  by_cases hp : 0 < (weightSum B) x
  · exact add_pos_of_pos_of_nonneg hp (Real.smoothTransition.nonneg _)
  · have hz : (weightSum B) x = 0 := le_antisymm (le_of_not_gt hp) ((weightSum_nonneg B) x)
    simp [partitionDenom, hz, Real.smoothTransition.one]

theorem partitionDenom_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : ∀ i, (B i).Smooth) : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ (partitionDenom B) :=
  (weightSum_smooth B hB).add
    (Real.smoothTransition.contDiff.contMDiff.comp
      (contMDiff_const.sub (weightSum_smooth B hB)))

/-- Every partition coefficient is a displayed quotient of fixed functions. -/
def partitionWeight (i : I) (x : M) : ℝ :=
  RawCoordinateBox.weight (B i) x / (partitionDenom B) x

theorem partitionWeight_smooth [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : ∀ i, (B i).Smooth) (i : I) :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ ((partitionWeight B) i) :=
  (RawCoordinateBox.weight_smooth _ (hB i)).div₀ (partitionDenom_smooth B hB) (fun x => ((partitionDenom_pos B) x).ne')

theorem weightSum_cover {K : Set M} (hcover : K ⊆ ⋃ i, RawCoordinateBox.inner (B i))
    (x : M) (hx : x ∈ K) : 1 ≤ (weightSum B) x := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  have hh : RawCoordinateBox.weight (B i) x ≤ (weightSum B) x :=
    Finset.single_le_sum (fun j _ => RawCoordinateBox.weight_nonneg (B j) x) (Finset.mem_univ i)
  rwa [RawCoordinateBox.weight_one (B i) x hi] at hh

/-- The finite partition produced solely from the coordinate boxes and their inner
cover certificate. No smooth functions or primitive operators are supplied as input data. -/
def partition [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hB : ∀ i, (B i).Smooth) {K : Set M} (hcover : K ⊆ ⋃ i, RawCoordinateBox.inner (B i)) :
    SmoothPartitionOfUnity (I) 𝓘(ℝ, Plane) M K where
  toFun i := ⟨(partitionWeight B) i, partitionWeight_smooth B hB i⟩
  locallyFinite' := locallyFinite_of_finite _
  nonneg' i x := div_nonneg (RawCoordinateBox.weight_nonneg _ _) ((partitionDenom_pos B) x).le
  sum_eq_one' x hx := by
    change (∑ᶠ i, RawCoordinateBox.weight (B i) x / (partitionDenom B) x) = 1
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_div]
    have hge := (weightSum_cover B) hcover x hx
    change (weightSum B) x / (partitionDenom B) x = 1
    have hd : (partitionDenom B) x = (weightSum B) x := by
      rw [partitionDenom, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hge), add_zero]
    rw [hd, div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one hge))]
  sum_le_one' x := by
    change (∑ᶠ i, RawCoordinateBox.weight (B i) x / (partitionDenom B) x) ≤ 1
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_div]
    apply (div_le_one ((partitionDenom_pos B) x)).2
    exact le_add_of_nonneg_right (Real.smoothTransition.nonneg _)

end RawBoxFamily
end SymplecticPacking.HighDim.ToricPackingStages
