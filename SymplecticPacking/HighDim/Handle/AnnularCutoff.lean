import SymplecticPacking.HighDim.Handle.NormalPrimitivePotential

/-!
# A fixed cutoff on the handle annulus

A fixed compact cutoff on the handle annulus, avoiding arbitrary manifold bumps.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology

/-- Equal to one on [-b,b], with support in [-c,c]. -/
def intervalPlateau (b c s : ℝ) : ℝ :=
  Real.smoothTransition ((s+c)/(c-b)) * Real.smoothTransition ((c-s)/(c-b))

theorem intervalPlateau_smooth (b c : ℝ) : ContDiff ℝ ∞ (intervalPlateau b c) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem intervalPlateau_one {b c s : ℝ} (hbc : b < c) (hs : s ∈ Icc (-b) b) :
    intervalPlateau b c s = 1 := by
  unfold intervalPlateau
  rw [Real.smoothTransition.one_of_one_le (x := (s+c)/(c-b))
    ((one_le_div (sub_pos.mpr hbc)).2 (by linarith [hs.1])),
    Real.smoothTransition.one_of_one_le (x := (c-s)/(c-b))
    ((one_le_div (sub_pos.mpr hbc)).2 (by linarith [hs.2])), mul_one]

theorem intervalPlateau_zero {b c s : ℝ} (hbc : b < c) (hs : s ∉ Icc (-c) c) :
    intervalPlateau b c s = 0 := by
  unfold intervalPlateau
  rcases not_and_or.mp hs with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (x := (s+c)/(c-b))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hbc).le), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (c-s)/(c-b))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hbc).le), mul_zero]

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [T2Space M]

/-- The midpoint width leaves a fixed margin inside the supplied annular chart. -/
def annularCutWidth (D : AnnularHandleData Plane M) (b : ℝ) : ℝ := (b+D.width)/2

/-- The cutoff, with zero extension off the chart. -/
def annularCutoff (D : AnnularHandleData Plane M) (b : ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ D.chart.target then
    intervalPlateau b (annularCutWidth D b) (D.chart.symm x).1 else 0

theorem annularCutoff_zero (D : AnnularHandleData Plane M) {b : ℝ} (hbw : b < D.width)
    (x : M) (hx : x ∉ D.chart '' band (annularCutWidth D b)) : annularCutoff D b x = 0 := by
  unfold annularCutoff
  split_ifs with ht
  · apply intervalPlateau_zero (by dsimp [annularCutWidth]; linarith)
    intro hs
    exact hx ⟨D.chart.symm x, ⟨hs, mem_univ _⟩, D.chart.right_inv ht⟩
  · rfl

theorem annularCutoff_support (D : AnnularHandleData Plane M) {b : ℝ} (hbw : b < D.width) :
    tsupport (annularCutoff D b) ⊆ D.chart '' band (annularCutWidth D b) :=
  closure_minimal (fun x hx => by by_contra hn; exact hx (annularCutoff_zero D hbw x hn))
    (D.image_band_compact (b := annularCutWidth D b) (by dsimp [annularCutWidth]; linarith)).isClosed

theorem annularCutoff_smooth (D : AnnularHandleData Plane M) {b : ℝ} (hbw : b < D.width) :
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ (annularCutoff D b) := by
  apply contMDiff_of_tsupport
  intro x hx
  have ht : x ∈ D.chart.target :=
    D.image_band_subset_target (b := annularCutWidth D b)
      (by dsimp [annularCutWidth]; linarith) (annularCutoff_support D hbw hx)
  have hs := (annular_inverse_fst_smooth D.chart).contMDiffAt (D.chart.open_target.mem_nhds ht)
  apply ContMDiffAt.congr_of_eventuallyEq
    ((intervalPlateau_smooth b (annularCutWidth D b)).contMDiff.contMDiffAt.comp x hs)
  filter_upwards [D.chart.open_target.mem_nhds ht] with y hy
  exact if_pos hy

theorem annularCutoff_one (D : AnnularHandleData Plane M) {b : ℝ} (hbw : b < D.width)
    {x : M} (hx : x ∈ D.chart '' band b) : annularCutoff D b x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hzs := D.band_subset_source hbw hz
  unfold annularCutoff
  rw [if_pos (D.chart.map_source hzs)]
  apply intervalPlateau_one (by dsimp [annularCutWidth]; linarith)
  have he : (D.chart.symm (D.chart z)).1 = z.1 := congrArg Prod.fst (D.chart.left_inv hzs)
  exact he.symm ▸ hz.1

end SymplecticPacking.HighDim.ToricPackingStages
