import SymplecticPacking.BranchSmall.TransportGraph
import OAI.Geometry.BallPacking.Annuli.AnnularMean

/-!
# Conservation of the graph constraint

Conservation of the exact graph constraint on any initial time interval.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {q : ℕ}

/-- The defining constraint is conserved at every time, including the two endpoints. -/
theorem graph_along_trajectory_Icc (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {T : ℝ}
    {γ : ℝ → Tot q} (h0 : equations a (γ 0).1 = 0)
    (hγO : ∀ s ∈ Icc (0 : ℝ) T, γ s ∈ goodSet q)
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γ (transportField a b s (γ s)) (Icc 0 T) s)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    equations a (γ s).1 = (s : ℂ) • (γ s).2 := by
  let G : ℝ → (Fin q → ℂ) := fun t => equations a (γ t).1 - (t : ℂ) • (γ t).2
  have hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt G 0 (Icc 0 T) t := by
    intro t ht
    have h := hγ t ht
    have h1 : HasDerivWithinAt (fun t => (γ t).1) (transportField a b t (γ t)).1 (Icc 0 T) t :=
      (ContinuousLinearMap.fst ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivWithinAt t h
    have h2 : HasDerivWithinAt (fun t => (γ t).2) (transportField a b t (γ t)).2 (Icc 0 T) t :=
      (ContinuousLinearMap.snd ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivWithinAt t h
    have he := ((equations_hasFDerivAt a (γ t).1).restrictScalars ℝ).comp_hasDerivWithinAt t h1
    have hc : HasDerivWithinAt (fun t : ℝ => (t : ℂ)) ((1 : ℝ) : ℂ) (Icc 0 T) t :=
      (hasDerivAt_id t).ofReal_comp.hasDerivWithinAt
    have hlin := transportField_lin a hb0 hb t (hγO t ht)
    convert he.sub (hc.smul h2) using 1
    · funext t; rfl
    · rw [ContinuousLinearMap.coe_restrictScalars', Complex.ofReal_one, one_smul,
        ← sub_sub, hlin, sub_self]
  have hcont : ContinuousOn G (Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht => by
    exact (hd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))) s hs
  have he : G s = 0 := by
    rw [hconst]
    simp only [G, h0, Complex.ofReal_zero, zero_smul, sub_zero]
  exact sub_eq_zero.mp he

/-- The unit-time form used by the final transport. -/
theorem graph_along_trajectory (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {γ : ℝ → Tot q} (h0 : equations a (γ 0).1 = 0)
    (hγO : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ goodSet q)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt γ (transportField a b s (γ s)) (Icc 0 1) s)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    equations a (γ s).1 = (s : ℂ) • (γ s).2 :=
  graph_along_trajectory_Icc a hb0 hb h0 hγO hγ hs


end SymplecticPacking.BranchSmall.VT
