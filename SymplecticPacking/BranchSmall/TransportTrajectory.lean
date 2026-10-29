import SymplecticPacking.BranchSmall.TransportPositiveTrajectory
import SymplecticPacking.BranchSmall.TransportInitial
import SymplecticPacking.BranchSmall.TransportGlue
import SymplecticPacking.BranchSmall.TransportConservation

/-!
# Complete horizontal transport from the central curve

A short regular segment at the central fibre is followed by the complete
logarithmic-time graph flow. Reflection invariance preserves the zero pattern.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff

/-- Every central-fibre point admits a complete horizontal trajectory on `[0,1]`. -/
theorem transport_trajectory_complete (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx1 : x.1 ∈ locus (parameters m)) :
    ∃ γ : ℝ → Tot (m + 2), γ 0 = radialInj b x.1 (toC x.2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ goodSet (m + 2)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (transportField (parameters m) b s (γ s)) (Icc 0 1) s := by
  let y : Tot (m + 2) := radialInj b x.1 (toC x.2)
  have hy0 : y ∈ goodSet (m + 2) := mem_goodSet_of_mem_locus m hx1
  obtain ⟨δ, γ₀, hδ0, hδ1, hγ₀smooth, hγ₀0, hγ₀⟩ := exists_smooth_initial_segment
    (isOpen_goodSet (m + 2)) (transportField_contDiffOn (parameters m) hb0 hb) y hy0
  have hzero : equations (parameters m) (γ₀ 0).1 = 0 := by
    rw [hγ₀0]
    change equations (parameters m) x.1 = 0
    simpa only [locus, Set.mem_preimage, Set.mem_singleton_iff] using hx1
  have hgraph : equations (parameters m) (γ₀ δ).1 = (δ : ℂ) • (γ₀ δ).2 :=
    graph_along_trajectory_Icc (parameters m) hb0 hb hzero
      (fun s hs => (hγ₀ s hs).1) (fun s hs => (hγ₀ s hs).2.hasDerivWithinAt)
      ⟨hδ0.le, le_rfl⟩
  obtain ⟨γ₁, hγ₁δ, hγ₁⟩ := exists_positive_transport_segment (parameters m) hb0 hb hδ0 hδ1
    (γ₀ δ) (hγ₀ δ ⟨hδ0.le, le_rfl⟩).1 hgraph
  let γ := glueTrajectory δ γ₀ γ₁
  have hfg : γ₀ δ = γ₁ δ := hγ₁δ.symm
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [show γ 0 = γ₀ 0 from glueTrajectory_left hδ0.le, hγ₀0]
  · intro s hs
    by_cases hsδ : s ≤ δ
    · rw [show γ s = γ₀ s from glueTrajectory_left hsδ]
      exact (hγ₀ s ⟨hs.1, hsδ⟩).1
    · rw [show γ s = γ₁ s from glueTrajectory_right hfg (not_le.mp hsδ).le]
      exact (hγ₁ s ⟨(not_le.mp hsδ).le, hs.2⟩).1
  · exact glueTrajectory_hasDerivWithinAt hδ0.le hδ1.le hfg
      (fun s hs => (hγ₀ s hs).2.hasDerivWithinAt)
      (fun s hs => (hγ₁ s hs).2.hasDerivWithinAt)

/-- Complete transport for the radial-tube interface. -/
theorem transport_trajectory (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx1 : x.1 ∈ locus (parameters m))
    (hx2 : Real.pi * wsq (toC x.2) < b) :
    ∃ γ : ℝ → Tot (m + 2), γ 0 = radialInj b x.1 (toC x.2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ goodSet (m + 2)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (transportField (parameters m) b s (γ s)) (Icc 0 1) s := by
  exact transport_trajectory_complete m hb0 hb x hx1

/-- **Transport, local control** (prop:vtr-transport (c)–(e)), assembled
from the generic cutoff lemma and the two analytic inputs. -/
theorem transport_control_of_inputs (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx1 : x.1 ∈ locus (parameters m))
    (hx2 : Real.pi * wsq (toC x.2) < b) :
    LocalControl (transportField (parameters m) b) (radialInj b x.1 (toC x.2)) := by
  obtain ⟨γ, hγ0, hγO, hγ⟩ := transport_trajectory m hb0 hb x hx1 hx2
  exact localControl_of_contDiffOn (isOpen_goodSet (m + 2))
    (transportField_contDiffOn (parameters m) hb0 hb) hγ0 hγO hγ

end SymplecticPacking.BranchSmall.VT
