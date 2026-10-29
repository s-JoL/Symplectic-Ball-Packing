import SymplecticPacking.HighDim.Transport
import OAI.Geometry.BallPacking.Flows.NonautonomousManifoldFlow

/-!
# Assembly (paper prop:mech-assembly)

Packing maps `ψ_i` into a model `(X, Ω)` followed by one transfer `g : X → ℂ^{m+1}`, smooth and
an embedding on an open `T ⊇ ψ_i(B(ρ''_i))` with `g^*ω₀ = Ω` and `g(T) ⊆ B°(C)`, give an
`AmbientPacking` with enlarged capacities `ρ'_i` and domains `ρ''_i`. Disjointness of the
images follows because `g` is one injective map.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Manifold
open OAI.PackingSufficiencySupport (Ambient closedBall openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {X : Type*} [TopologicalSpace X] [ChartedSpace EX X]

theorem closedBall_mono {n : ℕ} {r s : ℝ} (h : r ≤ s) : closedBall n r ⊆ closedBall n s :=
  fun _ hz => le_trans hz h

/-- **prop:mech-assembly.** -/
theorem assembly_spec {m k : ℕ} {Ω : ManifoldTwoForm EX X} {φ : Fin k → Ambient (m + 1) → X}
    {g : X → Ambient (m + 1)} {T : Set X} {C : ℝ} {c ρ' ρ'' : Fin k → ℝ}
    (hφ : ∀ i, FormNeighborhoodEmbedding (closedBall (m + 1) (ρ'' i))
      (fun _ => successorStandardForm m) Ω (φ i))
    (hφT : ∀ i, MapsTo (φ i) (closedBall (m + 1) (ρ'' i)) T)
    (hdisj : Pairwise (fun i j => Disjoint (φ i '' closedBall (m + 1) (ρ'' i))
      (φ j '' closedBall (m + 1) (ρ'' j))))
    (hT : IsOpen T) (hg : ContMDiffOn 𝓘(ℝ, EX) 𝓘(ℝ, Ambient (m + 1)) ∞ g T)
    (hgemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hgform : ∀ x ∈ T, ∀ v w, successorStandardForm m
      (mfderiv 𝓘(ℝ, EX) 𝓘(ℝ, Ambient (m + 1)) g x v)
      (mfderiv 𝓘(ℝ, EX) 𝓘(ℝ, Ambient (m + 1)) g x w) = Ω x v w)
    (hgC : ∀ x ∈ T, g x ∈ openBall (m + 1) C)
    (hc : ∀ i, c i < ρ' i) (hρ : ∀ i, ρ' i < ρ'' i) :
    (AmbientPacking.mk (fun i => g ∘ φ i) ρ' ρ'').Spec C c := by
  obtain ⟨hf, hdj⟩ := postcompose_form_packing (fun i => closedBall (m + 1) (ρ'' i))
    (fun _ => successorStandardForm m) Ω (fun _ => successorStandardForm m) hT g hg hgemb
    hgform φ hφ hφT hdisj
  refine ⟨hc, hρ, fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i), ?_, ?_⟩
  · intro i j hij
    exact (hdj hij).mono (image_mono (closedBall_mono (hρ i).le))
      (image_mono (closedBall_mono (hρ j).le))
  · rintro i _ ⟨x, hx, rfl⟩
    exact hgC _ (hφT i (closedBall_mono (hρ i).le hx))

end SymplecticPacking.HighDim
