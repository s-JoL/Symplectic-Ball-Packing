import SymplecticPacking.HighDim.Handle.LayerForm

/-!
# Auxiliary lemmas for the handle map

`image_trans_eq` (images under a composite of diffeomorphisms) and the boundary values
`layerClock_lo`, `layerClock_hi` of the explicit layer clocks `layerClock` of
`Handle/LayerForm.lean`, used by the explicit handle map `handleMapCut`
(`Handle/HandleMapSpec.lean`).
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

namespace ToricPackingStages

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ M] [T2Space M] [_root_.NormalSpace M] [SigmaCompactSpace M]
variable {m : ℕ}

/-- Images under a composite of diffeomorphisms. -/
theorem image_trans_eq {N : Type*} [TopologicalSpace N] [ChartedSpace ((ℝ × ℝ) × Fibre m) N]
    (e f : N ≃ₘ⟮𝓘(ℝ, (ℝ × ℝ) × Fibre m), 𝓘(ℝ, (ℝ × ℝ) × Fibre m)⟯ N) {S : Set N}
    (he : e '' S = S) (hf : f '' S = S) : (e.trans f) '' S = S := by
  have : ((e.trans f : N → N)) = f ∘ e := rfl
  rw [this, image_comp, he, hf]

/-- The explicit layer clocks on `k + 1` subintervals of `(−b, b)` vanish left of `−b`. -/
theorem layerClock_lo {k : ℕ} {b : ℝ} (hb : 0 < b) (i : Fin (k + 1)) {s : ℝ} (hs : s ≤ -b) :
    layerClock (k + 1) (-b) b i s = 0 := by
  have hab : -b < b := by linarith
  obtain ⟨hin, -, -, -, hcol⟩ := layerClocks_spec (k + 1) hab
  obtain ⟨δ, hδ, hz, -⟩ := hcol i
  exact hz s (by linarith [(hin i).1])

/-- The explicit layer clocks equal one right of `b`. -/
theorem layerClock_hi {k : ℕ} {b : ℝ} (hb : 0 < b) (i : Fin (k + 1)) {s : ℝ} (hs : b ≤ s) :
    layerClock (k + 1) (-b) b i s = 1 := by
  have hab : -b < b := by linarith
  obtain ⟨hin, -, -, -, hcol⟩ := layerClocks_spec (k + 1) hab
  obtain ⟨δ, hδ, -, ho⟩ := hcol i
  exact ho s (by linarith [(hin i).2.2])

end ToricPackingStages

end SymplecticPacking.HighDim
