import SymplecticPacking.Strip.LayerMaps

/-!
# The three fibres of the normal bundle in the cover

`sec:str-embeddings` (`prop:shd4-maps`): the fibres `N_{b_j}` over the three points
`b_j = C ∩ {Z₀ = 0}` in the cover `E4` (`fibreSet`, all integer translates of the base points
`bpoints j`), and `not_mem_fibreSet`. The embeddings `f_i^N = Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i` for cubic data are
in `Branch2/Model/Cubic/Strip/Embed.lean`.
-/

noncomputable section

namespace SymplecticPacking.Strip

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc pull2 Form2)
open SymplecticPacking.Bundle (pE annulus bpoints)
open SymplecticPacking.Handle (OmegaFinal OmegaPre chartA chartInv DlamInv Dlam bandE)
open scoped ContDiff Real

/-! ### The three fibres -/

/-- **The fibres `N_{b_j}` over `b_j = C ∩ {Z₀ = 0}`**, `j = 1, 2, 3`, in the cover `E4`
(all integer translates of the base points `bpoints j`). -/
def fibreSet : Set E4 :=
  {X | ∃ j : Fin 3, ∃ m n : ℤ, X 2 = (bpoints j).1 + m ∧ X 3 = (bpoints j).2 + n}

/-- The annulus `𝒜` avoids the base points `b_j`. -/
theorem not_mem_fibreSet {X : E4} (hX : X 2 ∈ annulus) : X ∉ fibreSet := by
  rintro ⟨j, m, n, h2, -⟩
  obtain ⟨h1, h3⟩ := hX
  rw [h2] at h1 h3
  rcases Bundle.bpoints_fst j with h | h | h <;> rw [h] at h1 h3
  · have a : (0 : ℝ) < m := by linarith
    have b : (m : ℝ) < 1 := by linarith
    have a' : (0 : ℤ) < m := by exact_mod_cast a
    have b' : m < (1 : ℤ) := by exact_mod_cast b
    omega
  · have a : (-1 : ℝ) < m := by linarith
    have b : (m : ℝ) < 0 := by linarith
    have a' : (-1 : ℤ) < m := by exact_mod_cast a
    have b' : m < (0 : ℤ) := by exact_mod_cast b
    omega
  · have a : (-1 : ℝ) < m := by linarith
    have b : (m : ℝ) < 0 := by linarith
    have a' : (-1 : ℤ) < m := by exact_mod_cast a
    have b' : m < (0 : ℤ) := by exact_mod_cast b
    omega

variable (P : Params)

/-! ### `𝒟⁻¹` in global coordinates -/

/-- **`𝒟⁻¹` in the global frame**: `chartA ∘ 𝒟₁⁻¹` (local `𝒜⁺`-frame → global `Zunit`-frame). -/
def DinvN (Y : E4) : E4 := chartA (DlamInv P 1 Y)

@[simp] lemma DlamInv_apply2 (Y : E4) : DlamInv P 1 Y 2 = Y 2 := by simp [DlamInv]
@[simp] lemma DlamInv_apply3 (Y : E4) : DlamInv P 1 Y 3 = Y 3 := by simp [DlamInv]
@[simp] lemma DinvN_apply2 (Y : E4) : DinvN P Y 2 = Y 2 := by simp [DinvN]

/-! ### The Moser flow as a parameter -/

/-- **What `prop:shd4-maps` uses of the Moser flow `Φ`** (`prop:shd4-moser`), with
`Ω₀ = OmegaT P 0`: `Φ⁻¹` is smooth on `{p < h}`, `(Φ⁻¹)^* Ω₀ = Ω_final` there, `Φ⁻¹` maps
`{p < h}` into itself with left inverse `Φ`, and `Φ` fixes the three fibres pointwise. -/
structure PhiInvSpec (Phi PhiInv : E4 → E4) : Prop where
  smooth : ∀ X, pE X < P.h → ContDiffAt ℝ ∞ PhiInv X
  pullback : ∀ X, pE X < P.h → X 2 ∈ annulus → pull2 PhiInv (Bundle.OmegaT P 0) X = OmegaFinal P X
  mapsTo : ∀ X, pE X < P.h → pE (PhiInv X) < P.h
  left_inv : ∀ X, pE X < P.h → Phi (PhiInv X) = X
  fixes : ∀ X ∈ fibreSet, Phi X = X

/-- **The embeddings into the normal bundle** `f_i^N = Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i` (`prop:shd4-maps`),
in the global coordinates of `N`; the same `𝒟` and `Φ` for all `i`. -/
def fN (PhiInv : E4 → E4) (i : ℕ) (X : E4) : E4 := PhiInv (DinvN P (layerMap P i X))

variable {P} {Phi PhiInv : E4 → E4} (hΦ : PhiInvSpec P Phi PhiInv)
include hΦ

end SymplecticPacking.Strip
