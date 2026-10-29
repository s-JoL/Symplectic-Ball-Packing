import SymplecticPacking.BranchLargeHigh.Coupled
import SymplecticPacking.BranchLargeHigh.SecondStageMaps
import SymplecticPacking.BranchLargeHigh.MixedModel
import SymplecticPacking.BranchLargeHigh.SecondStageCore

/-!
# The second stage: packing of the small balls into the first coupled line (interface)

Supplement `thm:two-packing` up to the slit-shell map, main `thm:lrg-high`. Input (normalised): dimension
`n = m + 1 ≥ 4`, reserved capacity `1/2 < a < 1`, small target capacities `ρ_i` and auxiliary
capacities `ρ_i < r_i < 1 - a` with `a^n + Σ r_i^n < 1`.

The construction (each step an explicit definition):

1. `QuadricCurve`: the Vandermonde curve `Γ ⊂ CP^m` cut by `m - 1` diagonal quadrics, degree
   `2^{m-1}`, genus `1 + (m-3)2^{m-2}`, `Γ ∩ {Y₀ = 0}` the marked points.
2. Vector normal transfer `φ : X → CP^m` of `E₂ = O_Γ(2)^{⊕(m-1)}` (shared with the small-ball
   branch, `thm:vtr-transfer`, applied in `CP^m` instead of `CP^{m+1}`), with its base homotopy.
3. Connection lift `Ĵ = J ∘ e^{-2πif}` of `O(1)` (`lem:two-identification`).
4. Mixed coordinates `p₁ = u`, `p_j = (1-u) v_j` and the mixed model
   `(Γ, O(1) ⊕ O(2)^{⊕(m-1)}, Δ, Ω_mix)` (`MixedModel.lean`, `lem:two-mixed`).
5. Comparison datum + handle packing in the mixed model (`thm:mech-packing`, shared).
6. Return: undo the mixed coordinates, apply `(φ, Ĵ)`, read the result in the unitary frame over
   the ball chart `CP^m ∖ F` (marked fibres avoided). The result lands in the coupled model of
   `Coupled.lean` with `u ≤ h̄ < 1 - a` and `μ ≤ M̄ < 1`.

This file states the *output* of steps 1–6 as one interface (`SecondStageSpec`); the slit-shell
map (`Shell.lean`) and the assembly (`Embeddings.lean`) are proved from it.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Set
open scoped ContDiff

/-- Specification of the second stage for targets `ρ`, auxiliary capacities `r`, output maps
`g`, output capacities `ρ̂` and moment bounds `h̄, M̄`: for every `i`, `ρ_i < ρ̂_i`; `g_i` is
smooth, coupled-symplectic, injective on `B°(ρ̂_i)`; images pairwise disjoint; on the images
`u ≤ h̄ < 1 - a` and `μ ≤ M̄ < 1`. -/
structure SecondStageSpec {ι : Type} (m : ℕ) (a : ℝ) (ρ : ι → ℝ) (g : ι → E (m + 1) → E (m + 1))
    (ρhat : ι → ℝ) (h M : ℝ) : Prop where
  lt_hat : ∀ i, ρ i < ρhat i
  h_lt : h < 1 - a
  M_lt : M < 1
  smooth : ∀ i, ContDiffOn ℝ ∞ (g i) (capBallOpen 0 (ρhat i))
  coupled : ∀ i, ∀ y ∈ capBallOpen 0 (ρhat i), IsCoupledSymplectic (g i) y
  fib_le : ∀ i, ∀ y ∈ capBallOpen 0 (ρhat i), fibMoment (g i y) ≤ h
  base_le : ∀ i, ∀ y ∈ capBallOpen 0 (ρhat i), baseMoment (g i y) ≤ M
  inj : ∀ i, InjOn (g i) (capBallOpen 0 (ρhat i))
  disj : ∀ i i', i ≠ i' →
    Disjoint (g i '' capBallOpen 0 (ρhat i)) (g i' '' capBallOpen 0 (ρhat i'))

/-- **The second-stage maps** (steps 1–6 above). -/
def secondStage (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ρ r : ι → ℝ) : ι → E (m + 1) → E (m + 1) :=
  match m with
  | 0 => fun _ y => y
  | 1 => fun _ y => y
  | 2 => fun _ y => y
  | q + 3 => fun i => Two.stageMap q a (Two.rF r) (Two.hatF ρ r) (Two.enum ι i)

/-- The output capacities `ρ̂_i ∈ (ρ_i, r_i)` of `thm:mech-packing` (main `sec:hdl-proof` with
caps `a_i = r_i`): `ρ̄_i = (ρ_i + r_i)/2`, `δ_i = r_i - ρ̄_i`, `ρ̂_i = ρ̄_i + δ_i/4 = (3ρ_i + 5r_i)/8`. -/
def secondStageHat (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ρ r : ι → ℝ) : ι → ℝ :=
  fun i => (ρ i + r i) / 2 + (r i - (ρ i + r i) / 2) / 4

/-- The certified fibre-moment bound `h̄ < 1 - a` (the polytope height `h₁` of the mixed model
`MixedModel.lean` in dimension `n = m + 1 = q + 2`, i.e. `q = m - 1`). -/
def secondStageH (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ρ r : ι → ℝ) : ℝ :=
  Mixed.h1 (m - 1) a r

/-- The supremum `μ_𝒦` of the base moment `μ` over the compact set `𝒦' = ⋃_i g_i(B(ρ̂_i))` (closed
source balls); by compact avoidance of `F` it is `< 1` (supp. `large-shell`, proof of
`thm:two-packing`, "Second stage and line"). -/
def secondStageMuK (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ρ r : ι → ℝ) : ℝ :=
  sSup (⋃ i, (fun y => baseMoment (secondStage m a ρ r i y)) '' capBall 0 (secondStageHat m a ρ r i))

/-- The certified base-moment bound `M̄ = (1 + μ_𝒦)/2 ∈ (μ_𝒦, 1)` (compact avoidance of `F`).
The midpoint is used in place of a least rational `μ₀ ∈ (μ_𝒦, 1)`, so no search (and no
classical decidability) is needed; only `μ_𝒦 < 1` is used downstream. -/
def secondStageM (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (ρ r : ι → ℝ) : ℝ :=
  (1 + secondStageMuK m a ρ r) / 2

/-! ### Elementary properties of the output parameters -/

section Params

variable {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {a : ℝ} {ρ r : ι → ℝ}

lemma secondStageHat_eq (i : ι) : secondStageHat m a ρ r i = (3 * ρ i + 5 * r i) / 8 := by
  simp only [secondStageHat]; ring

lemma lt_secondStageHat (hρr : ∀ i, ρ i < r i) (i : ι) : ρ i < secondStageHat m a ρ r i := by
  rw [secondStageHat_eq]; linarith [hρr i]

/-- The mixed-model hypotheses `Mixed.Hyp (m - 1) a r` from those of `secondStage_spec`. -/
lemma secondStage_mixedHyp (hm : 3 ≤ m) (ha : 1 / 2 < a) (ha1 : a < 1) (hρ : ∀ i, 0 < ρ i)
    (hρr : ∀ i, ρ i < r i) (hr : ∀ i, r i < 1 - a)
    (hvol : a ^ (m + 1) + ∑ i, r i ^ (m + 1) < 1) : Mixed.Hyp (m - 1) a r := by
  have hq : m - 1 + 2 = m + 1 := by omega
  exact ⟨by omega, ha, ha1, fun i => (hρ i).trans (hρr i), hr, by rw [hq]; exact hvol⟩

lemma secondStageH_lt (hm : 3 ≤ m) (ha : 1 / 2 < a) (ha1 : a < 1) (hρ : ∀ i, 0 < ρ i)
    (hρr : ∀ i, ρ i < r i) (hr : ∀ i, r i < 1 - a)
    (hvol : a ^ (m + 1) + ∑ i, r i ^ (m + 1) < 1) : secondStageH m a ρ r < 1 - a :=
  Mixed.h1_lt (secondStage_mixedHyp hm ha ha1 hρ hρr hr hvol)

/-- `M̄ < 1` as soon as the compact supremum `μ_𝒦` is `< 1`. -/
lemma secondStageM_lt (h : secondStageMuK m a ρ r < 1) : secondStageM m a ρ r < 1 := by
  unfold secondStageM; linarith

lemma secondStageMuK_lt_M (h : secondStageMuK m a ρ r < 1) :
    secondStageMuK m a ρ r < secondStageM m a ρ r := by
  unfold secondStageM; linarith

/-- The base moment on the (open) source balls is bounded by `μ_𝒦`, given boundedness. -/
lemma baseMoment_le_MuK
    (hbdd : BddAbove (⋃ i, (fun y => baseMoment (secondStage m a ρ r i y)) ''
      capBall 0 (secondStageHat m a ρ r i)))
    (i : ι) {y : E (m + 1)} (hy : y ∈ capBallOpen 0 (secondStageHat m a ρ r i)) :
    baseMoment (secondStage m a ρ r i y) ≤ secondStageMuK m a ρ r := by
  have hy' : y ∈ capBall 0 (secondStageHat m a ρ r i) := by
    simp only [capBall, capBallOpen, mem_setOf_eq] at hy ⊢; exact hy.le
  exact le_csSup hbdd (mem_iUnion.2 ⟨i, y, hy', rfl⟩)

/-- Hence the base moment is bounded by `M̄` when `μ_𝒦 < 1`. -/
lemma baseMoment_le_M
    (hbdd : BddAbove (⋃ i, (fun y => baseMoment (secondStage m a ρ r i y)) ''
      capBall 0 (secondStageHat m a ρ r i)))
    (h : secondStageMuK m a ρ r < 1)
    (i : ι) {y : E (m + 1)} (hy : y ∈ capBallOpen 0 (secondStageHat m a ρ r i)) :
    baseMoment (secondStage m a ρ r i y) ≤ secondStageM m a ρ r :=
  (baseMoment_le_MuK hbdd i hy).trans (secondStageMuK_lt_M h).le

end Params

/-- **Geometric core of the second stage** (steps 1–6: handle packing `mixedPsi_spec` in the mixed
model, return through `unmix` and `chartLift`, `secondStage_return`; compact avoidance of `F`).
The maps are smooth, coupled-symplectic, injective with disjoint images on the open source balls,
have fibre moment `≤ h̄ = h₁`, and the base moment is bounded on the closed source balls with
supremum `μ_𝒦 < 1`. -/
theorem secondStage_core {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {a : ℝ} {ρ r : ι → ℝ}
    (hm : 3 ≤ m) (ha : 1 / 2 < a)
    (ha1 : a < 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, ρ i < r i) (hr : ∀ i, r i < 1 - a)
    (hvol : a ^ (m + 1) + ∑ i, r i ^ (m + 1) < 1) :
    (∀ i, ContDiffOn ℝ ∞ (secondStage m a ρ r i) (capBallOpen 0 (secondStageHat m a ρ r i))) ∧
    (∀ i, ∀ y ∈ capBallOpen 0 (secondStageHat m a ρ r i),
      IsCoupledSymplectic (secondStage m a ρ r i) y) ∧
    (∀ i, ∀ y ∈ capBallOpen 0 (secondStageHat m a ρ r i),
      fibMoment (secondStage m a ρ r i y) ≤ secondStageH m a ρ r) ∧
    (∀ i, InjOn (secondStage m a ρ r i) (capBallOpen 0 (secondStageHat m a ρ r i))) ∧
    (∀ i i', i ≠ i' → Disjoint (secondStage m a ρ r i '' capBallOpen 0 (secondStageHat m a ρ r i))
      (secondStage m a ρ r i' '' capBallOpen 0 (secondStageHat m a ρ r i'))) ∧
    BddAbove (⋃ i, (fun y => baseMoment (secondStage m a ρ r i y)) ''
      capBall 0 (secondStageHat m a ρ r i)) ∧
    secondStageMuK m a ρ r < 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 3 := ⟨m - 3, by omega⟩
  have hvol' : a ^ (q + 4) + ∑ i, r i ^ (q + 4) < 1 := hvol
  exact Two.stageMap_core ha ha1 hρ hρr hr hvol'

/-- **Second stage** (`thm:two-packing` minus the slit-shell map). -/
theorem secondStage_spec {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {a : ℝ} {ρ r : ι → ℝ} (hm : 3 ≤ m) (ha : 1 / 2 < a)
    (ha1 : a < 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, ρ i < r i) (hr : ∀ i, r i < 1 - a)
    (hvol : a ^ (m + 1) + ∑ i, r i ^ (m + 1) < 1) :
    SecondStageSpec m a ρ (secondStage m a ρ r) (secondStageHat m a ρ r)
      (secondStageH m a ρ r) (secondStageM m a ρ r) := by
  obtain ⟨hsm, hcp, hfib, hinj, hdisj, hbdd, hμ⟩ :=
    secondStage_core hm ha ha1 hρ hρr hr hvol
  exact
    { lt_hat := lt_secondStageHat hρr
      h_lt := secondStageH_lt hm ha ha1 hρ hρr hr hvol
      M_lt := secondStageM_lt hμ
      smooth := hsm
      coupled := hcp
      fib_le := hfib
      base_le := fun i _ hy => baseMoment_le_M hbdd hμ i hy
      inj := hinj
      disj := hdisj }

end SymplecticPacking.BranchLargeHigh
