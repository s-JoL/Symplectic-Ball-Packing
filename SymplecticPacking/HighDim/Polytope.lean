import OAI.Geometry.BallPacking.Models.RationalSlack

/-!
# Moment polytopes

`Δ = region bF cF = {p ≥ 0, ⟨b_ν, p⟩ ≤ ℓ_ν}` (OpenAI library), its `j`-th slice length
`L_j(p) = min_{ν : b_{νj} > 0} (ℓ_ν − Σ_{i≠j} b_{νi} p_i) / b_{νj}`, and the simplex
`Δ_h = {p ≥ 0, Σ p_j ≤ h}` as the polytope with one face.
Paper: def:mech-model (b), def:cmp-rearrangement.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)

variable {m q : ℕ}

/-- Data of a downward polytope `{p ≥ 0, ⟨b_ν, p⟩ ≤ ℓ_ν}`. -/
structure Polytope (m q : ℕ) where
  b : Fin q → Moments m
  ℓ : Fin q → ℝ

namespace Polytope

/-- The polytope as a set. -/
def set (Δ : Polytope m q) : Set (Moments m) := region Δ.b Δ.ℓ

/-- Standing hypotheses: nonnegative normals, positive levels, compact region, and every
coordinate direction is bounded by some face. -/
structure Spec (Δ : Polytope m q) : Prop where
  b_nonneg : ∀ ν j, 0 ≤ Δ.b ν j
  ℓ_pos : ∀ ν, 0 < Δ.ℓ ν
  compact : IsCompact Δ.set
  bounded_dir : ∀ j, ∃ ν, 0 < Δ.b ν j

theorem convex_set (Δ : Polytope m q) : Convex ℝ Δ.set := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun j => ?_, fun ν => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 j; have := hy.1 j
    positivity
  · have h1 := hx.2 ν
    have h2 := hy.2 ν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have e1 : ∑ j, Δ.b ν j * (a * x j) = a * ∑ j, Δ.b ν j * x j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, Δ.b ν j * (b * y j) = b * ∑ j, Δ.b ν j * y j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left h1 ha
    have := mul_le_mul_of_nonneg_left h2 hb
    have : Δ.ℓ ν = a * Δ.ℓ ν + b * Δ.ℓ ν := by rw [← add_mul, hab, one_mul]
    linarith

/-- Slice length in direction `j`: `L_j(p) = min_{ν : b_{νj} > 0} (ℓ_ν − Σ_{i≠j} b_{νi}p_i)/b_{νj}`
(it does not depend on `p_j`). -/
def sliceLen (Δ : Polytope m q) (j : Fin m) (p : Moments m) : ℝ :=
  ⨅ ν : {ν : Fin q // 0 < Δ.b ν j},
    (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j

/-- Moving the `j`-th coordinate of a point of `Δ` inside `[0, L_j]` stays in `Δ`. -/
theorem update_mem {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ Δ.sliceLen j p) :
    Function.update p j x ∈ Δ.set := by
  classical
  refine ⟨fun i => ?_, fun ν => ?_⟩
  · by_cases hij : i = j
    · subst hij; simpa using hx0
    · simpa [Function.update_of_ne hij] using hp.1 i
  · set S := ∑ i, (if i = j then 0 else Δ.b ν i * p i)
    have hsplit : ∑ i, Δ.b ν i * Function.update p j x i = S + Δ.b ν j * x := by
      have : ∀ i, Δ.b ν i * Function.update p j x i =
          (if i = j then 0 else Δ.b ν i * p i) + (if i = j then Δ.b ν j * x else 0) := by
        intro i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij, Function.update_of_ne hij]
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
      simp [S]
    have hfull : ∑ i, Δ.b ν i * p i = S + Δ.b ν j * p j := by
      have : ∀ i, Δ.b ν i * p i =
          (if i = j then 0 else Δ.b ν i * p i) + (if i = j then Δ.b ν j * p j else 0) := by
        intro i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
      simp [S]
    rw [hsplit]
    rcases (hΔ.b_nonneg ν j).lt_or_eq with hb | hb
    · have hL : Δ.sliceLen j p ≤ (Δ.ℓ ν - S) / Δ.b ν j :=
        ciInf_le (Set.finite_range _).bddBelow (⟨ν, hb⟩ : {ν : Fin q // 0 < Δ.b ν j})
      have := hxL.trans hL
      rw [le_div_iff₀ hb] at this
      linarith
    · rw [← hb, zero_mul, add_zero]
      have h1 := hp.2 ν
      rw [hfull, ← hb, zero_mul, add_zero] at h1
      exact h1

/-- The `j`-th coordinate of a point of `Δ` is at most `L_j`. -/
theorem le_sliceLen {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) : p j ≤ Δ.sliceLen j p := by
  classical
  obtain ⟨ν₀, hν₀⟩ := hΔ.bounded_dir j
  have : Nonempty {ν : Fin q // 0 < Δ.b ν j} := ⟨⟨ν₀, hν₀⟩⟩
  refine le_ciInf fun ν => ?_
  rw [le_div_iff₀ ν.2]
  have h1 := hp.2 ν.1
  have hfull : ∑ i, Δ.b ν.1 i * p i =
      ∑ i, (if i = j then 0 else Δ.b ν.1 i * p i) + Δ.b ν.1 j * p j := by
    have : ∀ i, Δ.b ν.1 i * p i =
        (if i = j then 0 else Δ.b ν.1 i * p i) + (if i = j then Δ.b ν.1 j * p j else 0) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
    simp
  rw [hfull] at h1
  linarith

/-- The simplex `Δ_h = {p ≥ 0, Σ_j p_j ≤ h}`. -/
def simplex (m : ℕ) (h : ℝ) : Polytope m 1 where
  b _ _ := 1
  ℓ _ := h

theorem simplex_set (m : ℕ) (h : ℝ) :
    (simplex m h).set = OAI.PackingSufficiencySupport.momentSimplex m h := by
  ext p
  simp [set, simplex, region, OAI.PackingSufficiencySupport.momentSimplex]

/-- The dilated polytope `τ Δ` (levels multiplied by `τ`). -/
def dilate (Δ : Polytope m q) (τ : ℝ) : Polytope m q where
  b := Δ.b
  ℓ ν := τ * Δ.ℓ ν

theorem simplex_spec {m : ℕ} {h : ℝ} (hh : 0 < h) : (simplex m h).Spec := by
  refine ⟨fun _ _ => zero_le_one, fun _ => hh, ?_, fun _ => ⟨0, one_pos⟩⟩
  rw [simplex_set]
  exact OAI.PackingSufficiencySupport.momentSimplex_isCompact m h

end Polytope

end SymplecticPacking.HighDim
