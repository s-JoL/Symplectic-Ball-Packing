import SymplecticPacking.HighDim.Comparator.Poly

/-!
# Exact finite comparator data for a polyhedral area profile

For `A = −max(FA)`, the list `negPolyOf FA r e = FA + caps r + e` represents
exactly `A − caps r − e`. Its specification verifies the comparison gap,
outer-face bound and positive mean used by the surface packing.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3.Surf

open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)
open Set MeasureTheory
open scoped Pointwise

/-- The affine piece `p ↦ r − Σ_j p_j`. -/
def capPiece {m : ℕ} (ρ : ℝ) : AffinePiece m := ⟨fun _ => -1, ρ⟩

/-- The single cap `p ↦ max(0, r − Σ_j p_j)` as polyhedral data. -/
def capOne {m : ℕ} (ρ : ℝ) : PolyFn m := [⟨0, 0⟩, capPiece ρ]

theorem capOne_ne_nil {m : ℕ} (ρ : ℝ) : (capOne ρ : PolyFn m) ≠ [] := by simp [capOne]

theorem eval_capOne {m : ℕ} (ρ : ℝ) (p : Moments m) :
    PolyFn.eval (capOne ρ) p = max (ρ - ∑ j, p j) 0 := by
  simp only [capOne, PolyFn.eval, List.foldl_cons, List.foldl_nil, capPiece, AffinePiece.eval]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul,
    Finset.sum_neg_distrib]
  rw [max_comm]; ring_nf

/-- The cap profile `Σ_{i<n} max(0, r_i − Σ_j p_j)` (list recursion). -/
def capsList {m : ℕ} : List ℝ → PolyFn m
  | [] => PolyFn.const 0
  | ρ :: l => PolyFn.add (capOne ρ) (capsList l)

theorem capsList_ne_nil {m : ℕ} : ∀ l : List ℝ, (capsList l : PolyFn m) ≠ []
  | [] => by simp [capsList, PolyFn.const]
  | ρ :: l => PolyFn.add_ne_nil (capOne_ne_nil ρ) (capsList_ne_nil l)

theorem eval_capsList {m : ℕ} (p : Moments m) :
    ∀ l : List ℝ, PolyFn.eval (capsList l) p = (l.map fun ρ => max (ρ - ∑ j, p j) 0).sum
  | [] => by simp [capsList, PolyFn.eval_const]
  | ρ :: l => by
    rw [capsList, PolyFn.eval_add (capOne_ne_nil ρ) (capsList_ne_nil l), eval_capOne,
      eval_capsList p l]
    simp

/-- The cap profile `Σ_i max(0, r_i − Σ_j p_j)` as polyhedral data. -/
def capsPoly {m N : ℕ} (r : Fin N → ℝ) : PolyFn m := capsList ((List.finRange N).map r)

theorem capsPoly_ne_nil {m N : ℕ} (r : Fin N → ℝ) : (capsPoly r : PolyFn m) ≠ [] :=
  capsList_ne_nil _

theorem eval_capsPoly {m N : ℕ} (r : Fin N → ℝ) (p : Moments m) :
    PolyFn.eval (capsPoly r) p = ∑ i, max (r i - ∑ j, p j) 0 := by
  rw [capsPoly, eval_capsList, List.map_map]
  rw [Fin.sum_univ_def]
  rfl

/-- The exact polyhedral minorant `negP = FA + caps r + e` for a polyhedral area profile
`A = −max(FA)`: `−max(negP) = A − caps r − e`. -/
def negPolyOf {m N : ℕ} (FA : PolyFn m) (r : Fin N → ℝ) (e : ℝ) : PolyFn m :=
  PolyFn.add (PolyFn.add FA (capsPoly r)) (PolyFn.const e)

theorem negPolyOf_ne_nil {m N : ℕ} {FA : PolyFn m} (hFA : FA ≠ []) (r : Fin N → ℝ) (e : ℝ) :
    negPolyOf FA r e ≠ [] :=
  PolyFn.add_ne_nil (PolyFn.add_ne_nil hFA (capsPoly_ne_nil r)) (by simp [PolyFn.const])

theorem eval_negPolyOf {m N : ℕ} {FA : PolyFn m} (hFA : FA ≠ []) (r : Fin N → ℝ) (e : ℝ)
    (p : Moments m) :
    -PolyFn.eval (negPolyOf FA r e) p =
      -PolyFn.eval FA p - ∑ i, max (r i - ∑ j, p j) 0 - e := by
  rw [negPolyOf, PolyFn.eval_add (PolyFn.add_ne_nil hFA (capsPoly_ne_nil r))
    (by simp [PolyFn.const]), PolyFn.eval_add hFA (capsPoly_ne_nil r), eval_capsPoly,
    PolyFn.eval_const]
  ring

/-- **Specification of `negPolyOf`** (for an area
profile given by polyhedral data `A = −max(FA)` on the polytope). -/
theorem negPolyOf_spec {m q N : ℕ}
    (bF : Fin q → Moments m) (cF : Fin q → ℝ) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF)) (r : Fin N → ℝ)
    (FA : PolyFn m) (hFA : FA ≠ []) (hAF : ∀ p ∈ region bF cF, A p = -PolyFn.eval FA p)
    (hmean : 0 < ∫ p in region bF cF, A p - ∑ i, max (r i - ∑ j, p j) 0)
    {τ d₀ : ℝ}
    (houter : ∀ p ∈ region bF cF, p ∉ τ • region bF cF →
      d₀ ≤ A p - ∑ i, max (r i - ∑ j, p j) 0)
    {e : ℝ} (he : 0 < e) (he₀ : 4 * e ≤ d₀)
    (hem : 4 * e * (volume (region bF cF)).toReal ≤
      ∫ p in region bF cF, A p - ∑ i, max (r i - ∑ j, p j) 0) :
    negPolyOf FA r e ≠ [] ∧
    (∀ p ∈ region bF cF, -PolyFn.eval (negPolyOf FA r e) p ≤
      A p - ∑ i, max (r i - ∑ j, p j) 0 - e) ∧
    (∀ p ∈ region bF cF, p ∉ τ • region bF cF →
      d₀ / 2 ≤ -PolyFn.eval (negPolyOf FA r e) p) ∧
    0 < ∫ p in region bF cF, -PolyFn.eval (negPolyOf FA r e) p := by
  have heq : ∀ p ∈ region bF cF, -PolyFn.eval (negPolyOf FA r e) p =
      A p - ∑ i, max (r i - ∑ j, p j) 0 - e := by
    intro p hp; rw [eval_negPolyOf hFA, hAF p hp]
  refine ⟨negPolyOf_ne_nil hFA r e, fun p hp => (heq p hp).le, fun p hp hpt => ?_, ?_⟩
  · rw [heq p hp]; have := houter p hp hpt; linarith
  · have hmeas : MeasurableSet (region bF cF) := hcomp.isClosed.measurableSet
    have hvt : volume (region bF cF) < ⊤ := hcomp.measure_lt_top
    have hvol : 0 < (volume (region bF cF)).toReal := by
      refine ENNReal.toReal_pos ?_ hvt.ne
      intro h0
      have : (∫ p in region bF cF, A p - ∑ i, max (r i - ∑ j, p j) 0) = 0 := by
        rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
      linarith
    have hcap : Continuous (fun p : Moments m => ∑ i, max (r i - ∑ j, p j) 0) := by fun_prop
    have hf : IntegrableOn (fun p => A p - ∑ i, max (r i - ∑ j, p j) 0) (region bF cF) :=
      (hA.sub hcap.continuousOn).integrableOn_compact hcomp
    have hc : IntegrableOn (fun _ : Moments m => e) (region bF cF) :=
      integrableOn_const hvt.ne enorm_ne_top
    rw [setIntegral_congr_fun hmeas heq, integral_sub hf hc, setIntegral_const, smul_eq_mul,
      Measure.real]
    nlinarith

end SymplecticPacking.BranchLarge3.Surf
