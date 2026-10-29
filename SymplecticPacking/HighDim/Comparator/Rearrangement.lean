import SymplecticPacking.HighDim.Polytope

/-!
# Coordinatewise increasing rearrangement (paper def:cmp-rearrangement, lem:cmp-rearrangement)

For `F : Δ → ℝ` and a coordinate `j`,
`(R_j F)(y, x) = min_{0 ≤ a, a + x ≤ L_j(y)} max(F(y, a), F(y, a + x))`, and
`ℛ = R_m ∘ ⋯ ∘ R_1`. The definition is a definite infimum over an explicit compact interval.
Proofs of the properties may reuse `OAI.PackingSufficiencySupport.Comparison.rearrange_*`
(the library's slice rearrangement), after identifying the two definitions slice by slice.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set MeasureTheory
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)

variable {m q : ℕ}

/-- `R_j F`. -/
def rearr (Δ : Polytope m q) (j : Fin m) (F : Moments m → ℝ) (p : Moments m) : ℝ :=
  ⨅ a : Icc (0 : ℝ) (Δ.sliceLen j p - p j),
    max (F (Function.update p j a)) (F (Function.update p j (a + p j)))

/-- `ℛ F = R_m (⋯ (R_1 F))` (coordinate `0` first). -/
def rearrAll (Δ : Polytope m q) (F : Moments m → ℝ) : Moments m → ℝ :=
  (List.finRange m).foldl (fun G j => rearr Δ j G) F

/-- The class of functions on which `ℛ` is used: continuous and convex on `Δ`. -/
def ConvexCont (Δ : Polytope m q) (F : Moments m → ℝ) : Prop :=
  ContinuousOn F Δ.set ∧ ConvexOn ℝ Δ.set F

/-! ### Properties (paper lem:cmp-rearrangement; supplement S-lem:fcp-rearrangement) -/

/-- The integrand of `R_j F` at `p`. -/
def rearrIntegrand (Δ : Polytope m q) (j : Fin m) (F : Moments m → ℝ) (p : Moments m)
    (a : Icc (0 : ℝ) (Δ.sliceLen j p - p j)) : ℝ :=
  max (F (Function.update p j a)) (F (Function.update p j (a + p j)))

theorem rearr_eq_iInf (Δ : Polytope m q) (j : Fin m) (F : Moments m → ℝ) (p : Moments m) :
    rearr Δ j F p = ⨅ a, rearrIntegrand Δ j F p a := rfl

theorem rearrIntegrand_mem {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) (a : Icc (0 : ℝ) (Δ.sliceLen j p - p j)) :
    Function.update p j a ∈ Δ.set ∧ Function.update p j (a + p j) ∈ Δ.set := by
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  have hpj : 0 ≤ p j := hp.1 j
  exact ⟨Polytope.update_mem hΔ hp j ha0 (by linarith [a.2.2]),
    Polytope.update_mem hΔ hp j (by linarith) (by linarith [a.2.2])⟩

theorem rearr_nonempty {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) : Nonempty (Icc (0 : ℝ) (Δ.sliceLen j p - p j)) :=
  ⟨⟨0, le_rfl, by linarith [Polytope.le_sliceLen hΔ hp j]⟩⟩

theorem rearr_bdd {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) {F : Moments m → ℝ} (hF : ConvexCont Δ F) :
    BddBelow (Set.range (rearrIntegrand Δ j F p)) := by
  obtain ⟨M, hM⟩ := hΔ.compact.bddBelow_image hF.1
  refine ⟨M, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (hM ⟨_, (rearrIntegrand_mem hΔ hp j a).1, rfl⟩).trans (le_max_left _ _)

/-! ### Identification with the library's slice rearrangement

On `Δ`, `R_j F` coincides with `OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange`
applied to `F|_Δ`; this transfers the library's properties. -/

section Bridge
open OAI.PackingSufficiencySupport

theorem Polytope.Spec.activeNonempty {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) :
    Nonempty (MomentPolytope.Active Δ.b j) :=
  let ⟨ν, h⟩ := hΔ.bounded_dir j; ⟨⟨ν, h⟩⟩

/-- `F|_Δ` as a continuous map on the library's `region`. -/
def cmpRestrict {Δ : Polytope m q} {F : Moments m → ℝ} (hF : ContinuousOn F Δ.set) :
    C(MomentPolytope.region Δ.b Δ.ℓ, ℝ) :=
  ⟨Δ.set.restrict F, hF.restrict⟩

/-- `F|_Δ` as a convex map in the library's sense. -/
def cmpConvexMap {Δ : Polytope m q} {F : Moments m → ℝ} (hF : ConvexCont Δ F) :
    Comparison.ConvexMaps (MomentPolytope.region Δ.b Δ.ℓ)
      (MomentPolytope.convex_region Δ.b Δ.ℓ) :=
  ⟨cmpRestrict hF.1, fun x y a b ha hb hab => hF.2.2 x.2 y.2 ha hb hab⟩

theorem sum_ite_eq_subtype (B p : Moments m) (j : Fin m) :
    ∑ i, (if i = j then 0 else B i * p i) =
      ∑ i : {i : Fin m // i ≠ j}, B i.val * p i.val := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j, if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun i _ => if_neg i.property

theorem sliceLen_eq_length {Δ : Polytope m q} (j : Fin m)
    [Nonempty (MomentPolytope.Active Δ.b j)] (p : Moments m) :
    Δ.sliceLen j p =
      MomentPolytope.length Δ.b Δ.ℓ j (fun i : {i : Fin m // i ≠ j} => p i) := by
  have key : ∀ ν : MomentPolytope.Active Δ.b j,
      (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j =
        MomentPolytope.endpoint Δ.b Δ.ℓ j ν (fun i : {i : Fin m // i ≠ j} => p i) := by
    intro ν
    unfold MomentPolytope.endpoint
    rw [sum_ite_eq_subtype]
  apply le_antisymm
  · apply (MomentPolytope.le_length_iff Δ.b Δ.ℓ j).mpr
    intro ν
    rw [← key]
    exact ciInf_le (Set.finite_range _).bddBelow ν
  · unfold Polytope.sliceLen
    refine le_ciInf fun ν => ?_
    rw [key]
    exact MomentPolytope.length_le _ _ _ ν _

theorem assemble_eq_update (p : Moments m) (j : Fin m) (a : ℝ) :
    MomentPolytope.assemble j (fun i : {i : Fin m // i ≠ j} => p i) a =
      Function.update p j a := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [MomentPolytope.assemble]
  · simp [MomentPolytope.assemble, hi, Function.update_of_ne hi]

theorem rearr_bdd' {Δ : Polytope m q} (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set)
    (j : Fin m) {F : Moments m → ℝ} (hF : ContinuousOn F Δ.set) :
    BddBelow (Set.range (rearrIntegrand Δ j F p)) := by
  obtain ⟨M, hM⟩ := hΔ.compact.bddBelow_image hF
  refine ⟨M, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (hM ⟨_, (rearrIntegrand_mem hΔ hp j a).1, rfl⟩).trans (le_max_left _ _)

/-- On `Δ`, `R_j F` is the library's coordinate rearrangement of `F|_Δ`. -/
theorem rearr_eq_coord {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m)
    [Nonempty (MomentPolytope.Active Δ.b j)] {F : Moments m → ℝ} (hF : ContinuousOn F Δ.set)
    (p : Moments m) (hp : p ∈ Δ.set) :
    rearr Δ j F p =
      MomentPolytope.coordRearrange Δ.b Δ.ℓ j hΔ.b_nonneg (cmpRestrict hF) ⟨p, hp⟩ := by
  have hL := sliceLen_eq_length (Δ := Δ) j p
  have hcand : ∀ (a : ℝ) (ha : 0 ≤ a)
      (hax : a + p j ≤ MomentPolytope.length Δ.b Δ.ℓ j (fun i : {i : Fin m // i ≠ j} => p i)),
      Comparison.intervalCandidate (MomentPolytope.baseRegion Δ.b Δ.ℓ j)
        (MomentPolytope.length Δ.b Δ.ℓ j)
        (MomentPolytope.onSlice Δ.b Δ.ℓ j hΔ.b_nonneg (cmpRestrict hF))
        (MomentPolytope.sliceEquiv Δ.b Δ.ℓ j hΔ.b_nonneg ⟨p, hp⟩) a ha hax =
      max (F (Function.update p j a)) (F (Function.update p j (a + p j))) := by
    intro a ha hax
    rw [← assemble_eq_update, ← assemble_eq_update]
    rfl
  have hne := rearr_nonempty hΔ hp j
  rw [rearr_eq_iInf]
  change _ = Comparison.rearrange _ _ _
    (MomentPolytope.onSlice Δ.b Δ.ℓ j hΔ.b_nonneg (cmpRestrict hF))
    (MomentPolytope.sliceEquiv Δ.b Δ.ℓ j hΔ.b_nonneg ⟨p, hp⟩)
  apply le_antisymm
  · obtain ⟨a, ha, hax, h⟩ := Comparison.rearrange_attained _ _
      (MomentPolytope.continuous_length Δ.b Δ.ℓ j).continuousOn
      (MomentPolytope.onSlice Δ.b Δ.ℓ j hΔ.b_nonneg (cmpRestrict hF))
      (MomentPolytope.sliceEquiv Δ.b Δ.ℓ j hΔ.b_nonneg ⟨p, hp⟩)
    rw [h, hcand a ha hax]
    have hax' : a + p j ≤
        MomentPolytope.length Δ.b Δ.ℓ j (fun i : {i : Fin m // i ≠ j} => p i) := hax
    exact ciInf_le (rearr_bdd' hΔ hp j hF) ⟨a, ha, by rw [hL]; linarith⟩
  · refine le_ciInf fun a => ?_
    have hax : (a : ℝ) + p j ≤
        MomentPolytope.length Δ.b Δ.ℓ j (fun i : {i : Fin m // i ≠ j} => p i) := by
      rw [← hL]; linarith [a.2.2]
    refine (Comparison.rearrange_le_candidate _ _
      (MomentPolytope.continuous_length Δ.b Δ.ℓ j).continuousOn _ _ a a.2.1 hax).trans_eq ?_
    rw [hcand]
    rfl

end Bridge

theorem rearr_convexCont {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : ConvexCont Δ (rearr Δ j F) := by
  have := hΔ.activeNonempty j
  have hEq := rearr_eq_coord hΔ j hF.1
  refine ⟨?_, Δ.convex_set, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    exact (OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange Δ.b Δ.ℓ j hΔ.b_nonneg
      (cmpRestrict hF.1)).continuous.congr fun x => (hEq x.1 x.2).symm
  · intro x hx y hy a b ha hb hab
    have hxy := Δ.convex_set hx hy ha hb hab
    rw [hEq x hx, hEq y hy, hEq _ hxy]
    exact OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange_convex Δ.b Δ.ℓ j
      hΔ.b_nonneg (cmpConvexMap hF) ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab

theorem rearr_mono {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F G : Moments m → ℝ}
    (hF : ConvexCont Δ F) (hG : ConvexCont Δ G) (hFG : ∀ p ∈ Δ.set, F p ≤ G p) :
    ∀ p ∈ Δ.set, rearr Δ j F p ≤ rearr Δ j G p := by
  intro p hp
  have := rearr_nonempty hΔ hp j
  rw [rearr_eq_iInf, rearr_eq_iInf]
  refine ciInf_mono (rearr_bdd hΔ hp j hF) fun a => ?_
  obtain ⟨h1, h2⟩ := rearrIntegrand_mem hΔ hp j a
  exact max_le_max (hFG _ h1) (hFG _ h2)

/-- `R_j F` on `Δ` only depends on `F` on `Δ`. -/
theorem rearr_congr {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F G : Moments m → ℝ}
    (h : EqOn F G Δ.set) : EqOn (rearr Δ j F) (rearr Δ j G) Δ.set := by
  intro p hp
  unfold rearr
  congr 1
  funext a
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  have haL : (a : ℝ) + p j ≤ Δ.sliceLen j p := by linarith [a.2.2]
  have hpj : 0 ≤ p j := hp.1 j
  rw [h (Polytope.update_mem hΔ hp j ha0 (by linarith)),
    h (Polytope.update_mem hΔ hp j (by linarith) haL)]

theorem rearr_add_const {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) (c : ℝ) :
    EqOn (rearr Δ j (fun x => F x + c)) (fun p => rearr Δ j F p + c) Δ.set := by
  intro p hp
  have hpj : 0 ≤ p j := hp.1 j
  have hL := Polytope.le_sliceLen hΔ hp j
  have : Nonempty (Icc (0 : ℝ) (Δ.sliceLen j p - p j)) := ⟨⟨0, le_rfl, by linarith⟩⟩
  obtain ⟨M, hM⟩ := hΔ.compact.bddBelow_image hF.1
  set g : Icc (0 : ℝ) (Δ.sliceLen j p - p j) → ℝ := fun a =>
    max (F (Function.update p j a)) (F (Function.update p j (a + p j)))
  have hg : BddBelow (Set.range g) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨a, rfl⟩
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    have hmem := Polytope.update_mem hΔ hp j ha0 (by linarith [a.2.2])
    exact (hM ⟨_, hmem, rfl⟩).trans (le_max_left _ _)
  change (⨅ a : Icc (0 : ℝ) (Δ.sliceLen j p - p j),
      max (F (Function.update p j a) + c) (F (Function.update p j (a + p j)) + c)) =
    (⨅ a, g a) + c
  simp only [max_add_add_right]
  exact ((OrderIso.addRight c).map_ciInf hg).symm

theorem rearr_integral {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : ∫ p in Δ.set, rearr Δ j F p = ∫ p in Δ.set, F p := by
  have := hΔ.activeNonempty j
  have hmeas : MeasurableSet Δ.set := hΔ.compact.isClosed.measurableSet
  have h := OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange_integral Δ.b Δ.ℓ j
    hΔ.b_nonneg hΔ.compact (cmpConvexMap hF)
  change (∫ p, OAI.PackingSufficiencySupport.Comparison.zeroExtend _ _ p) =
    ∫ p, OAI.PackingSufficiencySupport.Comparison.zeroExtend _ _ p at h
  rw [← integral_indicator hmeas, ← integral_indicator hmeas]
  convert h using 2
  · funext p
    classical
    rw [Set.indicator_apply]
    by_cases hp : p ∈ Δ.set
    · rw [if_pos hp, rearr_eq_coord hΔ j hF.1 p hp]
      exact (OAI.PackingSufficiencySupport.Comparison.zeroExtend_coe _ _ ⟨p, hp⟩).symm
    · rw [if_neg hp]
      unfold OAI.PackingSufficiencySupport.Comparison.zeroExtend
      rw [dif_neg (show p ∉ OAI.PackingSufficiencySupport.MomentPolytope.region Δ.b Δ.ℓ
        from hp)]
  · funext p
    classical
    rw [Set.indicator_apply]
    by_cases hp : p ∈ Δ.set
    · rw [if_pos hp]
      exact (OAI.PackingSufficiencySupport.Comparison.zeroExtend_coe
        (OAI.PackingSufficiencySupport.MomentPolytope.region Δ.b Δ.ℓ) (cmpRestrict hF.1)
        ⟨p, hp⟩).symm
    · rw [if_neg hp]
      unfold OAI.PackingSufficiencySupport.Comparison.zeroExtend
      rw [dif_neg (show p ∉ OAI.PackingSufficiencySupport.MomentPolytope.region Δ.b Δ.ℓ
        from hp)]

/-- `R_j` does not increase the maximum. -/
theorem rearr_le_sup {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) {M : ℝ} (hM : ∀ p ∈ Δ.set, F p ≤ M) :
    ∀ p ∈ Δ.set, rearr Δ j F p ≤ M := by
  intro p hp
  have hL := Polytope.le_sliceLen hΔ hp j
  let a₀ : Icc (0 : ℝ) (Δ.sliceLen j p - p j) := ⟨0, le_rfl, by linarith⟩
  rw [rearr_eq_iInf]
  refine (ciInf_le (rearr_bdd hΔ hp j hF) a₀).trans ?_
  obtain ⟨h1, h2⟩ := rearrIntegrand_mem hΔ hp j a₀
  exact max_le (hM _ h1) (hM _ h2)

/-- `G` is nondecreasing in coordinate `i` along `Δ`. -/
def IncOn (Δ : Polytope m q) (i : Fin m) (G : Moments m → ℝ) : Prop :=
  ∀ p ∈ Δ.set, ∀ p' ∈ Δ.set, p i ≤ p' i → (∀ l, l ≠ i → p l = p' l) → G p ≤ G p'

theorem rearr_incOn_self {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : IncOn Δ j (rearr Δ j F) := by
  have := hΔ.activeNonempty j
  intro p hp p' hp' h1 h2
  rw [rearr_eq_coord hΔ j hF.1 p hp, rearr_eq_coord hΔ j hF.1 p' hp']
  exact OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange_increasing Δ.b Δ.ℓ j
    hΔ.b_nonneg (cmpConvexMap hF) ⟨p, hp⟩ ⟨p', hp'⟩ h1 h2

theorem rearr_incOn_of_ne {Δ : Polytope m q} (hΔ : Δ.Spec) {i j : Fin m} (hij : i ≠ j)
    {F : Moments m → ℝ} (hF : ContinuousOn F Δ.set) (hi : IncOn Δ i F) :
    IncOn Δ i (rearr Δ j F) := by
  have := hΔ.activeNonempty j
  intro p hp p' hp' h1 h2
  rw [rearr_eq_coord hΔ j hF p hp, rearr_eq_coord hΔ j hF p' hp']
  exact OAI.PackingSufficiencySupport.MomentPolytope.coordRearrange_preserves_increasing
    Δ.b Δ.ℓ j hΔ.b_nonneg i hij (cmpRestrict hF)
    (fun x y hxy hrest => hi x.1 x.2 y.1 y.2 hxy hrest) ⟨p, hp⟩ ⟨p', hp'⟩ h1 h2

theorem foldl_rearr_incOn {Δ : Polytope m q} (hΔ : Δ.Spec) (l : List (Fin m))
    {F : Moments m → ℝ} (hF : ConvexCont Δ F) (S : Set (Fin m))
    (hS : ∀ i ∈ S, IncOn Δ i F) :
    ∀ i, i ∈ S ∨ i ∈ l → IncOn Δ i (l.foldl (fun G j => rearr Δ j G) F) := by
  induction l generalizing F S with
  | nil =>
    intro i hi
    rcases hi with hi | hi
    · exact hS i hi
    · simp at hi
  | cons j l ih =>
    intro i hi
    refine ih (rearr_convexCont hΔ j hF) (insert j S) ?_ i ?_
    · intro i' hi'
      by_cases h : i' = j
      · subst h; exact rearr_incOn_self hΔ i' hF
      · exact rearr_incOn_of_ne hΔ h hF.1 (hS i' ((Set.mem_insert_iff.mp hi').resolve_left h))
    · rcases hi with hi | hi
      · exact Or.inl (Set.mem_insert_of_mem _ hi)
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inl (Set.mem_insert _ _)
        · exact Or.inr hi

/-- On the downward closed `Δ`, monotonicity in each coordinate gives monotonicity. -/
theorem monotoneOn_of_incOn {Δ : Polytope m q} (hΔ : Δ.Spec) {G : Moments m → ℝ}
    (hG : ∀ i, IncOn Δ i G) :
    ∀ p ∈ Δ.set, ∀ p' ∈ Δ.set, p ≤ p' → G p ≤ G p' := by
  intro p hp p' hp' hle
  let r : ℕ → Moments m := fun k (i : Fin m) => if (i : ℕ) < k then p' i else p i
  have hr : ∀ k, r k ∈ Δ.set := fun k =>
    OAI.PackingSufficiencySupport.MomentPolytope.lower_closed Δ.b Δ.ℓ hΔ.b_nonneg hp'
      (fun i => by
        dsimp [r]; split_ifs
        · exact hp'.1 i
        · exact hp.1 i)
      (fun i => by
        dsimp [r]; split_ifs
        · exact le_rfl
        · exact hle i)
  have hstep : ∀ k, G (r k) ≤ G (r (k + 1)) := by
    intro k
    by_cases hk : k < m
    · refine hG ⟨k, hk⟩ _ (hr k) _ (hr (k + 1)) ?_ ?_
      · show (if k < k then _ else _) ≤ (if k < k + 1 then _ else _)
        rw [if_neg (lt_irrefl k), if_pos (Nat.lt_succ_self k)]
        exact hle _
      · intro l hl
        have hlk : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
        show (if (l : ℕ) < k then _ else _) = (if (l : ℕ) < k + 1 then _ else _)
        by_cases h1 : (l : ℕ) < k
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · have : r k = r (k + 1) := by
        funext i
        dsimp [r]
        rw [if_pos (by omega), if_pos (by omega)]
      rw [this]
  have h0 : r 0 = p := by funext i; simp [r]
  have hm : r m = p' := by funext i; simp [r, i.isLt]
  have hmono : G (r 0) ≤ G (r m) :=
    monotone_nat_of_le_succ (f := fun k => G (r k)) hstep (Nat.zero_le m)
  rwa [h0, hm] at hmono

/-- The output of `ℛ` is nondecreasing in every coordinate. -/
theorem rearrAll_monotone {Δ : Polytope m q} (hΔ : Δ.Spec) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : ∀ p ∈ Δ.set, ∀ p' ∈ Δ.set, p ≤ p' →
      rearrAll Δ F p ≤ rearrAll Δ F p' :=
  monotoneOn_of_incOn hΔ fun i =>
    foldl_rearr_incOn hΔ _ hF ∅ (fun _ h => h.elim) i
      (Or.inr (List.mem_finRange i))

/-! ### `ℛ` inherits the properties of the `R_j` -/

/-- Rearrangement along a list of coordinates (first element first). -/
def rearrList (Δ : Polytope m q) (l : List (Fin m)) (F : Moments m → ℝ) : Moments m → ℝ :=
  l.foldl (fun G j => rearr Δ j G) F

theorem rearrAll_eq (Δ : Polytope m q) (F : Moments m → ℝ) :
    rearrAll Δ F = rearrList Δ (List.finRange m) F := rfl

section
variable {Δ : Polytope m q} (hΔ : Δ.Spec)
include hΔ

theorem rearrList_convexCont (l : List (Fin m)) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : ConvexCont Δ (rearrList Δ l F) := by
  induction l generalizing F with
  | nil => exact hF
  | cons j l ih => exact ih (rearr_convexCont hΔ j hF)

theorem rearrList_mono (l : List (Fin m)) {F G : Moments m → ℝ}
    (hF : ConvexCont Δ F) (hG : ConvexCont Δ G) (hFG : ∀ p ∈ Δ.set, F p ≤ G p) :
    ∀ p ∈ Δ.set, rearrList Δ l F p ≤ rearrList Δ l G p := by
  induction l generalizing F G with
  | nil => exact hFG
  | cons j l ih =>
    exact ih (rearr_convexCont hΔ j hF) (rearr_convexCont hΔ j hG) (rearr_mono hΔ j hF hG hFG)

theorem rearrList_congr (l : List (Fin m)) {F G : Moments m → ℝ}
    (h : EqOn F G Δ.set) : EqOn (rearrList Δ l F) (rearrList Δ l G) Δ.set := by
  induction l generalizing F G with
  | nil => exact h
  | cons j l ih => exact ih (rearr_congr hΔ j h)

theorem rearrList_add_const (l : List (Fin m)) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) (c : ℝ) :
    EqOn (rearrList Δ l (fun x => F x + c)) (fun p => rearrList Δ l F p + c) Δ.set := by
  induction l generalizing F with
  | nil => exact fun _ _ => rfl
  | cons j l ih =>
    exact (rearrList_congr hΔ l (rearr_add_const hΔ j hF c)).trans
      (ih (rearr_convexCont hΔ j hF))

theorem rearrList_integral (l : List (Fin m)) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) : ∫ p in Δ.set, rearrList Δ l F p = ∫ p in Δ.set, F p := by
  induction l generalizing F with
  | nil => rfl
  | cons j l ih =>
    change ∫ p in Δ.set, rearrList Δ l (rearr Δ j F) p = _
    rw [ih (rearr_convexCont hΔ j hF), rearr_integral hΔ j hF]

theorem rearrList_le_sup (l : List (Fin m)) {F : Moments m → ℝ}
    (hF : ConvexCont Δ F) {M : ℝ} (hM : ∀ p ∈ Δ.set, F p ≤ M) :
    ∀ p ∈ Δ.set, rearrList Δ l F p ≤ M := by
  induction l generalizing F with
  | nil => exact hM
  | cons j l ih => exact ih (rearr_convexCont hΔ j hF) (rearr_le_sup hΔ j hF hM)

theorem rearrAll_convexCont {F : Moments m → ℝ} (hF : ConvexCont Δ F) :
    ConvexCont Δ (rearrAll Δ F) := rearrList_convexCont hΔ _ hF

theorem rearrAll_mono {F G : Moments m → ℝ} (hF : ConvexCont Δ F) (hG : ConvexCont Δ G)
    (hFG : ∀ p ∈ Δ.set, F p ≤ G p) : ∀ p ∈ Δ.set, rearrAll Δ F p ≤ rearrAll Δ G p :=
  rearrList_mono hΔ _ hF hG hFG

theorem rearrAll_congr {F G : Moments m → ℝ} (h : EqOn F G Δ.set) :
    EqOn (rearrAll Δ F) (rearrAll Δ G) Δ.set := rearrList_congr hΔ _ h

theorem rearrAll_add_const {F : Moments m → ℝ} (hF : ConvexCont Δ F) (c : ℝ) :
    EqOn (rearrAll Δ (fun x => F x + c)) (fun p => rearrAll Δ F p + c) Δ.set :=
  rearrList_add_const hΔ _ hF c

theorem rearrAll_integral {F : Moments m → ℝ} (hF : ConvexCont Δ F) :
    ∫ p in Δ.set, rearrAll Δ F p = ∫ p in Δ.set, F p := rearrList_integral hΔ _ hF

theorem rearrAll_le_sup {F : Moments m → ℝ} (hF : ConvexCont Δ F) {M : ℝ}
    (hM : ∀ p ∈ Δ.set, F p ≤ M) : ∀ p ∈ Δ.set, rearrAll Δ F p ≤ M :=
  rearrList_le_sup hΔ _ hF hM

end

end SymplecticPacking.HighDim
