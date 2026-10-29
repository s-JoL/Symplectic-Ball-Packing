import SymplecticPacking.BranchLargeHigh.Coupled
import SymplecticPacking.BranchLargeHigh.SecondStageMaps
import SymplecticPacking.BranchLargeHigh.MixedModel
import SymplecticPacking.BranchLargeHigh.ReturnMapSpec

/-!
# Supporting lemmas for `secondStage_core` (supplement `thm:two-packing`, steps 4–6)

The second-stage map of ball `i` is `g_i = R ∘ ψ_{e(i)} ∘ phaseEquiv`, where `ψ_j = mixedPsi`
are the handle packing maps of the mixed model (`mixedPsi_spec`, `thm:mech-packing`) and
`R = chartLift ∘ (id × unmix)` is the return map (`returnMap`). This file proves every clause of
`secondStage_core` for `m = q + 3` from

* `mixedPsi_spec` (proved, modulo `mixedModel_area`),
* the specification `returnMap_spec` of the return map on the open set
  `S = interior (mixedModel).region`: smooth, `R^*Ω = Ω_mix`, injective, `u ∘ R = u`
  (the connection lift is a phase rotation of the first normal coordinate) and `μ ∘ R < 1`
  (the image lies over the ball chart `CP^m ∖ F`).

The compact bound `μ_𝒦 < 1` follows from continuity on the compact closed source balls.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two

open Set Manifold Problem
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient closedBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

variable {k : ℕ}

/-- The return map `R = chartLift ∘ (id × unmix)` of the mixed model (step 6). -/
def returnMap (q : ℕ) (a : ℝ) (rr : Fin k → ℝ) : Surface q × Fibre (q + 3) → E (q + 4) :=
  fun x => chartLift q (Mixed.h1 (q + 2) a rr) (Mixed.h2 (q + 2) a rr) (Prod.map id unmix x)

/-- **Specification of the return map** (
`lem:two-identification`, `lem:two-mixed`): on the open set `interior (mixedModel).region`
the map `R = chartLift ∘ (id × unmix)` is smooth, pulls the coupled form back to the mixed form
`Ω_mix`, is injective, preserves the first fibre moment `u` (the connection lift
`Ĵ = J ∘ e^{-2πif}` rotates the phase of `z₀` only) and lands over the ball chart (`μ < 1`).
Assembled from `ReturnMapSpec.lean` (injectivity, `u ∘ R = u`, `μ ∘ R < 1` proved; smoothness
and the pullback identity remain separate lemmas). -/
theorem returnMap_spec {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) ∞ (returnMap q a rr)
      (interior (mixedModel q a rr).region) ∧
    (∀ x ∈ interior (mixedModel q a rr).region, ∀ v w,
      coupledForm (returnMap q a rr x)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) (returnMap q a rr) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) (returnMap q a rr) x w) =
      (mixedModel q a rr).form x v w) ∧
    InjOn (returnMap q a rr) (interior (mixedModel q a rr).region) ∧
    (∀ x ∈ interior (mixedModel q a rr).region, fibMoment (returnMap q a rr x) = uMom x.2) ∧
    (∀ x ∈ interior (mixedModel q a rr).region, baseMoment (returnMap q a rr x) < 1) :=
  ⟨returnMap'_contMDiffOn H, returnMap'_pullback H, (returnMap'_injOn H).mono interior_subset,
    fun x _ => fibMoment_returnMap' q a rr x, fun x _ => baseMoment_returnMap'_lt_one q a rr x⟩

/-- On the mixed region the first fibre moment is at most `h₁`. -/
lemma uMom_le_h1 {q : ℕ} {a : ℝ} {rr : Fin k → ℝ} {x : Surface q × Fibre (q + 3)}
    (hx : x ∈ (mixedModel q a rr).region) : uMom x.2 ≤ Mixed.h1 (q + 2) a rr := by
  obtain ⟨-, hxr⟩ := hx
  have h := (show planeMoments x.2 ∈
    region (mixedModel q a rr).Δ.b (mixedModel q a rr).Δ.ℓ from hxr).2 0
  simp only [mixedModel, Mixed.polytope, OAI.PackingSufficiencySupport.largeModelBounds,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Fin.cons_zero, Fin.cons_succ, zero_mul,
    Finset.sum_const_zero, add_zero, one_mul] at h
  exact h

/-! ### Reindexing -/

section Reindex

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma rMax_comp_equiv {κ : Type} [Fintype κ] (e : κ ≃ ι) (r : ι → ℝ) :
    Mixed.rMax (r ∘ e) = Mixed.rMax r := by
  unfold Mixed.rMax
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨e x, Finset.mem_univ _, le_rfl⟩)
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨e.symm x, Finset.mem_univ _, by simp⟩)

lemma sum_rF_pow (r : ι → ℝ) (p : ℕ) : ∑ j, rF r j ^ p = ∑ i, r i ^ p := by
  unfold rF
  exact (enum ι).symm.sum_comp (fun i => r i ^ p)

lemma rMax_rF (r : ι → ℝ) : Mixed.rMax (rF r) = Mixed.rMax r :=
  rMax_comp_equiv (enum ι).symm r

lemma h1_rF (q : ℕ) (a : ℝ) (r : ι → ℝ) : Mixed.h1 q a (rF r) = Mixed.h1 q a r := by
  simp only [Mixed.h1, Mixed.delta, Mixed.sigma, rMax_rF, sum_rF_pow]

lemma hyp_rF {q : ℕ} {a : ℝ} {r : ι → ℝ} (H : Mixed.Hyp q a r) : Mixed.Hyp q a (rF r) :=
  ⟨H.two_le, H.half_lt, H.lt_one, fun _ => H.r_pos _, fun _ => H.r_lt _,
    by rw [sum_rF_pow]; exact H.vol⟩

end Reindex

/-! ### The core -/

lemma isCompact_capBall {n : ℕ} (c : ℝ) : IsCompact (capBall (0 : E n) c) := by
  have hc : IsClosed (capBall (0 : E n) c) :=
    isClosed_le (f := fun y : E n => Real.pi * ‖y - 0‖ ^ 2) (g := fun _ => c)
      (by fun_prop) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  refine (Metric.isBounded_closedBall (x := (0 : E n)) (r := Real.sqrt (|c| / Real.pi))).subset ?_
  intro y hy
  have hy' : Real.pi * ‖y - 0‖ ^ 2 ≤ c := hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [le_div_iff₀ Real.pi_pos]
  nlinarith [le_abs_self c, Real.pi_pos]

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The geometric core of the second stage for `m = q + 3`.** -/
theorem stageMap_core {q : ℕ} {a : ℝ} {ρ r : ι → ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, ρ i < r i)
    (hr : ∀ i, r i < 1 - a) (hvol : a ^ (q + 4) + ∑ i, r i ^ (q + 4) < 1) :
    let g : ι → E (q + 4) → E (q + 4) :=
      fun i => stageMap q a (rF r) (hatF ρ r) (enum ι i)
    (∀ i, ContDiffOn ℝ ∞ (g i) (capBallOpen 0 (hat ρ r i))) ∧
    (∀ i, ∀ y ∈ capBallOpen 0 (hat ρ r i), IsCoupledSymplectic (g i) y) ∧
    (∀ i, ∀ y ∈ capBallOpen 0 (hat ρ r i), fibMoment (g i y) ≤ Mixed.h1 (q + 2) a r) ∧
    (∀ i, InjOn (g i) (capBallOpen 0 (hat ρ r i))) ∧
    (∀ i i', i ≠ i' → Disjoint (g i '' capBallOpen 0 (hat ρ r i))
      (g i' '' capBallOpen 0 (hat ρ r i'))) ∧
    BddAbove (⋃ i, (fun y => baseMoment (g i y)) '' capBall 0 (hat ρ r i)) ∧
    sSup (⋃ i, (fun y => baseMoment (g i y)) '' capBall 0 (hat ρ r i)) < 1 := by
  intro g
  have Hr : Mixed.Hyp (q + 2) a r :=
    ⟨by omega, ha, ha1, fun i => (hρ i).trans (hρr i), hr, hvol⟩
  have H : Mixed.Hyp (q + 2) a (rF r) := hyp_rF Hr
  obtain ⟨hψ, hψmaps, hψdisj⟩ := mixedPsi_spec H (hatF_nonneg hρ hρr) (hatF_lt hρr)
  obtain ⟨hRs, hRpull, hRinj, hRfib, hRbase⟩ := returnMap_spec H
  set S := interior (mixedModel q a (rF r)).region with hSdef
  have hS : IsOpen S := isOpen_interior
  set φ := phaseEquiv (q + 4)
  set ψ := mixedPsi q a (rF r) (hatF ρ r)
  set R := returnMap q a (rF r)
  have hg : ∀ i, g i = fun y => R (ψ (enum ι i) (φ y)) := fun _ => rfl
  have hgx : ∀ i y, g i y = R (ψ (enum ι i) (φ y)) := fun i y => congrFun (hg i) y
  -- closed and open source balls map into the closed ball of the packing
  have hcl : ∀ i {y : E (q + 4)}, y ∈ capBall 0 (hat ρ r i) →
      φ y ∈ closedBall (q + 4) (hatF ρ r (enum ι i)) := by
    intro i y hy
    rw [hatF_enum]; exact phaseEquiv_mem_closedBall.mpr hy
  have hop : ∀ i {y : E (q + 4)}, y ∈ capBallOpen 0 (hat ρ r i) →
      y ∈ capBall 0 (hat ρ r i) := by
    intro i y hy
    simp only [capBall, capBallOpen, Set.mem_setOf_eq] at hy ⊢
    exact hy.le
  -- pointwise smoothness of `ψ ∘ φ` and `R`
  have hψat : ∀ i {y : E (q + 4)}, y ∈ capBall 0 (hat ρ r i) →
      ContMDiffAt 𝓘(ℝ, E (q + 4)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) ∞
        (fun y => ψ (enum ι i) (φ y)) y := by
    intro i y hy
    obtain ⟨U, hUo, hKU, hs, -, -⟩ := hψ (enum ι i)
    have h1 : ContMDiffAt 𝓘(ℝ, Ambient (q + 4)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) ∞
        (ψ (enum ι i)) (φ y) := hs.contMDiffAt (hUo.mem_nhds (hKU (hcl i hy)))
    exact h1.comp y φ.contDiff.contMDiff.contMDiffAt
  have hmemS : ∀ i {y : E (q + 4)}, y ∈ capBall 0 (hat ρ r i) → ψ (enum ι i) (φ y) ∈ S :=
    fun i y hy => hψmaps (enum ι i) (hcl i hy)
  have hRat : ∀ x ∈ S, ContMDiffAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) ∞ R x :=
    fun x hx => hRs.contMDiffAt (hS.mem_nhds hx)
  have hgat : ∀ i {y : E (q + 4)}, y ∈ capBall 0 (hat ρ r i) →
      ContMDiffAt 𝓘(ℝ, E (q + 4)) 𝓘(ℝ, E (q + 4)) ∞ (g i) y := fun i y hy => by
    have h := (hRat _ (hmemS i hy)).comp y (hψat i hy)
    rw [hg i]; exact h
  -- injectivity of `ψ_j` on its closed ball
  have hψinj : ∀ j, InjOn (ψ j) (closedBall (q + 4) (hatF ρ r j)) := by
    intro j x hx y hy hxy
    obtain ⟨U, -, hKU, -, he, -⟩ := hψ j
    exact congrArg Subtype.val
      (he.injective (a₁ := ⟨x, hKU hx⟩) (a₂ := ⟨y, hKU hy⟩) hxy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro i y hy
    exact (contMDiffAt_iff_contDiffAt.mp (hgat i (hop i hy))).contDiffWithinAt
  · -- coupled symplecticity
    intro i y hy v w
    have hyc := hop i hy
    have hx := hmemS i hyc
    have hRd : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) R
        (ψ (enum ι i) (φ y)) := (hRat _ hx).mdifferentiableAt (by simp)
    obtain ⟨U, hUo, hKU, hs, -, hform⟩ := hψ (enum ι i)
    have hψd : MDifferentiableAt 𝓘(ℝ, Ambient (q + 4)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3))
        (ψ (enum ι i)) (φ y) :=
      (hs.contMDiffAt (hUo.mem_nhds (hKU (hcl i hyc)))).mdifferentiableAt (by simp)
    have hφd : MDifferentiableAt 𝓘(ℝ, E (q + 4)) 𝓘(ℝ, Ambient (q + 4)) φ y :=
      φ.differentiableAt.mdifferentiableAt
    have hcomp : fderiv ℝ (g i) y =
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) R (ψ (enum ι i) (φ y))).comp
          ((mfderiv 𝓘(ℝ, Ambient (q + 4)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) (ψ (enum ι i))
            (φ y)).comp (φ : E (q + 4) →L[ℝ] Ambient (q + 4))) := by
      rw [← mfderiv_eq_fderiv, hg i]
      change mfderiv _ _ (R ∘ (ψ (enum ι i) ∘ φ)) y = _
      rw [mfderiv_comp y hRd (hψd.comp y hφd), mfderiv_comp y hψd hφd, mfderiv_eq_fderiv,
        φ.fderiv]
      rfl
    rw [hcomp]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    show coupledForm (R (ψ (enum ι i) (φ y))) _ _ = _
    refine (hRpull _ hx _ _).trans ?_
    refine (hform (φ y) (hKU (hcl i hyc)) (φ v) (φ w)).trans ?_
    change successorStandardForm (q + 3) (φ v) (φ w) = _
    erw [successorStandardForm_apply]
    exact standardForm_phaseEquiv v w
  · -- fibre bound
    intro i y hy
    have hx := hmemS i (hop i hy)
    rw [hgx i y]
    rw [hRfib _ hx, ← h1_rF]
    exact uMom_le_h1 (interior_subset hx)
  · -- injectivity
    intro i x hx y hy hxy
    rw [hgx i x, hgx i y] at hxy
    have h1 := hRinj (hmemS i (hop i hx)) (hmemS i (hop i hy)) hxy
    exact φ.injective (hψinj (enum ι i) (hcl i (hop i hx)) (hcl i (hop i hy)) h1)
  · -- disjointness
    intro i i' hii
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    rw [hgx i x, hgx i' y] at hxy
    have h1 := hRinj (hmemS i' (hop i' hy)) (hmemS i (hop i hx)) hxy
    have hne : enum ι i ≠ enum ι i' := fun h => hii ((enum ι).injective h)
    exact Set.disjoint_left.mp (hψdisj hne) ⟨φ x, hcl i (hop i hx), rfl⟩
      ⟨φ y, hcl i' (hop i' hy), h1⟩
  · -- compact bound on the base moment
    have hcpt : ∀ i, IsCompact ((fun y => baseMoment (g i y)) '' capBall 0 (hat ρ r i)) := by
      intro i
      refine (isCompact_capBall _).image_of_continuousOn ?_
      intro y hy
      exact (baseMoment_contDiff.continuous.continuousAt.comp
        (hgat i hy).continuousAt).continuousWithinAt
    have hK := isCompact_iUnion hcpt
    refine ⟨hK.bddAbove, ?_⟩
    rcases (⋃ i, (fun y => baseMoment (g i y)) '' capBall 0 (hat ρ r i)).eq_empty_or_nonempty
      with he | hne
    · rw [he, Real.sSup_empty]; norm_num
    · obtain ⟨i, y, hy, hyv⟩ := Set.mem_iUnion.mp (hK.sSup_mem hne)
      rw [← hyv]
      show baseMoment (g i y) < 1
      rw [hgx i y]
      exact hRbase _ (hmemS i hy)

end Core

end SymplecticPacking.BranchLargeHigh.Two
