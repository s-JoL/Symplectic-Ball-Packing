import SymplecticPacking.BranchLargeHigh.Coupled
import SymplecticPacking.BranchLargeHigh.ChartLift
import SymplecticPacking.BranchLargeHigh.FSTail
import SymplecticPacking.BranchLargeHigh.MixedModel
import SymplecticPacking.BranchSmall.Model
import SymplecticPacking.HighDim.Phase
import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus
import SymplecticPacking.HighDim.Handle.NativePackingSpec
import SymplecticPacking.HighDim.Handle.ScalarRawAgreement
import SymplecticPacking.HighDim.Handle.QuadricFlowAtlas

/-!
# The second-stage maps: explicit pieces (supplement `thm:two-packing`, steps 1–6)

Supporting definitions for `secondStage` (`SecondStage.lean`). Dimension `m = q + 3`
(`n = m + 1 = q + 4`), base curve the Vandermonde quadric curve `Γ ⊂ CP^{q+3}` (the OpenAI
library's `locus (parameters q)`, affine part `Surface q`), fibre `ℂ^{q+3}` of
`O(1) ⊕ O(2)^{⊕(q+2)}` in mixed coordinates.

* `enum` — the enumeration `ι ≃ Fin (card ι)` used to index the balls of the handle packing;
* `rF`, `hatF` — capacities `r_i` and output capacities `ρ̂_i = (3ρ_i + 5r_i)/8` on `Fin (card ι)`;
* `negPData` — `−P` for the mixed profile `P = H_b − Σ (r_i − |p|)_+` as a maximum of affine
  functions (data for the finite comparator), with `negPData_eval`;
* `mixedDatum` — the comparison datum (`thm:cmp-main` for `Mixed.cmpInput`), `mixedDatum_spec`
  proved from `Mixed.cmpInput_spec`;
* `mixedModel` — the toric model `(Γ, O(1) ⊕ O(2)^{⊕(q+2)}, Δ, Ω_mix)`: horizontal primitive
  `(1 − u − 2w)·λ_FS` (`largeHorizontalPrimitive`), density `1 − u − 2w`, base domain the
  explicit exhaustion piece at level `mixedLevel`, handle data shared with the quadric model of
  the small-ball branch;
* `mixedPsi` — the handle packing maps `ψ_i` (`RawToricModel.packing`), with `mixedPsi_spec` proved from the native assembly;
* `mix`/`unmix` — mixed coordinates `ζ_0 = z_0`, `ζ_j = √(1 − u) w_j` and their inverse;
* `chartLift` — `(φ, Ĵ)` read in the unitary frame over the ball chart (vector normal transfer
  in `CP^m`, connection lift).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two

open Set Manifold
open Problem
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient closedBall momentSimplex largeModelGap
  largeModelDensity)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

/-! ### Indexing and capacities -/

/-- The enumeration of the balls used by the handle packing. -/
def enum (ι : Type) [Fintype ι] [DecidableEq ι] : ι ≃ Fin (Fintype.card ι) :=
  Fintype.equivFin ι

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The capacities `r` reindexed by `Fin (card ι)`. -/
def rF (r : ι → ℝ) : Fin (Fintype.card ι) → ℝ := fun j => r ((enum ι).symm j)

/-- The output capacities `ρ̂_i = ρ̄_i + (r_i - ρ̄_i)/4 ∈ (ρ_i, r_i)`, `ρ̄_i = (ρ_i + r_i)/2`
(the same expression as `secondStageHat`). -/
def hat (ρ r : ι → ℝ) : ι → ℝ := fun i => (ρ i + r i) / 2 + (r i - (ρ i + r i) / 2) / 4

/-- `ρ̂` reindexed by `Fin (card ι)`. -/
def hatF (ρ r : ι → ℝ) : Fin (Fintype.card ι) → ℝ := fun j => hat ρ r ((enum ι).symm j)

lemma hatF_enum (ρ r : ι → ℝ) (i : ι) : hatF ρ r (enum ι i) = hat ρ r i := by
  simp [hatF]

omit [Fintype ι] [DecidableEq ι] in
lemma lt_hat {ρ r : ι → ℝ} (h : ∀ i, ρ i < r i) (i : ι) : ρ i < hat ρ r i := by
  have := h i; unfold hat; linarith

omit [Fintype ι] [DecidableEq ι] in
lemma hat_lt {ρ r : ι → ℝ} (h : ∀ i, ρ i < r i) (i : ι) : hat ρ r i < r i := by
  have := h i; unfold hat; linarith

lemma hatF_lt {ρ r : ι → ℝ} (h : ∀ i, ρ i < r i) (j : Fin (Fintype.card ι)) :
    hatF ρ r j < rF r j := hat_lt h _

lemma hatF_nonneg {ρ r : ι → ℝ} (h0 : ∀ i, 0 < ρ i) (h : ∀ i, ρ i < r i)
    (j : Fin (Fintype.card ι)) : 0 ≤ hatF ρ r j :=
  ((h0 _).trans (lt_hat h _)).le

/-! ### The comparator data of the mixed profile -/

variable {k : ℕ}

/-- `−P = −H_b + Σ_i max(0, r_i − |p|)` as a maximum of affine functions, fibre rank `q + 3`:
`−H_b(p) = −2^{q+2} + 2^{q+2} u + 2^{q+3} w`. -/
def negPData (q : ℕ) (r : Fin k → ℝ) : PolyFn (q + 3) :=
  (List.finRange k).foldl (fun F i => PolyFn.add F (BranchSmall.capPair (q + 1) (r i)))
    [⟨Fin.cons (2 ^ (q + 2)) (fun _ => 2 ^ (q + 3)), -2 ^ (q + 2)⟩]

theorem negPData_ne_nil (q : ℕ) (r : Fin k → ℝ) : negPData q r ≠ [] :=
  (BranchSmall.foldl_capPair (q + 1) r (List.finRange k) (List.cons_ne_nil _ _) 0).1

theorem negPData_eval (q : ℕ) (a : ℝ) (r : Fin k → ℝ) (p : Moments (q + 3)) :
    (Mixed.cmpInput (q + 2) a r).P p = -PolyFn.eval (negPData q r) p := by
  have h := (BranchSmall.foldl_capPair (q + 1) r (List.finRange k)
    (F := [⟨Fin.cons (2 ^ (q + 2)) (fun _ => 2 ^ (q + 3)), -2 ^ (q + 2)⟩])
    (List.cons_ne_nil _ _) p).2
  change largeModelGap r p = -PolyFn.eval (negPData q r) p
  unfold negPData
  rw [h, ← Fin.sum_univ_def]
  simp only [largeModelGap, largeModelDensity, PolyFn.eval, List.foldl_nil, AffinePiece.eval,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
  ring

/-- The explicit comparison datum of the mixed model. -/
def mixedDatum (q : ℕ) (a : ℝ) (r : Fin k → ℝ) : ComparisonDatum (q + 3) :=
  (Mixed.cmpInput (q + 2) a r).comparatorDatum (negPData q r)

/-- `thm:cmp-main` for the mixed model. -/
theorem mixedDatum_spec {q : ℕ} {a : ℝ} {r : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a r) :
    (mixedDatum q a r).Spec (Mixed.cmpInput (q + 2) a r).Δ (Mixed.cmpInput (q + 2) a r).P
      (11 * (Mixed.cmpInput (q + 2) a r).d / 16) :=
  (Mixed.cmpInput (q + 2) a r).comparatorDatum_spec (negPData q r) (Mixed.cmpInput_spec H)
    (negPData_ne_nil q r) (fun p _ => negPData_eval q a r p)

/-! ### The mixed toric model and its handle packing -/

/-- Explicit exhaustion level of the closed quadric curve, `ℓ = ⌈2^{q+8}(q+4)/d⌉₊` with `d` the
comparator gap parameter `Mixed.dgap`. At this level the base-area defect is `≤ d/64 < 11d/32`,
half the comparator gap (`mixedModel_area`): on `{‖z‖ ≥ R}` the curve is a `2^{q+2}`-sheeted
cover of the `z`-line, the FS-area of `Γ ∖ projectionDomain R` is at most `2^{q+2}(q+4)/R²`,
`R² ≥ ℓ`, and the density is `≤ 1` on `Δ`. -/
def mixedLevel (q : ℕ) (a : ℝ) (r : Fin k → ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ (q + 8) * (q + 4) / Mixed.dgap (q + 2) a r⌉₊

/-- The mixed toric model `(Γ, O(1) ⊕ O(2)^{⊕(q+2)}, Δ, Ω_mix)`, `Ω_mix = σ_Γ + d[(1-u-2w)λ_FS]`
up to the closed term `u η` (which does not change the form). -/
def mixedModel (q : ℕ) (a : ℝ) (r : Fin k → ℝ) : ToricModel (Surface q) (q + 3) 2 where
  Δ := Mixed.polytope (q + 2) a r
  base := projectionDomain (parameters q) (exhaustionRadius (parameters q) (mixedLevel q a r))
  Λ := curveFSForm (parameters q) (1 / Real.pi)
  dens x := largeNormalCoefficient (q + 2) x.1
  Γ := largeHorizontalPrimitive (q := q + 2) (parameters q)
  handle := BranchSmall.quadricHandle q
  hb := (BranchSmall.quadricHandle q).width / 2
  hδ := 1 / 4

/-- Standing hypotheses of the mixed toric model (`def:mech-model` for the mixed weights). -/
theorem mixedModel_spec {q : ℕ} {a : ℝ} {r : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a r) :
    (mixedModel q a r).Spec := by
  have hR := exhaustionRadius_pos (parameters q) (mixedLevel q a r)
  have hw := (BranchSmall.quadricHandle q).width_pos
  have hin := BranchSmall.quadricHandleData_in_exhaustion q (mixedLevel q a r)
  have hKc := projectionDomain_interior_connected hR
    (exhaustionRadius_branch (parameters q) (mixedLevel q a r))
  have hh1 : Mixed.h1 (q + 2) a r < 1 := by linarith [Mixed.h1_lt H, H.half_lt]
  have hh2 : Mixed.h2 (q + 2) a r < 1 / 2 := Mixed.h2_lt_half H
  refine
    { Δ_spec := (Mixed.cmpInput_spec H).Δ_spec
      base_compact := projectionDomain_compact (parameters q) _
      base_conn := hKc.isPreconnected
      base_ne := hKc.nonempty
      base_boundary := projectionDomain_smoothBoundary hR
        (exhaustionRadius_branch (parameters q) (mixedLevel q a r))
      orient := positivePlaneTransitions (parameters q)
      hb_pos := half_pos hw
      hb_lt := by
        change (BranchSmall.quadricHandle q).width / 2 < (BranchSmall.quadricHandle q).width
        linarith
      hδ_pos := by norm_num [mixedModel]
      hδ_lt := by norm_num [mixedModel]
      handle_in_base := (subset_union_left).trans hin
      dual_in_base := (subset_union_right).trans hin
      handle_orient := BranchSmall.quadricHandleData_positive q
      clock := BranchSmall.quadricHandleData_clock q
      Λ_smooth := curveFSForm_smooth (parameters q) (1 / Real.pi)
      Λ_skew := curveFSForm_skew (parameters q) (1 / Real.pi)
      Λ_pos := fun c y hy =>
        curveFSForm_positive (parameters q) (one_div_pos.mpr Real.pi_pos) c hy
      dens_smooth := (largeNormalCoefficient_smooth (q + 2)).contMDiff.comp contMDiff_fst
      dens_pos := ?_
      Γ_smooth := largeHorizontalPrimitive_smooth (parameters q)
      dΓ := largeHorizontalPrimitive_exterior (parameters q) }
  intro p hp x _
  show 0 < largeNormalCoefficient (q + 2) p
  exact largeNormalCoefficient_pos hh1 hh2 hp

/-- The base area dominates the comparison profile plus the caps up to half the comparator gap:
the exact profile is `2^{q+2}(1 − u − 2w)` and the truncation defect at level `mixedLevel` is
`≤ d/64 ≤ 11d/32` (explicit FS tail bound). (Without the slack `11d/32` the inequality is false:
the compact piece `projectionDomain` misses part of the curve's FS area.) -/
theorem mixedModel_area {q : ℕ} {a : ℝ} {r : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a r) :
    ∀ p ∈ (mixedModel q a r).Δ.set,
      (Mixed.cmpInput (q + 2) a r).P p - 11 * (Mixed.cmpInput (q + 2) a r).d / 32 ≤
        (mixedModel q a r).baseArea (mixedModel_spec H) p - capSum r p := by
  intro p hp
  have hd : 0 < Mixed.dgap (q + 2) a r := Mixed.dgap_pos H
  have hh1 : Mixed.h1 (q + 2) a r < 1 := by linarith [Mixed.h1_lt H, H.half_lt]
  have hh2 : Mixed.h2 (q + 2) a r < 1 / 2 := Mixed.h2_lt_half H
  have hκ0 : 0 < largeNormalCoefficient (q + 2) p := largeNormalCoefficient_pos hh1 hh2 hp
  have hκ1 : largeNormalCoefficient (q + 2) p ≤ 1 := largeNormalCoefficient_le_one hp.1
  have hdef := exhaustion_area_defect_le_level (parameters q) (mixedLevel q a r)
  set A := compactSurfaceFormIntegral (projectionDomain_compact (parameters q)
    (exhaustionRadius (parameters q) (mixedLevel q a r))) (curveFSForm (parameters q) (1 / Real.pi))
    with hA
  have hbase : (mixedModel q a r).baseArea (mixedModel_spec H) p =
      largeNormalCoefficient (q + 2) p * A :=
    compactSurfaceFormIntegral_smul (projectionDomain_compact (parameters q)
      (exhaustionRadius (parameters q) (mixedLevel q a r))) (largeNormalCoefficient (q + 2) p)
      (curveFSForm (parameters q) (1 / Real.pi))
  have hP : (Mixed.cmpInput (q + 2) a r).P p =
      2 ^ (q + 2) * largeNormalCoefficient (q + 2) p - capSum r p := rfl
  have hdd : (Mixed.cmpInput (q + 2) a r).d = Mixed.dgap (q + 2) a r := rfl
  rw [hbase, hP, hdd]
  have hlev : (2 : ℝ) ^ (q + 8) * (q + 4) / Mixed.dgap (q + 2) a r ≤ (mixedLevel q a r : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hd] at hlev
  have hcast : ((q + 2 : ℕ) : ℝ) + 2 = (q : ℝ) + 4 := by push_cast; ring
  rw [hcast] at hdef
  have hℓ : (0 : ℝ) < (mixedLevel q a r : ℝ) + 2 := by positivity
  have hB : (2 : ℝ) ^ (q + 2) * ((q : ℝ) + 4) / ((mixedLevel q a r : ℝ) + 2) ≤
      Mixed.dgap (q + 2) a r / 64 := by
    rw [div_le_iff₀ hℓ]
    have h8 : (2 : ℝ) ^ (q + 8) = 2 ^ (q + 2) * 64 := by
      rw [show q + 8 = (q + 2) + 6 by ring, pow_add]; norm_num
    rw [h8] at hlev
    nlinarith
  have hX : (2 : ℝ) ^ (q + 2) - A ≤ Mixed.dgap (q + 2) a r / 64 := hdef.trans hB
  have hXd : 0 ≤ Mixed.dgap (q + 2) a r / 64 := by positivity
  have hκX : largeNormalCoefficient (q + 2) p * ((2 : ℝ) ^ (q + 2) - A) ≤
      Mixed.dgap (q + 2) a r / 64 :=
    (mul_le_mul_of_nonneg_left hX hκ0.le).trans (mul_le_of_le_one_left hXd hκ1)
  nlinarith

/-- Lowering the profile by `c < γ` keeps a comparison datum, with gap `γ - c`. -/
theorem _root_.SymplecticPacking.HighDim.ComparisonDatum.Spec.shift {m q : ℕ}
    {D : ComparisonDatum m} {Δ : Polytope m q} {P : Moments m → ℝ} {γ c : ℝ}
    (hD : D.Spec Δ P γ) (hc : c < γ) (hreserve : D.reserve ≤ γ - c) :
    D.Spec Δ (fun p => P p - c) (γ - c) where
  K_smooth := hD.K_smooth
  gen := hD.gen
  preserves := hD.preserves
  collar := hD.collar
  gap_pos := by linarith
  gap w hw := by
    have := hD.gap w hw
    show _ - (P _ - c) ≤ _ - (γ - c)
    linarith
  reserve_pos := hD.reserve_pos
  reserve_le_gap := hreserve

/-- The handle packing maps `ψ_j` of `thm:mech-packing` in the mixed model, caps `r`,
domains `ρ̂`. -/
def mixedPsi (q : ℕ) (a : ℝ) (rr hh : Fin k → ℝ) :
    Fin k → Ambient (q + 4) → Surface q × Fibre (q + 3) :=
  (ToricPackingStages.mixedRawModel q a rr).packing
    (ToricPackingStages.quadricFlowAtlas q (mixedLevel q a rr)) (mixedDatum q a rr) rr hh

/-- `thm:mech-packing` for the mixed model. -/
theorem mixedPsi_spec {q : ℕ} {a : ℝ} {rr hh : Fin k → ℝ} (H : Mixed.Hyp (q + 2) a rr)
    (hh0 : ∀ j, 0 ≤ hh j) (hhr : ∀ j, hh j < rr j) :
    (∀ j, FormNeighborhoodEmbedding (closedBall (q + 4) (hh j))
      (fun _ => successorStandardForm (q + 3)) (mixedModel q a rr).form
        (mixedPsi q a rr hh j)) ∧
    (∀ j, MapsTo (mixedPsi q a rr hh j) (closedBall (q + 4) (hh j))
      (interior (mixedModel q a rr).region)) ∧
    Pairwise (fun i j => Disjoint (mixedPsi q a rr hh i '' closedBall (q + 4) (hh i))
      (mixedPsi q a rr hh j '' closedBall (q + 4) (hh j))) := by
  have hT := mixedModel_spec H
  have hA : RawModelAgreement (ToricPackingStages.mixedRawModel q a rr) (mixedModel q a rr) :=
    ToricPackingStages.mixedRawModel_agreement q a rr
  have hF := ToricPackingStages.quadricFlowAtlas_spec (mixedLevel q a rr)
    (ToricPackingStages.mixedRawModel q a rr)
    (ToricPackingStages.quadricModelRawPresentation_inclusion q (mixedLevel q a rr)) rfl
  have hN := ToricPackingStages.mixedRawModel_spec H
  rw [ToricPackingStages.quadricScalarSemanticModel_area_eq q (q+3) 2
    (ToricPackingStages.mixedRawLevel q a rr) (Mixed.polytope (q+2) a rr)
    (largeNormalCoefficient (q+2)) hT] at hN
  have hambient : (ToricPackingStages.mixedRawModel q a rr).presentation.inclusion ∘
      (ToricPackingStages.mixedRawModel q a rr).handle.cover=
      (ToricPackingStages.mixedRawModel q a rr).handle.ambientCover := by
    rw [show (ToricPackingStages.mixedRawModel q a rr).presentation.inclusion=Subtype.val from
      ToricPackingStages.quadricModelRawPresentation_inclusion q (mixedLevel q a rr)]
    exact ToricPackingStages.quadricRawHandle_cover_ambient q
  exact hA.native_packing_spec hT hF hambient
    ((mixedDatum_spec H).shift (c := 11 * (Mixed.cmpInput (q + 2) a rr).d / 32)
      (by have := Mixed.dgap_pos H; change 11 * Mixed.dgap (q + 2) a rr / 32 <
            11 * Mixed.dgap (q + 2) a rr / 16; linarith)
      (by
        change 11 * (Mixed.cmpInput (q + 2) a rr).d / 64 ≤
          11 * (Mixed.cmpInput (q + 2) a rr).d / 16 - 11 * (Mixed.cmpInput (q + 2) a rr).d / 32
        have := Mixed.dgap_pos H
        change 0 < (Mixed.cmpInput (q + 2) a rr).d at this
        linarith))
    hN hh0 hhr (Mixed.tau_lt_one H) (fun j _ hp hs => Mixed.cap_subset H j ⟨hp, hs⟩) (mixedModel_area H)

/-! ### Mixed coordinates -/

/-- The fibre moment `u = π|ζ_0|²` of the `O(1)` coordinate. -/
def uMom {q : ℕ} (ζ : Fibre (q + 3)) : ℝ := radialArea (ζ 0)

/-- Mixed coordinates `ζ_0 = z_0`, `ζ_j = √(1 − u) w_j` (`p_j = (1 − u) v_j`). -/
def mix {q : ℕ} (z : Fibre (q + 3)) : Fibre (q + 3) :=
  fun j => if j = 0 then z 0 else Real.sqrt (1 - uMom z) • z j

/-- Inverse of the mixed coordinates on `u < 1`: `w_j = ζ_j / √(1 − u)`. -/
def unmix {q : ℕ} (ζ : Fibre (q + 3)) : Fibre (q + 3) :=
  fun j => if j = 0 then ζ 0 else (Real.sqrt (1 - uMom ζ))⁻¹ • ζ j

@[simp] lemma mix_zero {q : ℕ} (z : Fibre (q + 3)) : mix z 0 = z 0 := by simp [mix]

@[simp] lemma unmix_zero {q : ℕ} (ζ : Fibre (q + 3)) : unmix ζ 0 = ζ 0 := by simp [unmix]

lemma uMom_unmix {q : ℕ} (ζ : Fibre (q + 3)) : uMom (unmix ζ) = uMom ζ := by
  simp [uMom]

lemma mix_unmix {q : ℕ} {ζ : Fibre (q + 3)} (hu : uMom ζ < 1) : mix (unmix ζ) = ζ := by
  funext j
  by_cases hj : j = 0
  · subst hj; simp
  · have hs : Real.sqrt (1 - uMom ζ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    simp only [mix, unmix, hj, if_false, uMom_unmix, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-! ### Return to the coupled model -/

/-- `(φ, Ĵ)` read in the unitary frame of `O(1)` over the ball chart `CP^{q+3} ∖ F`, on the
unmixed fibre coordinates `(z_0, w)`: the vector normal transfer `φ` of
`E₂ = O_Γ(2)^{⊕(q+2)}` into `CP^{q+3}` at heights `(h₁, h₂)` (explicit flows), lifted to the
first normal line by the connection lift `Ĵ = J ∘ e^{−2πif}` (
`lem:two-identification`). Its image is the coupled model of `Coupled.lean`. -/
def chartLift (q : ℕ) (h₁ h₂ : ℝ) : Surface q × Fibre (q + 3) → E (q + 4) :=
  chartLiftExplicit q h₁ h₂

/-- The second-stage map of ball `j` for `m = q + 3`:
`g_j = chartLift ∘ (id × unmix) ∘ ψ_j ∘ phaseEquiv`. -/
def stageMap (q : ℕ) (a : ℝ) (rr hh : Fin k → ℝ) (j : Fin k) (y : E (q + 4)) : E (q + 4) :=
  chartLift q (Mixed.h1 (q + 2) a rr) (Mixed.h2 (q + 2) a rr)
    (Prod.map id unmix (mixedPsi q a rr hh j (phaseEquiv (q + 4) y)))

end SymplecticPacking.BranchLargeHigh.Two
