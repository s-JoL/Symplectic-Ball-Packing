import SymplecticPacking.BranchSmall.Transfer
import SymplecticPacking.HighDim.Handle.NativePackingSpec
import SymplecticPacking.HighDim.Handle.ScalarRawAgreement
import SymplecticPacking.HighDim.Handle.QuadricFlowAtlas

/-!
# The normalised packing of the small-ball branch (paper thm:qdr-packing)

`f_i = 𝒯_{h,b} ∘ ψ_i` with `ψ_i` the toric packing maps of the quadric model for the explicit
comparison datum, enlarged capacities `ρ'_i` and domains `ρ''_i`. The proof of
`normalized_spec` is the assembly (prop:mech-assembly) of thm:mech-packing, thm:cmp-main,
the model facts and thm:qdr-transfer.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set Manifold
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient closedBall openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

variable {k : ℕ}

/-- The explicit comparison datum. -/
def datum (m : ℕ) (ρ : Fin k → ℝ) : ComparisonDatum (m + 2) :=
  (cmpInput m ρ).comparatorDatum (negPData m ρ)

/-- The toric packing maps `ψ_i`. -/
def psi (m : ℕ) (ρ : Fin k → ℝ) : Fin k → Ambient (m + 3) → Surface m × Fibre (m + 2) :=
  (ToricPackingStages.smallRawModel m ρ).packing
    (ToricPackingStages.quadricFlowAtlas m (baseLevel m ρ))
    (datum m ρ) (capA (m + 3) ρ) (rho2 (m + 3) ρ)

/-- **The normalised maps** `f_i = 𝒯 ∘ ψ_i`. -/
def normalized (m : ℕ) (ρ : Fin k → ℝ) : AmbientPacking (m + 3) k where
  f i := vectorTransfer m (hgt (m + 3) ρ) (bT (m + 3) ρ) ∘ psi m ρ i
  enlarged := rho1 (m + 3) ρ
  domain := rho2 (m + 3) ρ

/-- Lowering the profile by `c < γ` keeps a comparison datum, with gap `γ - c`. -/
theorem datumSpec_lower {m q : ℕ} {D : ComparisonDatum m} {Δ : Polytope m q}
    {P : Moments m → ℝ} {γ c : ℝ} (hD : D.Spec Δ P γ) (hc : c < γ)
    (hreserve : D.reserve ≤ γ - c) : D.Spec Δ (fun p => P p - c) (γ - c) where
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

theorem normalized_spec {m : ℕ} {ρ : Fin k → ℝ} (H : Hyp (m + 3) ρ) :
    (normalized m ρ).Spec 1 ρ := by
  have hT := quadricModel_spec H
  have hD : (datum m ρ).Spec (quadricModel m ρ).Δ (cmpInput m ρ).P
      (11 * (cmpInput m ρ).d / 16) :=
    (cmpInput m ρ).comparatorDatum_spec (negPData m ρ) (cmpInput_spec H) (negPData_ne_nil m ρ)
      (fun p _ => negPData_eval m ρ p)
  have hcap : ∀ i, ∀ p : Moments (m + 2), (∀ j, 0 ≤ p j) → ∑ j, p j ≤ capA (m + 3) ρ i →
      p ∈ ((quadricModel m ρ).Δ.dilate (tau (m + 3) ρ)).set := by
    intro i p hp hs
    refine ⟨hp, fun _ => ?_⟩
    simp only [quadricModel, Polytope.dilate, Polytope.simplex, one_mul]
    exact hs.trans (capA_le_tau_hgt H i)
  have hD' := datumSpec_lower hD (c := 11 * (cmpInput m ρ).d / 32)
    (by have := dgap_pos H; change 11 * dgap (m + 3) ρ / 32 < 11 * dgap (m + 3) ρ / 16; linarith)
    (by
      change 11 * (cmpInput m ρ).d / 64 ≤ 11 * (cmpInput m ρ).d / 16 - 11 * (cmpInput m ρ).d / 32
      have := dgap_pos H
      change 0 < (cmpInput m ρ).d at this
      linarith)
  have hA := ToricPackingStages.smallRawModel_agreement m ρ
  have hF := ToricPackingStages.quadricFlowAtlas_spec (baseLevel m ρ)
    (ToricPackingStages.smallRawModel m ρ)
    (ToricPackingStages.quadricModelRawPresentation_inclusion m (baseLevel m ρ)) rfl
  have hN := ToricPackingStages.smallRawModel_spec H
  rw [ToricPackingStages.smallRawModel_area_eq H] at hN
  have hambient : (ToricPackingStages.smallRawModel m ρ).presentation.inclusion ∘
      (ToricPackingStages.smallRawModel m ρ).handle.cover=
      (ToricPackingStages.smallRawModel m ρ).handle.ambientCover := by
    rw [show (ToricPackingStages.smallRawModel m ρ).presentation.inclusion=Subtype.val from
      ToricPackingStages.quadricModelRawPresentation_inclusion m (baseLevel m ρ)]
    exact ToricPackingStages.quadricRawHandle_cover_ambient m
  obtain ⟨hψ, hψK, hψd⟩ := hA.native_packing_spec hT hF hambient hD' hN
    (rho2_nonneg H) (rho2_lt_capA H) (tau_lt_one H) hcap (quadricModel_area H)
  obtain ⟨hg, hgemb, hgform, hgC⟩ := vectorTransfer_spec m (hgt_pos H) (hgt_lt_bT H)
    (bT_lt_half H)
  have hT' : ∀ i, MapsTo (psi m ρ i) (closedBall (m + 3) (rho2 (m + 3) ρ i))
      (transferDomain m (bT (m + 3) ρ)) := by
    intro i x hx
    have hreg := interior_subset (hψK i hx)
    have hp : planeMoments (psi m ρ i x).2 ∈ (quadricModel m ρ).Δ.set := hreg.2
    rw [show (quadricModel m ρ).Δ = Polytope.simplex (m + 2) (hgt (m + 3) ρ) from rfl,
      Polytope.simplex_set] at hp
    exact lt_of_le_of_lt hp.2 (hgt_lt_bT H)
  exact assembly_spec hψ hT' hψd (transferDomain_isOpen m _) hg hgemb hgform hgC
    (lt_rho1 H) (rho1_lt_rho2 H)

end SymplecticPacking.BranchSmall
