import SymplecticPacking.General.Interface
import SymplecticPacking.HighDim.Phase

/-!
# From maps of `ℂⁿ` (OpenAI library conventions) to `EmbeddingData`

The geometric stages are written in the library's coordinates `Ambient n = Fin n → ℂ`, where
`IsBallEmbedding r f` says: `f` is smooth, an embedding and preserves `standardForm` on an open
neighbourhood of the closed capacity ball `closedBall n r`. `AmbientPacking.toData` conjugates
such maps by `phaseEquiv` and `toData_spec` derives the interface specification `EmbeddingSpec`.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Problem General
open OAI.PackingSufficiencySupport (Ambient capacity standardForm IsBallEmbedding)
open scoped ContDiff

/-- Explicit enlarged-source maps of `ℂⁿ`: maps `f i`, enlarged closed capacities `c'_i`
(`enlarged`) and capacities `a_i` of the closed balls on a neighbourhood of which `f i` is a
symplectic embedding (`domain`). -/
structure AmbientPacking (n k : ℕ) where
  f : Fin k → Ambient n → Ambient n
  enlarged : Fin k → ℝ
  domain : Fin k → ℝ

/-- Specification of an `AmbientPacking` for the input `(C, c)`, in library conventions. -/
structure AmbientPacking.Spec {n k : ℕ} (P : AmbientPacking n k) (C : ℝ) (c : Fin k → ℝ) :
    Prop where
  lt_enlarged : ∀ i, c i < P.enlarged i
  enlarged_lt_domain : ∀ i, P.enlarged i < P.domain i
  emb : ∀ i, IsBallEmbedding (P.domain i) (P.f i)
  disj : ∀ i j, i ≠ j →
    Disjoint (P.f i '' OAI.PackingSufficiencySupport.closedBall n (P.enlarged i))
      (P.f j '' OAI.PackingSufficiencySupport.closedBall n (P.enlarged j))
  into : ∀ i, P.f i '' OAI.PackingSufficiencySupport.closedBall n (P.enlarged i) ⊆
    OAI.PackingSufficiencySupport.openBall n C

/-- Conjugation by `phaseEquiv`. -/
def AmbientPacking.toData {n k : ℕ} (P : AmbientPacking n k) : EmbeddingData n k where
  f i y := (phaseEquiv n).symm (P.f i (phaseEquiv n y))
  enlarged := P.enlarged
  domain := P.domain

theorem omega0_phaseEquiv_symm {n : ℕ} (a b : Ambient n) :
    omega0 ((phaseEquiv n).symm a) ((phaseEquiv n).symm b) = standardForm a b := by
  rw [← standardForm_phaseEquiv]
  simp

theorem AmbientPacking.toData_spec {n k : ℕ} {P : AmbientPacking n k} {C : ℝ}
    {c : Fin k → ℝ} (h : P.Spec C c) : EmbeddingSpec n k C c P.toData := by
  set φ := phaseEquiv n
  have hcl : ∀ {r s : ℝ} {y : E n}, r ≤ s → y ∈ capBall 0 r →
      φ y ∈ OAI.PackingSufficiencySupport.closedBall n s := fun hrs hy =>
    phaseEquiv_mem_closedBall.mpr (le_trans hy hrs)
  have hop : ∀ {r : ℝ} {y : E n}, y ∈ capBallOpen 0 r →
      φ y ∈ OAI.PackingSufficiencySupport.closedBall n r := by
    intro r y hy
    have h' : Real.pi * ‖y - 0‖ ^ 2 < r := hy
    exact phaseEquiv_mem_closedBall.mpr h'.le
  refine ⟨h.lt_enlarged, h.enlarged_lt_domain, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨U, hU, hBU, hs, -, -⟩ := h.emb i
    have : ContDiffOn ℝ ∞ (fun y => P.f i (φ y)) (capBallOpen 0 (P.domain i)) :=
      hs.comp φ.contDiff.contDiffOn fun y hy => hBU (hop hy)
    exact φ.symm.contDiff.comp_contDiffOn this
  · intro i u hu x y
    obtain ⟨U, hU, hBU, hs, -, hform⟩ := h.emb i
    have hfu : DifferentiableAt ℝ (P.f i) (φ u) :=
      (hs.contDiffAt (hU.mem_nhds (hBU (hop hu)))).differentiableAt (by simp)
    have hd : HasFDerivAt (fun y => φ.symm (P.f i (φ y)))
        ((φ.symm : Ambient n →L[ℝ] E n).comp ((fderiv ℝ (P.f i) (φ u)).comp
          (φ : E n →L[ℝ] Ambient n))) u :=
      φ.symm.hasFDerivAt.comp u (hfu.hasFDerivAt.comp u φ.hasFDerivAt)
    change Problem.omega0 (fderiv ℝ (fun y => φ.symm (P.f i (φ y))) u x)
      (fderiv ℝ (fun y => φ.symm (P.f i (φ y))) u y) = Problem.omega0 x y
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [omega0_phaseEquiv_symm, hform (φ u) (hBU (hop hu)), standardForm_phaseEquiv]
  · intro i x hx y hy hxy
    obtain ⟨U, hU, hBU, -, he, -⟩ := h.emb i
    have hxy' : P.f i (φ x) = P.f i (φ y) := φ.symm.injective hxy
    have hx' : φ x ∈ U := hBU (hcl (h.enlarged_lt_domain i).le hx)
    have hy' : φ y ∈ U := hBU (hcl (h.enlarged_lt_domain i).le hy)
    have := he.injective (a₁ := ⟨φ x, hx'⟩) (a₂ := ⟨φ y, hy'⟩) hxy'
    exact φ.injective (congrArg Subtype.val this)
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxy' : P.f j (φ y) = P.f i (φ x) := φ.symm.injective hxy
    exact Set.disjoint_left.mp (h.disj i j hij) ⟨φ x, hcl le_rfl hx, rfl⟩
      ⟨φ y, hcl le_rfl hy, hxy'⟩
  · rintro i _ ⟨x, hx, rfl⟩
    exact phaseEquiv_symm_mem_openBall.mpr (h.into i ⟨φ x, hcl le_rfl hx, rfl⟩)

end SymplecticPacking.HighDim
