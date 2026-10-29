import SymplecticPacking.BranchSmall.Profile
import SymplecticPacking.HighDim.Model
import SymplecticPacking.BranchSmall.HandleExplicit
import OAI.Geometry.BallPacking.Models.RationalSlack
import SymplecticPacking.BranchLargeHigh.FSTail

/-!
# The quadric toric model (paper def:qdr-curve, lem:qdr-curve, def:qdr-model, prop:vtr-handle)

Base curve: the smooth complete intersection of diagonal quadrics
`Γ = {Z_j² = Z_0² − (j+1) W², j = 1, …, n−1} ⊂ CP^n` (the OpenAI library's
`locus (parameters m)`, `n = m + 3`); its affine part `Surface m = Γ ∖ {W = 0}` is the base
surface `M` of the product form. Degree `2^{n−1}`, genus `1 + (n−3)2^{n−2}`, normal bundle
`O(2)|_Γ^{⊕(n−1)}`. Model form `σ_FS + Σ_j d(p_j α_j)`, i.e. horizontal primitive
`Γ(p) = (1 − 2|p|) · (FS primitive)` (`normalHorizontalPrimitive _ 2`), density
`κ(p) = 1 − 2|p|` against `Λ = ω_FS|_Γ` (`curveFSForm _ (1/π)`, total area `2^{n−1}`).
Base domain: the explicit compact exhaustion piece `projectionDomain` at level `baseLevel`.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set Manifold
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Manifold

variable {k : ℕ}

instance surfaceSigmaCompact (m : ℕ) : SigmaCompactSpace (Surface m) :=
  curveSigmaCompact (parameters m)

/-- Explicit handle data on the affine quadric curve (annulus `𝒜` around a vanishing cycle,
dual band `ℬ`, closed one-form `β` of period one,
paper prop:vtr-handle). -/
def quadricHandle (m : ℕ) : AnnularHandleData (ℝ × ℝ) (Surface m) :=
  quadricHandleData m

/-- Explicit exhaustion level `ℓ = ⌈2^{m+8} (m+4) / d⌉₊`, `d = dgap` the comparator gap
parameter. By the explicit Fubini–Study tail bound (`BranchLargeHigh.exhaustion_area_defect_le_level`:
`projectionDomain R` misses FS area `≤ 2^{m+2}(m+4)/(ℓ+2)`), the base-area defect is `≤ d/64`,
which is absorbed by lowering the comparison profile by `11d/32` (`quadricModel_area`). -/
def baseLevel (m : ℕ) (ρ : Fin k → ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ (m + 8) * (m + 4) / dgap (m + 3) ρ⌉₊

/-- The quadric toric model for the normalised input `ρ`. -/
def quadricModel (m : ℕ) (ρ : Fin k → ℝ) : ToricModel (Surface m) (m + 2) 1 where
  Δ := Polytope.simplex (m + 2) (hgt (m + 3) ρ)
  base := projectionDomain (parameters m) (exhaustionRadius (parameters m) (baseLevel m ρ))
  Λ := curveFSForm (parameters m) (1 / Real.pi)
  dens x := equalNormalCoefficient (m + 2) 2 x.1
  Γ := normalHorizontalPrimitive (parameters m) 2
  handle := quadricHandle m
  hb := (quadricHandle m).width / 2
  hδ := 1 / 4

theorem quadricModel_spec {m : ℕ} {ρ : Fin k → ℝ} (H : Hyp (m + 3) ρ) :
    (quadricModel m ρ).Spec := by
  have hh0 : 0 < hgt (m + 3) ρ := hgt_pos H
  have hh1 : hgt (m + 3) ρ < 1 / 2 := hgt_lt_half H
  have hR := exhaustionRadius_pos (parameters m) (baseLevel m ρ)
  have hw := (quadricHandle m).width_pos
  have hin := quadricHandleData_in_exhaustion m (baseLevel m ρ)
  have hKc := projectionDomain_interior_connected hR
    (exhaustionRadius_branch (parameters m) (baseLevel m ρ))
  refine
    { Δ_spec := Polytope.simplex_spec hh0
      base_compact := projectionDomain_compact (parameters m) _
      base_conn := hKc.isPreconnected
      base_ne := hKc.nonempty
      base_boundary := projectionDomain_smoothBoundary hR
        (exhaustionRadius_branch (parameters m) (baseLevel m ρ))
      orient := positivePlaneTransitions (parameters m)
      hb_pos := half_pos hw
      hb_lt := by change (quadricHandle m).width / 2 < (quadricHandle m).width; linarith
      hδ_pos := by show (0:ℝ) < 1 / 4; norm_num
      hδ_lt := by show (1:ℝ) / 4 < 1 / 2; norm_num
      handle_in_base := (subset_union_left).trans hin
      dual_in_base := (subset_union_right).trans hin
      handle_orient := quadricHandleData_positive m
      clock := quadricHandleData_clock m
      Λ_smooth := curveFSForm_smooth (parameters m) (1 / Real.pi)
      Λ_skew := curveFSForm_skew (parameters m) (1 / Real.pi)
      Λ_pos := fun c y hy => curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy
      dens_smooth := (equalNormalCoefficient_smooth (m + 2) 2).contMDiff.comp contMDiff_fst
      dens_pos := ?_
      Γ_smooth := normalHorizontalPrimitive_smooth (parameters m) 2
      dΓ := normalHorizontalPrimitive_exterior (parameters m) 2 }
  intro p hp x _
  change p ∈ (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set at hp
  rw [Polytope.simplex_set] at hp
  show 0 < equalNormalCoefficient (m + 2) 2 p
  exact equalNormalCoefficient_pos (by norm_num) (by linarith : (2:ℝ) * hgt (m + 3) ρ < 1) hp.2

/-- The base area dominates the comparison profile plus the caps up to `11d/32` (the exact
profile is `2^{m+2}(1−2|p|) − caps`; the truncation defect at level `baseLevel` is `≤ d/64` by the
explicit FS tail bound). Without the slack `11d/32` the inequality is false: the compact piece
`projectionDomain` misses part of the curve's FS area (see `QuadricModelArea`). -/
theorem quadricModel_area {m : ℕ} {ρ : Fin k → ℝ} (H : Hyp (m + 3) ρ) :
    ∀ p ∈ (quadricModel m ρ).Δ.set,
      (cmpInput m ρ).P p - 11 * (cmpInput m ρ).d / 32 ≤
        (quadricModel m ρ).baseArea (quadricModel_spec H) p - capSum (capA (m + 3) ρ) p := by
  intro p hp
  have hd : 0 < dgap (m + 3) ρ := dgap_pos H
  change p ∈ (Polytope.simplex (m + 2) (hgt (m + 3) ρ)).set at hp
  rw [Polytope.simplex_set] at hp
  have hh1 := hgt_lt_half H
  have hκ0 : 0 < equalNormalCoefficient (m + 2) 2 p :=
    equalNormalCoefficient_pos (by norm_num) (by linarith : (2:ℝ) * hgt (m + 3) ρ < 1) hp.2
  have hκ1 : equalNormalCoefficient (m + 2) 2 p ≤ 1 :=
    equalNormalCoefficient_le_one (by norm_num) hp.1
  have hdef := BranchLargeHigh.exhaustion_area_defect_le_level (parameters m) (baseLevel m ρ)
  set A := compactSurfaceFormIntegral (projectionDomain_compact (parameters m)
    (exhaustionRadius (parameters m) (baseLevel m ρ))) (curveFSForm (parameters m) (1 / Real.pi))
    with hA
  have hbase : (quadricModel m ρ).baseArea (quadricModel_spec H) p =
      equalNormalCoefficient (m + 2) 2 p * A :=
    compactSurfaceFormIntegral_smul (projectionDomain_compact (parameters m)
      (exhaustionRadius (parameters m) (baseLevel m ρ))) (equalNormalCoefficient (m + 2) 2 p)
      (curveFSForm (parameters m) (1 / Real.pi))
  have hP : (cmpInput m ρ).P p =
      2 ^ (m + 2) * equalNormalCoefficient (m + 2) 2 p - capSum (capA (m + 3) ρ) p := rfl
  have hdd : (cmpInput m ρ).d = dgap (m + 3) ρ := rfl
  rw [hbase, hP, hdd]
  have hlev : (2 : ℝ) ^ (m + 8) * (m + 4) / dgap (m + 3) ρ ≤ (baseLevel m ρ : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hd] at hlev
  have hcast : ((m + 2 : ℕ) : ℝ) + 2 = (m : ℝ) + 4 := by push_cast; ring
  rw [hcast] at hdef
  have hℓ : (0 : ℝ) < (baseLevel m ρ : ℝ) + 2 := by positivity
  have hB : (2 : ℝ) ^ (m + 2) * ((m : ℝ) + 4) / ((baseLevel m ρ : ℝ) + 2) ≤
      dgap (m + 3) ρ / 64 := by
    rw [div_le_iff₀ hℓ]
    have h8 : (2 : ℝ) ^ (m + 8) = 2 ^ (m + 2) * 64 := by
      rw [show m + 8 = (m + 2) + 6 by ring, pow_add]; norm_num
    rw [h8] at hlev
    nlinarith
  have hX : (2 : ℝ) ^ (m + 2) - A ≤ dgap (m + 3) ρ / 64 := hdef.trans hB
  have hXd : 0 ≤ dgap (m + 3) ρ / 64 := by positivity
  have hκX : equalNormalCoefficient (m + 2) 2 p * ((2 : ℝ) ^ (m + 2) - A) ≤
      dgap (m + 3) ρ / 64 :=
    (mul_le_mul_of_nonneg_left hX hκ0.le).trans (mul_le_of_le_one_left hXd hκ1)
  nlinarith

end SymplecticPacking.BranchSmall
