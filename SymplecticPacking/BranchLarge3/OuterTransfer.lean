import SymplecticPacking.BranchLarge3.EuclideanGuards

/-!
# Step S5: explicit transfer from the cubic ambient form to the outer (quadric) form

Explicit version of the OpenAI theorem `CubicModel.exists_actual_outer_normal_transfer`: for a
compact `K ⊆ cubicAffineDomain` on which `cubicAmbientForm (L+S) S c t` is nondegenerate, an
explicit `δ > 0` and an explicit embedding `g : CubicAmbient → CubicAmbient`, smooth on all of
`CubicAmbient`, avoiding `{z₂ = 0}` near `K` and pulling `outerAmbientForm L S c t δ` back to
`cubicAmbientForm (L+S) S c t`. This is the relative quadric return of the large-ball model:
`quadricLiftPolynomial`, `outerPolynomial`, `outerTube δ` (OpenAI
`Projective/SixLargeCubicPacking`), with the exact primitive comparison and Moser along the
explicit tube parameter.

Paper: supplement `six-return.tex` (relative quadric return).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set

/-- The target hyperplane is avoided by one native polynomial guard. -/
def outerGuards : Fin 1 → ℝ × CubicAmbient → ℝ :=
  fun _ p => Complex.normSq (outerTube p.1 p.2).2

/-- The safe tube parameter from compact clearance and derivative bounds. -/
def outerDelta (L S A B : ℕ) (c t : ℝ) (K : Set CubicAmbient) : ℝ :=
  UMoser.time cubicBasis (outerConePrimitive (A := A) (B := B) L S c t) K 1 outerGuards

/-- The explicit outer transfer map. -/
def outerMap (L S A B : ℕ) (c t : ℝ) (K : Set CubicAmbient) : CubicAmbient → CubicAmbient :=
  UMoser.map cubicBasis (outerConePrimitive (A := A) (B := B) L S c t) K
    (fun p : ℝ × CubicAmbient => outerTube p.1 p.2) (outerDelta L S A B c t K)

theorem outerTransfer_spec {L S A B : ℕ} (hAS : A < S) (hS : 2 * S < L)
    (hB : 3 * B < L + S) (c t : ℝ) {K : Set CubicAmbient} (hK : IsCompact K)
    (hKd : K ⊆ cubicAffineDomain)
    (hinv : ∀ p ∈ K, (cubicAmbientForm (A := A) (B := B) (L + S) S c t p).IsInvertible) :
    let δ := outerDelta L S A B c t K
    let g := outerMap L S A B c t K
    0 < δ ∧ ∃ W : Set CubicAmbient,
      IsOpen W ∧ K ⊆ W ∧ ContDiffOn ℝ ∞ g W ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      (∀ x ∈ W, (g x).2 ≠ 0) ∧ ∀ x ∈ W, ∀ v w,
      outerAmbientForm (A := A) (B := B) L S c t δ (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) =
        cubicAmbientForm (A := A) (B := B) (L + S) S c t x v w := by
  intro δ g
  have hΓ := outerConePrimitive_smooth (A := A) (B := B) L S c t
  have hΓ0 : ∀ x, manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x =
      cubicAmbientForm (A := A) (B := B) (L + S) S c t x := by
    intro x
    rw [outerConePrimitive_zero hAS hS hB, vector_exteriorOneForm]
    rfl
  have hnondeg (x : CubicAmbient) (hx : x ∈ K) :
      (manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x).IsInvertible := by
    rw [hΓ0]
    exact hinv x hx
  have hform (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (x : CubicAmbient)
      (_hx : x ∈ (univ : Set CubicAmbient)) :
      manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t δ) x =
      (outerAmbientForm (A := A) (B := B) L S c t δ (outerTube δ x)).bilinearComp
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x) := by
    have hTube : ContDiff ℝ ∞ (outerTube δ) :=
      outerTube_smooth.comp (contDiff_const.prodMk contDiff_id)
    rw [outerConePrimitive_positive L S c t (ne_of_gt hδ.1), vector_exteriorOneForm,
      primitivePullback_exterior (outerAmbientPrimitive_smooth L S c t δ) hTube]
    simp only [outerAmbientForm, manifoldMapDifferential, mfderiv_eq_fderiv]
  have hinto : MapsTo (outerTube 0) K {p : CubicAmbient | p.2 ≠ 0} := by
    intro x hx
    have h := hKd hx
    change x.1.1 * x.1.2 + (0 : ℂ) * x.2 ≠ 0
    rw [zero_mul, add_zero]
    exact mul_ne_zero h.1 h.2
  have hTubeM : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicAmbient)) 𝓘(ℝ, CubicAmbient) ∞
      (fun p : ℝ × CubicAmbient => outerTube p.1 p.2) := by
    rw [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact outerTube_smooth.contMDiff
  have hgs : ∀ i, ContDiff ℝ ∞ (outerGuards i) :=
    fun _ => guard_normSq_smooth.comp (contDiff_snd.comp outerTube_smooth)
  have hg0 : ∀ i, ∀ x ∈ K, 0 < outerGuards i (0,x) :=
    fun _ x hx => Complex.normSq_pos.mpr (hinto hx)
  have hge : ∀ p, (∀ i, 0 < outerGuards i p) →
      p.2 ∈ (univ:Set CubicAmbient) ∧ (outerTube p.1 p.2).2 ≠ 0 :=
    fun p hp => ⟨mem_univ _,Complex.normSq_pos.mp (hp 0)⟩
  obtain ⟨hδ, hδ1, hall⟩ :=
    UMoser.spec cubicBasis hΓ hK hnondeg isOpen_univ (subset_univ K)
      (by norm_num : 0 < (1 : ℝ)) hTubeM
      (fun δ hδ => (outerTube_isEmbedding (ne_of_gt hδ.1)).comp Topology.IsEmbedding.subtypeVal)
      (isOpen_ne_fun continuous_snd continuous_const) hinto outerGuards hgs hg0 hge
      (fun δ => outerAmbientForm (A := A) (B := B) L S c t δ) hform
  obtain ⟨W,hW,hKW,hg,hgemb,hgT,hgform⟩ := hall δ ⟨hδ,le_rfl⟩
  refine ⟨hδ, W, hW, hKW, hg.contDiff.contDiffOn, hgemb, hgT, ?_⟩
  intro x hx v w
  have hh := hgform x hx v w
  rw [hΓ0] at hh
  simp only [mfderiv_eq_fderiv] at hh
  convert! hh using 1

end SymplecticPacking.BranchLarge3
