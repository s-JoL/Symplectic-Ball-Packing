import SymplecticPacking.Strip.Embed
import SymplecticPacking.Branch2.Model.Cubic.Strip.LayerMaps

/-!
# The embeddings into the normal bundle

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Strip.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:str-embeddings` (`prop:shd4-maps`): the embeddings into the normal bundle
`f_i^N = Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i`.

Coordinates: the layer maps `E_i = layerMap P i` take values in the handle's local `𝒜⁺`-frame
coordinates; the global (`Zunit`-frame) coordinates of `N` are reached with `chartA`. So
`𝒟⁻¹` in global coordinates is `DinvN P = chartA ∘ DlamInv P 1` (`DinvN_pullback`:
`(𝒟⁻¹)^* Ω_final = Ω_pre` over the annulus, from `Handle.Cubic.OmegaFinal_eq_pullback`).

The Moser flow `Φ` of `sec:shd-four` is a parameter here: `PhiInvSpec P Φ Φ⁻¹` records exactly what the
paper uses — `Φ⁻¹` is `C^∞` on `{p < h}` with `(Φ⁻¹)^* Ω₀ = Ω_final` there (equivalent to
`Φ^* Ω_final = Ω₀`), maps `{p < h}` into itself, `Φ ∘ Φ⁻¹ = id` on `{p < h}`, and `Φ` fixes
every point of the three fibres `N_{b_j}` (`fibreSet`, all lifts to the cover).
Here `Ω₀ = Bundle.Cubic.OmegaT P 0`.

`prop:shd4-maps`: `fN_smooth`, `fN_symplectic` (`(f_i^N)^* Ω₀ = ω_std`), `fN_eq_imp`,
`fN_disjoint`, `fN_avoid_fibres`, `fN_mem` (values in `N_{p<h}`), on `𝔹_{ρ̂_i} = srcBall P i`.
-/

noncomputable section

namespace SymplecticPacking.Strip.Cubic

open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Forms (dc pull2 Form2)
open SymplecticPacking.Bundle (pE annulus bpoints)
open SymplecticPacking.Handle (chartA chartInv bandE)
open SymplecticPacking.Handle.Cubic (OmegaFinal OmegaPre DlamInv Dlam)
open scoped ContDiff Real

/-! ### The three fibres -/

variable (P : Branch2.VCubic)

/-! ### `𝒟⁻¹` in global coordinates -/

/-- **`𝒟⁻¹` in the global frame**: `chartA ∘ 𝒟₁⁻¹` (local `𝒜⁺`-frame → global `Zunit`-frame). -/
def DinvN (Y : E4) : E4 := chartA (DlamInv P 1 Y)

@[simp] lemma DlamInv_apply2 (Y : E4) : DlamInv P 1 Y 2 = Y 2 := by simp [DlamInv]
@[simp] lemma DlamInv_apply3 (Y : E4) : DlamInv P 1 Y 3 = Y 3 := by simp [DlamInv]
@[simp] lemma DinvN_apply2 (Y : E4) : DinvN P Y 2 = Y 2 := by simp [DinvN]

lemma band_of_annulus {Y : E4} (hY : Y 2 ∈ annulus) : Y ∈ bandE :=
  Handle.annulus_subset_annulusPlus hY

/-- `𝒟⁻¹` maps `𝒜 × {p < h}` into itself. -/
theorem pE_DlamInv_lt {Y : E4} (hY : Y 2 ∈ annulus) (hp : pE Y < P.h) : pE (DlamInv P 1 Y) < P.h := by
  have hS := (Handle.Cubic.OmegaFinal_eq_pullback P).2.2.2.2.2.2
  have hmem : Y ∈ Dlam P 1 '' {X : E4 | X 2 ∈ annulus ∧ pE X < P.h} := by rw [hS]; exact ⟨hY, hp⟩
  obtain ⟨X, hX, rfl⟩ := hmem
  rw [Handle.Cubic.DlamInv_Dlam]; exact hX.2

theorem pE_DinvN {Y : E4} (hY : Y 2 ∈ annulus) : pE (DinvN P Y) = pE (DlamInv P 1 Y) :=
  Handle.pE_chartA (band_of_annulus (by simpa using hY))

theorem contDiffAt_DinvN {Y : E4} (hY : Y 2 ∈ annulus) : ContDiffAt ℝ ∞ (DinvN P) Y := by
  have h1 := (Handle.Cubic.contDiff_DlamInv P 1).contDiffAt (x := Y)
  have h2 := Handle.contDiffAt_chartA (band_of_annulus (Y := DlamInv P 1 Y) (by simpa using hY))
  exact h2.comp Y h1

/-- **`(𝒟⁻¹)^* Ω_final = Ω_pre`** over the annulus (`prop:shd4-third`). -/
theorem DinvN_pullback {Y : E4} (hY : Y 2 ∈ annulus) :
    pull2 (DinvN P) (OmegaFinal P) Y = OmegaPre P Y := by
  obtain ⟨hpull, -, hDinv, -, hinv2, -, -⟩ := Handle.Cubic.OmegaFinal_eq_pullback P
  have hW : DlamInv P 1 Y 2 ∈ annulus := by simpa using hY
  have hd1 : DifferentiableAt ℝ (DlamInv P 1) Y := hDinv.differentiable (by simp) Y
  have hd2 : DifferentiableAt ℝ chartA (DlamInv P 1 Y) :=
    (Handle.contDiffAt_chartA (band_of_annulus hW)).differentiableAt (by simp)
  have hd3 : DifferentiableAt ℝ (Dlam P 1) (DlamInv P 1 Y) :=
    (Handle.Cubic.contDiff_Dlam P 1).differentiable (by simp) _
  rw [show DinvN P = chartA ∘ DlamInv P 1 from rfl, Forms.pull2_comp_apply hd1 hd2,
    pull2_congr_pt (φ := DlamInv P 1) (hpull _ hW), ← Forms.pull2_comp_apply hd1 hd3]
  have hid : Dlam P 1 ∘ DlamInv P 1 = id := funext hinv2
  ext a b
  rw [Forms.pull2_apply, hid, fderiv_id]
  rfl

/-! ### The Moser flow as a parameter -/

/-- **What `prop:shd4-maps` uses of the Moser flow `Φ`** (`prop:shd4-moser`), with
`Ω₀ = OmegaT P 0`: `Φ⁻¹` is smooth on `{p < h}`, `(Φ⁻¹)^* Ω₀ = Ω_final` there, `Φ⁻¹` maps
`{p < h}` into itself with left inverse `Φ`, and `Φ` fixes the three fibres pointwise. -/
structure PhiInvSpec (Phi PhiInv : E4 → E4) : Prop where
  smooth : ∀ X, pE X < P.h → ContDiffAt ℝ ∞ PhiInv X
  pullback : ∀ X, pE X < P.h → X 2 ∈ annulus → pull2 PhiInv (Bundle.Cubic.OmegaT P 0) X = OmegaFinal P X
  mapsTo : ∀ X, pE X < P.h → pE (PhiInv X) < P.h
  left_inv : ∀ X, pE X < P.h → Phi (PhiInv X) = X
  fixes : ∀ X ∈ fibreSet, Phi X = X

/-- **The embeddings into the normal bundle** `f_i^N = Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i` (`prop:shd4-maps`),
in the global coordinates of `N`; the same `𝒟` and `Φ` for all `i`. -/
def fN (PhiInv : E4 → E4) (i : ℕ) (X : E4) : E4 := PhiInv (DinvN P (layerMap P i X))

variable {P} {Phi PhiInv : E4 → E4} (hΦ : PhiInvSpec P Phi PhiInv)
include hΦ

/-- The intermediate points: `Y = E_i(X)`, `Z = 𝒟⁻¹(Y)`. -/
theorem fN_aux {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    layerMap P i X 2 ∈ annulus ∧ pE (layerMap P i X) < P.h ∧
      DinvN P (layerMap P i X) 2 ∈ annulus ∧ pE (DinvN P (layerMap P i X)) < P.h := by
  have hY2 := layerMap_mem_annulus P hi1 hik hX
  have hYp : pE (layerMap P i X) < P.h := (layerMap_mem P hi1 hik hX).1.2
  refine ⟨hY2, hYp, by simpa using hY2, ?_⟩
  rw [pE_DinvN P hY2]; exact pE_DlamInv_lt P hY2 hYp

/-- **`prop:shd4-maps`, values in `N_{p<h}`.** -/
theorem fN_mem {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    pE (fN P PhiInv i X) < P.h :=
  hΦ.mapsTo _ (fN_aux hΦ hi1 hik hX).2.2.2

/-- **`prop:shd4-maps`, smoothness.** -/
theorem fN_smooth {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    ContDiffAt ℝ ∞ (fN P PhiInv i) X := by
  obtain ⟨hY2, -, -, hZp⟩ := fN_aux hΦ hi1 hik hX
  exact (hΦ.smooth _ hZp).comp X ((contDiffAt_DinvN P hY2).comp X (layerMap_smooth P hi1 hik hX))

/-- **`prop:shd4-maps`, `(f_i^N)^* Ω₀ = ω_std`.** -/
theorem fN_symplectic {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i)
    (v w : E4) : pull2 (fN P PhiInv i) (Bundle.Cubic.OmegaT P 0) X v w = omega0 v w := by
  obtain ⟨hY2, -, hZ2, hZp⟩ := fN_aux hΦ hi1 hik hX
  have hE : DifferentiableAt ℝ (layerMap P i) X :=
    (layerMap_smooth P hi1 hik hX).differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (DinvN P) (layerMap P i X) :=
    (contDiffAt_DinvN P hY2).differentiableAt (by simp)
  have hDE : DifferentiableAt ℝ (DinvN P ∘ layerMap P i) X := hD.comp X hE
  have hF : DifferentiableAt ℝ PhiInv ((DinvN P ∘ layerMap P i) X) :=
    (hΦ.smooth _ hZp).differentiableAt (by simp)
  rw [show fN P PhiInv i = PhiInv ∘ (DinvN P ∘ layerMap P i) from rfl,
    Forms.pull2_comp_apply hDE hF,
    pull2_congr_pt (φ := DinvN P ∘ layerMap P i) (Ω' := OmegaFinal P) (hΦ.pullback _ hZp hZ2),
    Forms.pull2_comp_apply hE hD,
    pull2_congr_pt (φ := layerMap P i) (Ω' := OmegaPre P) (DinvN_pullback P hY2)]
  exact layerMap_symplectic P hi1 hik hX v w

/-- Equal values of `f^N` come from equal values of the layer maps. -/
theorem fN_eq_imp {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (hj1 : 1 ≤ j) (hjk : j ≤ P.k)
    {X X' : E4} (hX : X ∈ srcBall P i) (hX' : X' ∈ srcBall P j)
    (h : fN P PhiInv i X = fN P PhiInv j X') : layerMap P i X = layerMap P j X' := by
  obtain ⟨hY2, -, hZ2, hZp⟩ := fN_aux hΦ hi1 hik hX
  obtain ⟨hY2', -, hZ2', hZp'⟩ := fN_aux hΦ hj1 hjk hX'
  have h1 := congrArg Phi h
  simp only [fN] at h1
  rw [hΦ.left_inv _ hZp, hΦ.left_inv _ hZp'] at h1
  have h2 := congrArg chartInv h1
  simp only [DinvN] at h2
  rw [Handle.chartInv_chartA (band_of_annulus (by simpa using hY2)),
    Handle.chartInv_chartA (band_of_annulus (by simpa using hY2'))] at h2
  have h3 := congrArg (Dlam P 1) h2
  rwa [Handle.Cubic.Dlam_DlamInv, Handle.Cubic.Dlam_DlamInv] at h3

/-- **`prop:shd4-maps`, disjointness**: same `𝒟`, same `Φ` for all `i`. -/
theorem fN_disjoint {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (hj1 : 1 ≤ j) (hjk : j ≤ P.k)
    (hij : i ≠ j) : Disjoint (fN P PhiInv i '' srcBall P i) (fN P PhiInv j '' srcBall P j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨X, hX, rfl⟩ ⟨X', hX', h⟩
  have := fN_eq_imp hΦ hj1 hjk hi1 hik hX' hX h
  exact Set.disjoint_left.mp (layerMap_disjoint P hi1 hik hj1 hjk hij) ⟨X, hX, rfl⟩ ⟨X', hX', this⟩

/-- **`prop:shd4-maps`, the three fibres**: the images avoid `N_{b_1}, N_{b_2}, N_{b_3}`. -/
theorem fN_avoid_fibres {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    fN P PhiInv i X ∉ fibreSet := by
  obtain ⟨-, -, hZ2, hZp⟩ := fN_aux hΦ hi1 hik hX
  intro hF
  have h := hΦ.left_inv _ hZp
  rw [show PhiInv (DinvN P (layerMap P i X)) = fN P PhiInv i X from rfl, hΦ.fixes _ hF] at h
  exact not_mem_fibreSet hZ2 (by rw [← h]; exact hF)

end SymplecticPacking.Strip.Cubic
