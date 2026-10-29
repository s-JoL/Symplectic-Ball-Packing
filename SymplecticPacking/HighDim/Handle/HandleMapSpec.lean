import SymplecticPacking.HighDim.Handle.HandleMap
import SymplecticPacking.HighDim.Handle.RelMoser

/-!
# The handle map `𝒟` as an explicit composite of two cut-off Moser maps

The two handle-path endpoints `ψ₁, ψ₂` are the explicit time-one maps `horizontalMoserMap`
(`Handle/RelMoser.lean`) of the cut-off Moser fields of the library's first and second handle
paths (`globalSurfaceFirstPath_moser_endpoint`, `globalSurfaceSecondPath_moser_endpoint` give
the corresponding existence statements), with the cutoffs `χ₁, χ₂` as explicit parameters:

* `handleFirstMap`  : the first path (suspension of `Φ` over the annulus with the dual band);
* `handleSecondMap` : the second path (layer splitting with clocks `ρ`, `ρ₀` and caps `h`);
* `handleCutComposite` : `handleFirstMap.trans handleSecondMap`.

`handleCutComposite_spec` proves that the composite preserves the region and its interior and
carries the coupling of `Γ` to the second-path form at time one, under the hypotheses of the
library endpoints plus the four standard cutoff conditions of `horizontalMoserMap_spec` for each
cutoff. `handleMapCut` and `handleMapCut_spec` specialise it to a toric model with the explicit
`layerClock`/`smoothCap` of `Handle/LayerForm.lean`, i.e. to the target form `layerFormOf`.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ M] [T2Space M] [_root_.NormalSpace M] [SigmaCompactSpace M]
variable {m : ℕ}

/-- The first handle-path family `(t, v) ↦ Γ¹_t(v)` (library `globalSurfaceFirstPrimitive`). -/
def handleFirstPath (D : AnnularHandleData (ℝ × ℝ) M) (b : ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (H : Moments m → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) :
    ℝ × Fibre m → ManifoldOneForm (ℝ × ℝ) M :=
  fun q => D.globalSurfaceFirstPrimitive b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) q

/-- The second handle-path family (library `globalSurfaceSecondPrimitive`). -/
def handleSecondPath {κ : Type*} [Fintype κ] (D : AnnularHandleData (ℝ × ℝ) M) (b : ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (K H : Moments m → ℝ)
    (h : κ → Fibre m → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) :
    ℝ × Fibre m → ManifoldOneForm (ℝ × ℝ) M :=
  fun q => D.globalSurfaceSecondPrimitive b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
    (Γ ∘ planeMoments) q

/-- `ψ₁`: explicit cut-off Moser map of the first handle path. -/
def handleFirstMap (D : AnnularHandleData (ℝ × ℝ) M) (b : ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (H : Moments m → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (χ : ℝ × (M × Fibre m) → ℝ) :
    (M × Fibre m) ≃ₘ⟮𝓘(ℝ, (ℝ × ℝ) × Fibre m), 𝓘(ℝ, (ℝ × ℝ) × Fibre m)⟯ (M × Fibre m) :=
  horizontalMoserMap phaseArea (handleFirstPath D b Φ H Γ) χ

/-- `ψ₂`: explicit cut-off Moser map of the second handle path. -/
def handleSecondMap {κ : Type*} [Fintype κ] (D : AnnularHandleData (ℝ × ℝ) M) (b : ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (K H : Moments m → ℝ)
    (h : κ → Fibre m → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (χ : ℝ × (M × Fibre m) → ℝ) :
    (M × Fibre m) ≃ₘ⟮𝓘(ℝ, (ℝ × ℝ) × Fibre m), 𝓘(ℝ, (ℝ × ℝ) × Fibre m)⟯ (M × Fibre m) :=
  horizontalMoserMap phaseArea (handleSecondPath D b Φ K H h ρ ρ₀ Γ) χ

/-- `𝒟 = ψ₂ ∘ ψ₁` with explicit cutoffs. -/
def handleCutComposite {κ : Type*} [Fintype κ] (D : AnnularHandleData (ℝ × ℝ) M) (b : ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (K H : Moments m → ℝ)
    (h : κ → Fibre m → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (χ₁ χ₂ : ℝ × (M × Fibre m) → ℝ) :
    (M × Fibre m) ≃ₘ⟮𝓘(ℝ, (ℝ × ℝ) × Fibre m), 𝓘(ℝ, (ℝ × ℝ) × Fibre m)⟯ (M × Fibre m) :=
  (handleFirstMap D b Φ H Γ χ₁).trans (handleSecondMap D b Φ K H h ρ ρ₀ Γ χ₂)

/-- The standard conditions on a Moser cutoff `χ` for a path family `P` on the closed set
`Icc 0 1 × S` (those of `horizontalMoserMap_spec`). -/
structure MoserCutoff (P : ℝ × Fibre m → ManifoldOneForm (ℝ × ℝ) M)
    (χ : ℝ × (M × Fibre m) → ℝ) (S : Set (M × Fibre m)) : Prop where
  smooth : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (ℝ × ℝ) × Fibre m)) 𝓘(ℝ, ℝ) ∞ χ
  supp : tsupport χ ⊆
    {p | (manifoldExteriorOneForm (horizontalPath phaseArea P p.1) p.2).IsInvertible}
  one : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ S), χ p = 1
  compact : ∃ K : Set (Fibre m), IsCompact K ∧ ∀ t z, z.2 ∉ K → χ (t, z) = 0

/-- **Explicit first handle path endpoint** (explicit form of the library's
`globalSurfaceFirstPath_moser_endpoint`). -/
theorem handleFirstMap_spec
    (D : AnnularHandleData (ℝ × ℝ) M)
    {b : ℝ} (hb : 0 < b) (hbw : b < D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm (ℝ × ℝ) M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v, Λ x u v = -Λ x v u)
    (hpΛ : ∀ c y, y ∈ (extChartAt 𝓘(ℝ, ℝ × ℝ) c).target → 0 < chartTwoForm Λ c y (1, 0) (0, 1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm (ℝ × ℝ) M}
    (hγ : ∀ x ∈ D.chart.target, ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ, ℝ × ℝ) x x))
    (hdγ : ∀ x ∈ D.chart.target, manifoldExteriorOneForm γ x = r • Λ x)
    {Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M} (hΓ : SmoothOneFormFamily Γ)
    {H : Moments m → ℝ} (hH : ContDiff ℝ ∞ H) {Y : Set (Moments m)} (hHp : ∀ p ∈ Y, 0 ≤ H p)
    {Kbase : Set M} (heD : D.chart.target ⊆ interior Kbase)
    (hbase : ∀ p ∈ Y, ∀ x ∈ Kbase, 0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ, ℝ × ℝ) x x) (1, 0) (0, 1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' AnnularHandleData.band b ⊆ W)
    (hWA : W ⊆ D.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {J : Type*} (F : J → Moments m → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j, α j < c j)
    (hYeq : planeMoments ⁻¹' Y = {v | ∀ j, (F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v, α j < (F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t, v)) = 0)
    {χ : ℝ × (M × Fibre m) → ℝ}
    (hχ : MoserCutoff (handleFirstPath D b Φ H Γ) χ (Kbase ×ˢ (planeMoments ⁻¹' Y))) :
    handleFirstMap D b Φ H Γ χ '' (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      handleFirstMap D b Φ H Γ χ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn (handleFirstMap D b Φ H Γ χ)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (fun v =>
          D.globalSurfaceFirstPrimitive b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1, v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) := by
  have hSD : D.chart '' AnnularHandleData.band b ⊆ interior Kbase :=
    (D.image_band_subset_target hbw).trans heD
  have hparam : ∀ x, ContDiff ℝ ∞ (fun p => Γ p x) :=
    fun x => contDiff_iff_contDiffAt.mpr (fun p => hΓ.parameter_contDiffAt p x)
  have h1 := hχ.one
  rw [hYeq] at h1
  obtain ⟨hD, hI, hp, -⟩ := horizontalMoserMap_spec phaseArea_isInvertible phaseArea_skew
    (globalSurfaceFirstPrimitive_smooth D hb hbw Φ
      (hH.comp planeMoments_smooth) (hΓ.comp planeMoments_smooth))
    (D.image_band_compact hbw) hSD
    (fun x hx t v => by
      rw [AnnularHandleData.globalSurfaceFirstPrimitive_off_band D hb Φ _ _ (t, v) hx,
        AnnularHandleData.globalSurfaceFirstPrimitive_zero])
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => globalSurfaceFirstPrimitive_collarInvariant D b Φ phaseArea_isInvertible
      phaseArea_skew (((hF j).comp planeMoments_smooth).differentiable (by simp)) (hzero j)
      (toric_collarInvariant (hF j) hH (α j))
      (fun x => toric_collarInvariant (hF j) (hparam x) (α j)) t x)
    (fun t ht z hz => globalSurfaceFirstPath_isInvertible D hb hbw hor hΛ hsΛ hpΛ
      hr hγ hdγ hΓ hH hHp hbase hW hBW hWA hN Φ hΦ ht (by simpa only [hYeq] using hz))
    hχ.smooth hχ.supp h1 hχ.compact
  refine ⟨?_, ?_, ?_⟩
  · rw [← hYeq] at hD
    exact hD
  · rw [← hYeq] at hI
    exact hI
  · have hp' := hp
    simp only [AnnularHandleData.globalSurfaceFirstPrimitive_zero] at hp'
    rw [← hYeq] at hp'
    exact hp'

/-- **Explicit second handle path endpoint** (explicit form of the library's
`globalSurfaceSecondPath_moser_endpoint`). -/
theorem handleSecondMap_spec {κ : Type*} [Fintype κ]
    (D : AnnularHandleData (ℝ × ℝ) M)
    {b : ℝ} (hb : 0 < b) (hbw : b < D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm (ℝ × ℝ) M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v, Λ x u v = -Λ x v u)
    (hpΛ : ∀ c y, y ∈ (extChartAt 𝓘(ℝ, ℝ × ℝ) c).target → 0 < chartTwoForm Λ c y (1, 0) (0, 1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm (ℝ × ℝ) M}
    (hγ : ∀ x ∈ D.chart.target, ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ, ℝ × ℝ) x x))
    (hdγ : ∀ x ∈ D.chart.target, manifoldExteriorOneForm γ x = r • Λ x)
    {Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M} (hΓ : SmoothOneFormFamily Γ)
    {K H : Moments m → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (Moments m)}
    (hHp : ∀ p ∈ Y, 0 ≤ H p)
    {Kbase : Set M} (heD : D.chart.target ⊆ interior Kbase) (hβD : tsupport D.dual ⊆ interior Kbase)
    (hbase : ∀ p ∈ Y, ∀ x ∈ Kbase, 0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ, ℝ × ℝ) x x) (1, 0) (0, 1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' AnnularHandleData.band b ⊆ W)
    (hWA : W ⊆ D.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → Fibre m → ℝ} (hh : ∀ i, ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s, s ≤ -b → (∀ i, ρ i s = 0) ∧ ρ₀ s = 0)
    (hhi : ∀ s, b ≤ s → (∀ i, ρ i s = 1) ∧ ρ₀ s = 1)
    (hclock : ∀ i s, 0 ≤ deriv (ρ i) s) (hclock₀ : ∀ s, 0 ≤ deriv ρ₀ s)
    (hcap : ∀ v, planeMoments v ∈ Y → ∀ i, 0 ≤ h i v)
    (hres : ∀ v, planeMoments v ∈ Y →
      0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {J : Type*} (F : J → Moments m → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j, α j < c j)
    (hYeq : planeMoments ⁻¹' Y = {v | ∀ j, (F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v, α j < (F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t, v)) = 0)
    (hhInv : ∀ j i, CollarInvariant phaseArea (F j ∘ planeMoments) (α j) (h i))
    {χ : ℝ × (M × Fibre m) → ℝ}
    (hχ : MoserCutoff (handleSecondPath D b Φ K H h ρ ρ₀ Γ) χ (Kbase ×ˢ (planeMoments ⁻¹' Y))) :
    handleSecondMap D b Φ K H h ρ ρ₀ Γ χ '' (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      handleSecondMap D b Φ K H h ρ ρ₀ Γ χ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn (handleSecondMap D b Φ K H h ρ ρ₀ Γ χ)
        (globalHorizontalCoupling phaseArea (fun v =>
          D.globalSurfaceFirstPrimitive b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1, v)))
        (globalHorizontalCoupling phaseArea (fun v =>
          D.globalSurfaceSecondPrimitive b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
            (Γ ∘ planeMoments) (1, v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) := by
  have hSD : (D.chart '' AnnularHandleData.band b) ∪ tsupport D.dual ⊆ interior Kbase :=
    union_subset ((D.image_band_subset_target hbw).trans heD) hβD
  have hparam : ∀ x, ContDiff ℝ ∞ (fun p => Γ p x) :=
    fun x => contDiff_iff_contDiffAt.mpr (fun p => hΓ.parameter_contDiffAt p x)
  have h1 := hχ.one
  rw [hYeq] at h1
  obtain ⟨hD, hI, hp, -⟩ := horizontalMoserMap_spec phaseArea_isInvertible phaseArea_skew
    (globalSurfaceSecondPrimitive_smooth D hb hbw Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth) hh hρ hρ₀ hlo hhi
      (hΓ.comp planeMoments_smooth))
    ((D.image_band_compact hbw).union D.dual_compact) hSD
    (fun x hx t v => by
      have hb' : x ∉ D.chart '' AnnularHandleData.band b := fun h => hx (Or.inl h)
      have hf' : D.dual x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
      rw [globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (t, v) hb',
        globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (0, v) hb', hf']
      simp)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => globalSurfaceSecondPrimitive_collarInvariant D b Φ phaseArea_isInvertible
      phaseArea_skew (((hF j).comp planeMoments_smooth).differentiable (by simp)) (hzero j)
      (toric_collarInvariant (hF j) hK (α j)) (toric_collarInvariant (hF j) hH (α j))
      (hhInv j) ρ ρ₀ (fun x => toric_collarInvariant (hF j) (hparam x) (α j)) t x)
    (fun t ht z hz => globalSurfaceSecondPath_isInvertible D hb hbw hor hΛ hsΛ hpΛ
      hr hγ hdγ hΓ hK hH hHp hbase hW hBW hWA hN Φ hΦ hh hρ hρ₀ hlo hhi hclock hclock₀
      hcap hres ht (by simpa only [hYeq] using hz))
    hχ.smooth hχ.supp h1 hχ.compact
  refine ⟨?_, ?_, ?_⟩
  · rw [← hYeq] at hD
    exact hD
  · rw [← hYeq] at hI
    exact hI
  · have hp' := hp
    simp only [AnnularHandleData.globalSurfaceSecondPrimitive_zero] at hp'
    rw [← hYeq] at hp'
    exact hp'

/-- **Composite handle map with explicit cutoffs.** `ψ₂ ∘ ψ₁` preserves `Kbase × Y`, its
interior, and carries the coupling of `Γ` to the second-path form at time one. -/
theorem handleCutComposite_spec {κ : Type*} [Fintype κ]
    (D : AnnularHandleData (ℝ × ℝ) M)
    {b : ℝ} (hb : 0 < b) (hbw : b < D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm (ℝ × ℝ) M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v, Λ x u v = -Λ x v u)
    (hpΛ : ∀ c y, y ∈ (extChartAt 𝓘(ℝ, ℝ × ℝ) c).target → 0 < chartTwoForm Λ c y (1, 0) (0, 1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm (ℝ × ℝ) M}
    (hγ : ∀ x ∈ D.chart.target, ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ, ℝ × ℝ) x x))
    (hdγ : ∀ x ∈ D.chart.target, manifoldExteriorOneForm γ x = r • Λ x)
    {Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M} (hΓ : SmoothOneFormFamily Γ)
    {K H : Moments m → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (Moments m)}
    (hHp : ∀ p ∈ Y, 0 ≤ H p)
    {Kbase : Set M} (heD : D.chart.target ⊆ interior Kbase) (hβD : tsupport D.dual ⊆ interior Kbase)
    (hbase : ∀ p ∈ Y, ∀ x ∈ Kbase, 0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ, ℝ × ℝ) x x) (1, 0) (0, 1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' AnnularHandleData.band b ⊆ W)
    (hWA : W ⊆ D.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → Fibre m → ℝ} (hh : ∀ i, ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s, s ≤ -b → (∀ i, ρ i s = 0) ∧ ρ₀ s = 0)
    (hhi : ∀ s, b ≤ s → (∀ i, ρ i s = 1) ∧ ρ₀ s = 1)
    (hclock : ∀ i s, 0 ≤ deriv (ρ i) s) (hclock₀ : ∀ s, 0 ≤ deriv ρ₀ s)
    (hcap : ∀ v, planeMoments v ∈ Y → ∀ i, 0 ≤ h i v)
    (hres : ∀ v, planeMoments v ∈ Y →
      0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {J : Type*} (F : J → Moments m → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j, α j < c j)
    (hYeq : planeMoments ⁻¹' Y = {v | ∀ j, (F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v, α j < (F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t, v)) = 0)
    (hhInv : ∀ j i, CollarInvariant phaseArea (F j ∘ planeMoments) (α j) (h i))
    {χ₁ χ₂ : ℝ × (M × Fibre m) → ℝ}
    (hχ₁ : MoserCutoff (handleFirstPath D b Φ H Γ) χ₁ (Kbase ×ˢ (planeMoments ⁻¹' Y)))
    (hχ₂ : MoserCutoff (handleSecondPath D b Φ K H h ρ ρ₀ Γ) χ₂
      (Kbase ×ˢ (planeMoments ⁻¹' Y))) :
    handleCutComposite D b Φ K H h ρ ρ₀ Γ χ₁ χ₂ '' (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      handleCutComposite D b Φ K H h ρ ρ₀ Γ χ₁ χ₂ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) =
        interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn (handleCutComposite D b Φ K H h ρ ρ₀ Γ χ₁ χ₂)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (fun v =>
          D.globalSurfaceSecondPrimitive b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
            (Γ ∘ planeMoments) (1, v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) := by
  obtain ⟨hD₁, hI₁, hf₁⟩ := handleFirstMap_spec D hb hbw hor hΛ hsΛ hpΛ hr hγ hdγ hΓ hH hHp
    heD hbase hW hBW hWA hN Φ hΦ F hF α c hαc hYeq hYC hzero hχ₁
  obtain ⟨hD₂, hI₂, hf₂⟩ := handleSecondMap_spec D hb hbw hor hΛ hsΛ hpΛ hr hγ hdγ hΓ hK hH
    hHp heD hβD hbase hW hBW hWA hN Φ hΦ hh hρ hρ₀ hlo hhi hclock hclock₀ hcap hres F hF α c
    hαc hYeq hYC hzero hhInv hχ₂
  refine ⟨image_trans_eq _ _ hD₁ hD₂, image_trans_eq _ _ hI₁ hI₂, ?_⟩
  exact hf₁.trans hf₂ (fun z hz => hD₁ ▸ mem_image_of_mem _ hz)

variable {q k : ℕ}

/-- The handle map of a toric model with explicit layer clocks and caps and cutoffs `χ₁, χ₂`. -/
def handleMapCut (T : ToricModel M m q)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m))) (K H : Moments m → ℝ)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (a r : Fin k → ℝ)
    (χ₁ χ₂ : ℝ × (M × Fibre m) → ℝ) :
    (M × Fibre m) ≃ₘ⟮𝓘(ℝ, (ℝ × ℝ) × Fibre m), 𝓘(ℝ, (ℝ × ℝ) × Fibre m)⟯ (M × Fibre m) :=
  handleCutComposite T.handle T.hb Φ K H (fun i => smoothCap a r i ∘ planeMoments)
    (fun i => layerClock (k + 1) (-T.hb) T.hb i.castSucc)
    (layerClock (k + 1) (-T.hb) T.hb (Fin.last k)) Γ χ₁ χ₂

/-- **The handle map.** `handleMapCut` preserves `T.region` and its interior and carries the
coupling of `Γ` to `layerFormOf`, given the normal-form hypotheses on `Γ, H`, the comparator
hypotheses on `Φ, K`, and Moser cutoffs `χ₁, χ₂` on `T.region`. -/
theorem handleMapCut_spec (T : ToricModel M m q) (hT : T.Spec)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    {K H : Moments m → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M} (hΓ : SmoothOneFormFamily Γ)
    {a r' : Fin k → ℝ} (hra : ∀ i, r' i < a i)
    (hHp : ∀ p ∈ region T.Δ.b T.Δ.ℓ, 0 ≤ H p)
    (hbase : ∀ p ∈ region T.Δ.b T.Δ.ℓ, ∀ x ∈ T.base,
      0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
        (extChartAt 𝓘(ℝ, ℝ × ℝ) x x) (1, 0) (0, 1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm (ℝ × ℝ) M}
    (hγ : ∀ x ∈ T.handle.chart.target, ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ, ℝ × ℝ) x x))
    (hdγ : ∀ x ∈ T.handle.chart.target, manifoldExteriorOneForm γ x = r • T.Λ x)
    {W : Set M} (hW : IsOpen W) (hBW : T.handle.chart '' AnnularHandleData.band T.hb ⊆ W)
    (hWA : W ⊆ T.handle.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo (Φ.map t) (planeRegion T.Δ.b T.Δ.ℓ) (planeRegion T.Δ.b T.Δ.ℓ) ∧
      MapsTo (Φ.map t).symm (planeRegion T.Δ.b T.Δ.ℓ) (planeRegion T.Δ.b T.Δ.ℓ))
    (hres : ∀ v, planeMoments v ∈ region T.Δ.b T.Δ.ℓ →
      0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
        (fun i => smoothCap a r' i ∘ planeMoments) (Φ.map 1).symm v)
    {J : Type*} (F : J → Moments m → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j, α j < c j)
    (hYeq : planeRegion T.Δ.b T.Δ.ℓ = {v | ∀ j, (F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeRegion T.Δ.b T.Δ.ℓ))
    (hzero : ∀ j t v, α j < (F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t, v)) = 0)
    (hhInv : ∀ j i, CollarInvariant phaseArea (F j ∘ planeMoments) (α j)
      (smoothCap a r' i ∘ planeMoments))
    {χ₁ χ₂ : ℝ × (M × Fibre m) → ℝ}
    (hχ₁ : MoserCutoff (handleFirstPath T.handle T.hb Φ H Γ) χ₁ T.region)
    (hχ₂ : MoserCutoff (handleSecondPath T.handle T.hb Φ K H
      (fun i => smoothCap a r' i ∘ planeMoments)
      (fun i => layerClock (k + 1) (-T.hb) T.hb i.castSucc)
      (layerClock (k + 1) (-T.hb) T.hb (Fin.last k)) Γ) χ₂ T.region) :
    handleMapCut T Φ K H Γ a r' χ₁ χ₂ '' T.region = T.region ∧
      handleMapCut T Φ K H Γ a r' χ₁ χ₂ '' interior T.region = interior T.region ∧
      PreservesTwoFormOn (handleMapCut T Φ K H Γ a r' χ₁ χ₂)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
        (layerFormOf T Φ K H Γ a r') T.region := by
  have heD : T.handle.chart.target ⊆ interior T.base := subset_closure.trans hT.handle_in_base
  have hb := hT.hb_pos
  exact handleCutComposite_spec T.handle hb hT.hb_lt hT.handle_orient hT.Λ_smooth hT.Λ_skew
    hT.Λ_pos hr hγ hdγ hΓ hK hH hHp heD hT.dual_in_base hbase hW hBW hWA hN Φ hΦ
    (h := fun i => smoothCap a r' i ∘ planeMoments)
    (fun i => (smoothCap_smooth a r' i).comp planeMoments_smooth)
    (ρ := fun i : Fin k => layerClock (k + 1) (-T.hb) T.hb i.castSucc)
    (fun i => (layerClocks_spec (k + 1) (by linarith : -T.hb < T.hb)).2.2.1 _ |>.1)
    ((layerClocks_spec (k + 1) (by linarith : -T.hb < T.hb)).2.2.1 _).1
    (fun s hs => ⟨fun i => layerClock_lo hb _ hs, layerClock_lo hb _ hs⟩)
    (fun s hs => ⟨fun i => layerClock_hi hb _ hs, layerClock_hi hb _ hs⟩)
    (fun i s => ((layerClocks_spec (k + 1) (by linarith : -T.hb < T.hb)).2.2.2.1 _ s).2.2)
    (fun s => ((layerClocks_spec (k + 1) (by linarith : -T.hb < T.hb)).2.2.2.1 _ s).2.2)
    (fun v _ i => smoothCap_nonneg (hra i) _) hres F hF α c hαc hYeq hYC hzero hhInv hχ₁ hχ₂

end SymplecticPacking.HighDim.ToricPackingStages
