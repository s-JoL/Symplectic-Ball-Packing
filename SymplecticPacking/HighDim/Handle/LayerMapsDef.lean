import SymplecticPacking.HighDim.Handle.LayerMaps
import SymplecticPacking.Strip.Map
import OAI.Geometry.BallPacking.Moser.AnnularFinalPacking
import OAI.Geometry.BallPacking.Layers.LayerBallEmbedding
import OAI.Geometry.BallPacking.Annuli.LayerCoordinates

/-!
# The explicit layer maps `E_i` (paper thm:mech-packing, layer stage)

The OpenAI library obtains the ball embeddings into the split layer form existentially
(`exists_global_surface_final_packing` → `exists_final_surface_layer_packing` →
`finite_weighted_layer_packing` → `finite_area_layer_packing` → `finite_layer_packing_local` →
`exists_ball_in_layer_local`). Unwinding these proofs, the `i`-th ball map is the composite

  `E_i = U ∘ R_g ∘ L_i⁻¹ ∘ (q × id) ∘ s`,

where
* `s = complexSplitPhase m : ℂ^{m+1} ≅ ℝ² × ℂ^m` splits off the first complex coordinate;
* `q` is a thin area-preserving planar map with `0 < x(q z) < π|z|² + δ`, `0 < T(q z) < 1`
  (library leaf `exists_thin_planar_embedding`); here it is the explicit strip map
  `Strip.psiStrip` of the four-dimensional construction (`thinPlanar`);
* `L_i = layerChart F_i f_i` is the `i`-th layer chart, `F_i = (K − H) + Σ_{j<i} h_j` the
  Hamiltonian below the `i`-th layer, `f_i = areaLayerCoordinate ℓ lo_i ρ_i h_i` the area
  coordinate with the explicit clocks `layerClock` and caps `smoothCap`, and its inverse is the
  explicit definite description `layerChartInv` (`Handle/LayerMaps.lean`);
* `ℓ = normalizedAreaDensity A B g` is the normalized base density, with the explicit
  circle-clock inverse `g = circleClockInv δ` and the annular coefficients `A, B` of the
  background primitive `γ` (the part of the normalized primitive not carried by the handle,
  `handleBackground`);
* `R_g = angularReparam g` and `U = annularUnshearMap` (handle cover and inverse comparator
  shear).

Every ingredient is an explicit definition (formulas, integrals, unique preimages, flows).
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Manifold
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Manifold Real

namespace ToricPackingStages

/-! ### The explicit thin planar map -/

/-- The thin planar map: the explicit strip map `Ψ_strip` of `Strip/Map.lean`, read in the
coordinates `(x, T)` of the plane. -/
def thinPlanar (δ : ℝ) (x : Plane) : Plane :=
  ((Strip.psiStrip δ ⟨x.1, x.2⟩).re, (Strip.psiStrip δ ⟨x.1, x.2⟩).im)

/-- The thin planar map on the first factor of `ℝ² × ℂ^m`. -/
def thinProduct {ι : Type*} (δ : ℝ) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  (thinPlanar δ p.1, p.2)

theorem thinPlanar_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (thinPlanar δ) := by
  have hc : ContDiff ℝ ∞ (fun x : Plane => (⟨x.1, x.2⟩ : ℂ)) := by
    have : (fun x : Plane => (⟨x.1, x.2⟩ : ℂ)) =
        fun x : Plane => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [this]
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have hp := (Strip.psiStrip_smooth hδ).comp hc
  exact (Complex.reCLM.contDiff.comp hp).prodMk (Complex.imCLM.contDiff.comp hp)

/-- The strip estimate of the thin planar map (the bound of the library's
`exists_thin_planar_embedding`, with margin `δ / 2`). -/
theorem thinPlanar_bound {δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    0 < (thinPlanar δ x).1 ∧ (thinPlanar δ x).1 < radialArea x + δ / 2 ∧
      (thinPlanar δ x).2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1, h2⟩ := Strip.psiStrip_mem hδ ⟨x.1, x.2⟩
  have hlt := Strip.psiStrip_x_lt hδ ⟨x.1, x.2⟩
  have hn : ‖(⟨x.1, x.2⟩ : ℂ)‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn] at hlt
  refine ⟨h0, ?_, h1, h2⟩
  change (Strip.psiStrip δ ⟨x.1, x.2⟩).re < Real.pi * radiusSq x + δ / 2
  simpa [radiusSq] using hlt

/-! ### The ingredients of the layer maps -/

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ M]
variable {m q k : ℕ}

/-- The background primitive `γ` near the handle band: the normalized primitive at `p = 0`
minus its handle part `clock_b(s) H(0) · dual` (on a neighbourhood of the band the normalized
primitive is `γ + clock_b(s) H(p) · dual`, so this is independent of `p` there). -/
def handleBackground (T : ToricModel M m q) (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M)
    (H : Moments m → ℝ) : ManifoldOneForm (ℝ × ℝ) M :=
  Γ 0 - H 0 • T.handle.clockPrimitive T.hb

/-- The formula for the background recovers any common background on a handle-normal
neighbourhood, so it introduces no choice of primitive. -/
theorem handleBackground_eq_on (T : ToricModel M m q)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (H : Moments m → ℝ)
    {γ : ManifoldOneForm (ℝ × ℝ) M} {W : Set M}
    (hWA : W ⊆ T.handle.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x)
    (x : M) (hx : x ∈ W) : handleBackground T Γ H x = γ x := by
  unfold handleBackground
  change Γ 0 x - H 0 • T.handle.clockPrimitive T.hb x = γ x
  rw [hN 0 x hx, T.handle.clockPrimitive_eq T.hb (hWA hx)]
  apply ContinuousLinearMap.ext
  intro v
  change γ x v + _ * T.handle.dual x v - H 0 * (_ * T.handle.dual x v) = γ x v
  ring

theorem handleBackground_normal (T : ToricModel M m q)
    (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (H : Moments m → ℝ)
    {γ : ManifoldOneForm (ℝ × ℝ) M} {W : Set M}
    (hWA : W ⊆ T.handle.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x) :
    ∀ p x, x ∈ W → Γ p x = handleBackground T Γ H x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x := by
  intro p x hx
  rw [handleBackground_eq_on T Γ H hWA hN x hx]
  exact hN p x hx

/-- The normalized base area density `ℓ = normalizedAreaDensity A B g` of the layer charts:
`A, B` the annular coefficients of the background `γ`, `g` the explicit circle-clock inverse. -/
def layerDensity (T : ToricModel M m q) (γ : ManifoldOneForm (ℝ × ℝ) M) : Plane → ℝ :=
  normalizedAreaDensity (T.handle.annularCoverA γ) (T.handle.annularCoverB γ)
    (circleClockInv T.hδ)

/-- The Hamiltonian below the `i`-th layer: `F_i = (K − H) + Σ_{j<i} h_j`. -/
def layerBelow (K H : Moments m → ℝ) (a r : Fin k → ℝ) (i : Fin k) : Moments m → ℝ :=
  fun p => (K p - H p) + ∑ j ∈ Finset.univ.filter (fun j : Fin k => j < i), smoothCap a r j p

/-- Left end of the `i`-th ball layer in `(−b, b)`. -/
def ballLayerLo (T : ToricModel M m q) (i : Fin k) : ℝ := layerLo (k + 1) (-T.hb) T.hb i.castSucc

/-- Right end of the `i`-th ball layer in `(−b, b)`. -/
def ballLayerHi (T : ToricModel M m q) (i : Fin k) : ℝ := layerHi (k + 1) (-T.hb) T.hb i.castSucc

/-- The `i`-th area layer coordinate `f_i = ∫_{lo_i}^s ℓ + ρ_i(s) h_i(p)`. -/
def layerCoord (T : ToricModel M m q) (γ : ManifoldOneForm (ℝ × ℝ) M) (a r : Fin k → ℝ)
    (i : Fin k) : Plane × Fibre m → ℝ :=
  areaLayerCoordinate (layerDensity T γ) (ballLayerLo T i)
    (layerClock (k + 1) (-T.hb) T.hb i.castSucc) (smoothCap a r i)

/-- The moment region with strict upper faces. Its fibre preimage is open, including the
coordinate axes because all fibre moments are nonnegative automatically. -/
def layerMomentDomain (T : ToricModel M m q) : Set (Moments m) :=
  {p | (∀ j, 0 ≤ p j) ∧ ∀ ν, ∑ j, T.Δ.b ν j * p j < T.Δ.ℓ ν}

theorem layerMomentDomain_open (T : ToricModel M m q) :
    IsOpen (planeMoments ⁻¹' layerMomentDomain T) := by
  have he : planeMoments ⁻¹' layerMomentDomain T =
      {v | ∀ ν, ∑ j, T.Δ.b ν j * planeMoments v j < T.Δ.ℓ ν} := by
    ext v
    exact ⟨fun h => h.2, fun h => ⟨planeMoments_nonneg v, h⟩⟩
  rw [he]
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun ν => isOpen_lt
    ((ContDiff.sum fun j _ => contDiff_const.mul
      ((contDiff_apply ℝ ℝ j).comp planeMoments_smooth)).continuous) continuous_const

theorem layerMomentDomain_subset (T : ToricModel M m q) : layerMomentDomain T ⊆ T.Δ.set :=
  fun _ hp => ⟨hp.1, fun ν => (hp.2 ν).le⟩

/-- Strict upper-face membership follows from any proper positive dilation. -/
theorem layerMomentDomain_of_dilate (T : ToricModel M m q) (hΔ : T.Δ.Spec)
    {τ : ℝ} (hτ : τ < 1) {p : Moments m} (hp : p ∈ (T.Δ.dilate τ).set) :
    p ∈ layerMomentDomain T := by
  refine ⟨hp.1, fun ν => ?_⟩
  exact (hp.2 ν).trans_lt (by
    change τ * T.Δ.ℓ ν < T.Δ.ℓ ν
    nlinarith [hΔ.ℓ_pos ν])

/-- The `i`-th ball map into the split product chart: `L_i⁻¹ ∘ (q × id) ∘ s`, with the thin
planar map of margin `(a_i − r_i)/4`. -/
def layerBallMap (T : ToricModel M m q) (K H : Moments m → ℝ) (γ : ManifoldOneForm (ℝ × ℝ) M)
    (a r : Fin k → ℝ) (i : Fin k) : Ambient (m + 1) → Plane × Fibre m :=
  layerChartInv (layerBelow K H a r i) (layerCoord T γ a r i) (ballLayerLo T i)
      (ballLayerHi T i) (layerMomentDomain T) ∘
    thinProduct ((a i - r i) / 4) ∘ complexSplitPhase m

/-- **The explicit layer maps for given ingredients**: isotopy `Φ`, comparator `K`, handle mass
`H` and normalized primitive `Γ`: `E_i = U ∘ R_g ∘ L_i⁻¹ ∘ (q × id) ∘ s`. -/
def layerMapsOf (T : ToricModel M m q) (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (K H : Moments m → ℝ) (Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M) (a r : Fin k → ℝ)
    (i : Fin k) : Ambient (m + 1) → M × Fibre m :=
  T.handle.annularUnshearMap T.hb Φ ∘ angularReparam (circleClockInv T.hδ) ∘
    layerBallMap T K H (handleBackground T Γ H) a r i

end ToricPackingStages

end SymplecticPacking.HighDim
