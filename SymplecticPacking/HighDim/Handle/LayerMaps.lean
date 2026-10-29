import SymplecticPacking.Explicit
import SymplecticPacking.HighDim.Handle.LayerForm
import OAI.Geometry.BallPacking.Layers.LayerAreaForm
import OAI.Geometry.BallPacking.Layers.SmoothFormTransport
import OAI.Geometry.BallPacking.Annuli.LayerCoordinates

/-!
# Explicit ingredients of the layer maps `E_i` (paper thm:mech-packing, layer stage)

The layer maps of the OpenAI library (`finite_weighted_layer_packing`,
`finite_area_layer_packing`, `exists_ball_in_layer`) are built from three existential leaves:

1. the inverse `g` of the angular circle clock (`positiveCircleClock_inverse`), used for the
   angular reparametrization that normalizes the base area density;
2. the inverse of the layer chart `layerChart F f` (`layerChart_inverse`), which carries the
   split product form to the layer form;
3. the thin area-preserving planar map (`exists_thin_planar_embedding`), which squeezes the
   capacity disc into the strip `0 < x < area + δ`, `0 < y < 1`.

This file gives (1) and (2) as explicit definite descriptions (`Explicit.the` of the unique
preimage) and proves that they have every property the library's witnesses have:
`circleClockInv_spec`, `normalizedArea_spec`, `layerChartInv_local_spec`.
The fixed strip map is defined in `LayerMapsDef.lean` and verified in `ThinPlanarSpec.lean`.
The composite layer maps are verified in `LayerPackingFormula.lean` under the
normalization properties needed from `normalPrimitive`.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Topology

namespace ToricPackingStages

/-! ### (1) The explicit inverse of the angular circle clock -/

open Classical in
/-- The explicit inverse of `t ↦ intervalClock (−b) b (t − 1/2)` on `(1/2 − b, 1/2 + b)`:
the unique preimage of `T` (and `1/2` if there is none). -/
def circleClockInv (b T : ℝ) : ℝ :=
  if h : ∃! t, t ∈ Ioo (1/2 - b) (1/2 + b) ∧ intervalClock (-b) b (t - 1/2) = T then
    SymplecticPacking.Explicit.the h
  else 1/2

/-- The explicit circle-clock inverse agrees with any inverse having the properties of the
library's `positiveCircleClock_inverse`. -/
theorem circleClockInv_eq {b : ℝ} {g : ℝ → ℝ}
    (hm : ∀ T ∈ Ioo (0:ℝ) 1, g T ∈ Ioo (1/2 - b) (1/2 + b))
    (hl : ∀ t ∈ Ioo (1/2 - b) (1/2 + b), g (intervalClock (-b) b (t - 1/2)) = t)
    (hr : ∀ T ∈ Ioo (0:ℝ) 1, intervalClock (-b) b (g T - 1/2) = T)
    {T : ℝ} (hT : T ∈ Ioo (0:ℝ) 1) : circleClockInv b T = g T := by
  have hu : ∃! t, t ∈ Ioo (1/2 - b) (1/2 + b) ∧ intervalClock (-b) b (t - 1/2) = T := by
    refine ⟨g T, ⟨hm T hT, hr T hT⟩, ?_⟩
    rintro t ⟨ht, hct⟩
    rw [← hct, hl t ht]
  unfold circleClockInv
  rw [dif_pos hu]
  exact SymplecticPacking.Explicit.the_eq hu ⟨hm T hT, hr T hT⟩

/-- **The explicit circle-clock inverse** has every property of the library's
`positiveCircleClock_inverse`. -/
theorem circleClockInv_spec {b : ℝ} (hb : 0 < b) (hsmall : b < 1/2) :
    ContDiffOn ℝ ∞ (circleClockInv b) (Ioo (0:ℝ) 1) ∧
      (∀ T ∈ Ioo (0:ℝ) 1, circleClockInv b T ∈ Ioo (1/2 - b) (1/2 + b)) ∧
      (∀ t ∈ Ioo (1/2 - b) (1/2 + b),
        circleClockInv b (intervalClock (-b) b (t - 1/2)) = t) ∧
      (∀ T ∈ Ioo (0:ℝ) 1, intervalClock (-b) b (circleClockInv b T - 1/2) = T) ∧
      (∀ T ∈ Ioo (0:ℝ) 1, 0 < deriv (circleClockInv b) T ∧
        positiveCircleClock b (circleTurn (circleClockInv b T)) *
          deriv (circleClockInv b) T = 1) := by
  obtain ⟨g, hg, hm, hl, hr, hd⟩ := positiveCircleClock_inverse hb hsmall
  have heq : EqOn (circleClockInv b) g (Ioo (0:ℝ) 1) := fun T hT =>
    circleClockInv_eq hm hl hr hT
  have hderiv : ∀ T ∈ Ioo (0:ℝ) 1, deriv (circleClockInv b) T = deriv g T := by
    intro T hT
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hT] with S hS
    exact heq hS
  have hleft : ∀ t ∈ Ioo (1/2 - b) (1/2 + b),
      circleClockInv b (intervalClock (-b) b (t - 1/2)) = t := by
    intro t ht
    have hu : ∃! s, s ∈ Ioo (1/2 - b) (1/2 + b) ∧
        intervalClock (-b) b (s - 1/2) = intervalClock (-b) b (t - 1/2) := by
      refine ⟨t, ⟨ht, rfl⟩, ?_⟩
      rintro s ⟨hs, hcs⟩
      rw [← hl s hs, hcs, hl t ht]
    unfold circleClockInv
    rw [dif_pos hu]
    exact SymplecticPacking.Explicit.the_eq hu ⟨ht, rfl⟩
  refine ⟨hg.congr heq, fun T hT => (heq hT).symm ▸ hm T hT, ?_, ?_, ?_⟩
  · exact hleft
  · intro T hT
    rw [heq hT, hr T hT]
  · intro T hT
    rw [hderiv T hT, heq hT]
    exact hd T hT

/-- **The normalized positive area** of the library's `exists_normalized_positive_area`, with
the explicit circle-clock inverse. -/
theorem normalizedArea_spec {b : ℝ} (hb : 0 < b) (hsmall : b < 1/2)
    {I : Set ℝ} (hI : IsOpen I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ Ioo (1/2 - b) (1/2 + b)))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ Ioo (1/2 - b) (1/2 + b)))
    (hbase : ∀ q ∈ I ×ˢ Ioo (1/2 - b) (1/2 + b), 0 < fderiv ℝ B q (1,0) - fderiv ℝ A q (0,1)) :
    ContDiffOn ℝ ∞ (circleClockInv b) (Ioo (0:ℝ) 1) ∧
      MapsTo (circleClockInv b) (Ioo (0:ℝ) 1) (Ioo (1/2 - b) (1/2 + b)) ∧
      (∀ t ∈ Ioo (1/2 - b) (1/2 + b), circleClockInv b (intervalClock (-b) b (t - 1/2)) = t) ∧
      (∀ T ∈ Ioo (0:ℝ) 1, intervalClock (-b) b (circleClockInv b T - 1/2) = T) ∧
      (∀ T ∈ Ioo (0:ℝ) 1, positiveCircleClock b (circleTurn (circleClockInv b T)) *
        deriv (circleClockInv b) T = 1) ∧
      ContDiffOn ℝ ∞ (normalizedAreaDensity A B (circleClockInv b)) (I ×ˢ Ioo (0:ℝ) 1) ∧
      (∀ q ∈ I ×ˢ Ioo (0:ℝ) 1, 0 < normalizedAreaDensity A B (circleClockInv b) q) := by
  obtain ⟨hg, hm, hl, hr, hd⟩ := circleClockInv_spec hb hsmall
  refine ⟨hg, fun _ h => hm _ h, hl, hr, fun T hT => (hd T hT).2,
    normalizedAreaDensity_smooth hI isOpen_Ioo hA hB hg (fun _ h => hm _ h), ?_⟩
  intro q hq
  exact normalizedAreaDensity_pos (fun _ h => hm _ h) (fun T hT => (hd T hT).1) hbase hq

/-! ### (2) The explicit inverse of the layer chart -/

section LayerChart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The domain `(a, b) × (0, 1) × μ⁻¹(V)` of the layer chart. -/
def layerDomain (a b : ℝ) (V : Set (ι → ℝ)) : Set (Plane × PlanePhase ι) :=
  (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)

open Classical in
/-- The explicit inverse of the layer chart: the unique preimage in `layerDomain a b V`
(and the point itself if there is none). -/
def layerChartInv (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ) (a b : ℝ)
    (V : Set (ι → ℝ)) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  if h : ∃! x, x ∈ layerDomain a b V ∧ layerChart F f x = p then
    SymplecticPacking.Explicit.the h
  else p

/-- The local version needed for the area layer coordinate: smoothness is required only
on the strip, since the angular inverse need not extend smoothly across its endpoints. -/
theorem layerChartInv_local_spec {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v)) :
    let W := layerChart F f '' layerDomain a b V
    let g := layerChartInv F f a b V
    IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → planeMoments p.2 ∈ V →
        0 < p.1.1 → p.1.1 < H (planeMoments p.2) → p ∈ W) ∧
      (∀ p ∈ layerDomain a b V, g (layerChart F f p) = p) ∧
      (∀ p ∈ W, g p ∈ layerDomain a b V ∧ layerChart F f (g p) = p) := by
  obtain ⟨W, g, hWo, hgs, hWe, hav, hl, hr⟩ :=
    layerChart_inverse_local hF hV hab hf H hderiv hlo hhi
  have hWe' : W = layerChart F f '' layerDomain a b V := hWe
  have heq : EqOn (layerChartInv F f a b V) g W := by
    intro p hp
    have hu : ∃! x, x ∈ layerDomain a b V ∧ layerChart F f x = p := by
      refine ⟨g p, hr p hp, ?_⟩
      rintro x ⟨hx, hxp⟩
      rw [← hxp, hl x hx]
    unfold layerChartInv
    rw [dif_pos hu]
    exact SymplecticPacking.Explicit.the_eq hu (hr p hp)
  rw [← hWe']
  refine ⟨hWo, hgs.congr heq, hav, ?_, ?_⟩
  · intro p hp
    have hpW : layerChart F f p ∈ W := hWe' ▸ mem_image_of_mem _ hp
    rw [heq hpW, hl p hp]
  · intro p hp
    rw [heq hp]
    exact hr p hp

end LayerChart

end ToricPackingStages

end SymplecticPacking.HighDim
