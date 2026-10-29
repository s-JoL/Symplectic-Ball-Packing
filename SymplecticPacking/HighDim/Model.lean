import SymplecticPacking.HighDim.Comparator.Datum
import OAI.Geometry.BallPacking.Models.SurfaceComparison

/-!
# Toric models in product form (paper def:mech-model)

The total space of a toric model of rank `m` over a surface `M` (the base curve with the
marked fibres removed) is `M × ℂ^m` with the form
`Ω = phaseArea + d(Γ(p))` (`globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)`),
`Γ : Δ → Ω¹(M)` a smooth family of horizontal primitives with `dΓ(p) = κ(p) Λ`,
`κ(p, x) > 0`. The compact base domain `base ⊆ M` (smooth boundary) carries the handle
data; `∫_base κ(p) Λ` bounds the base area profile from below.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set Manifold
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff Manifold

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ M] [T2Space M] [_root_.NormalSpace M] [SigmaCompactSpace M]

/-- The sum of the ball-cap profiles on the fibre moment region. -/
def capSum {m k : ℕ} (a : Fin k → ℝ) (p : Moments m) : ℝ :=
  ∑ i,max (a i-∑ j,p j) 0

/-- Data of a toric model of rank `m` with polytope of `q` faces over the surface `M`, with
handle data. -/
structure ToricModel (M : Type) [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M] (m q : ℕ) where
  Δ : Polytope m q
  base : Set M
  Λ : ManifoldTwoForm (ℝ × ℝ) M
  dens : Moments m × M → ℝ
  Γ : Moments m → ManifoldOneForm (ℝ × ℝ) M
  handle : AnnularHandleData (ℝ × ℝ) M
  hb : ℝ
  hδ : ℝ

namespace ToricModel

variable {m q : ℕ} (T : ToricModel M m q)

/-- The model form on `M × ℂ^m`. -/
def form : ManifoldTwoForm ((ℝ × ℝ) × Fibre m) (M × Fibre m) :=
  globalHorizontalCoupling phaseArea (T.Γ ∘ planeMoments)

/-- The region `V_Δ` over the base domain. -/
def region : Set (M × Fibre m) := T.base ×ˢ planeRegion T.Δ.b T.Δ.ℓ

/-- Standing hypotheses on a toric model (those of the OpenAI library's surface packing at a
fixed base domain). -/
structure Spec : Prop where
  Δ_spec : T.Δ.Spec
  base_compact : IsCompact T.base
  base_conn : IsPreconnected (interior T.base)
  base_ne : (interior T.base).Nonempty
  base_boundary : HasSmoothSurfaceBoundary T.base
  orient : PositivePlaneTransitions M
  hb_pos : 0 < T.hb
  hb_lt : T.hb < T.handle.width
  hδ_pos : 0 < T.hδ
  hδ_lt : T.hδ < 1 / 2
  handle_in_base : closure T.handle.chart.target ⊆ interior T.base
  dual_in_base : tsupport T.handle.dual ⊆ interior T.base
  handle_orient : PositivePartialChart T.handle.densityChart
  clock : T.handle.clock = positiveCircleClock T.hδ
  Λ_smooth : SmoothTwoForm T.Λ
  Λ_skew : ∀ x u v, T.Λ x u v = -T.Λ x v u
  Λ_pos : ∀ c y, y ∈ (extChartAt 𝓘(ℝ, ℝ × ℝ) c).target →
    0 < chartTwoForm T.Λ c y (1, 0) (0, 1)
  dens_smooth : ContMDiff (𝓘(ℝ, Moments m).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞ T.dens
  dens_pos : ∀ p ∈ T.Δ.set, ∀ x ∈ T.base, 0 < T.dens (p, x)
  Γ_smooth : SmoothOneFormFamily T.Γ
  dΓ : ∀ p x, manifoldExteriorOneForm (T.Γ p) x = T.dens (p, x) • T.Λ x

/-- The base area `∫_base κ(p) Λ`. -/
def baseArea (hT : T.Spec) (p : Moments m) : ℝ :=
  compactSurfaceFormIntegral hT.base_compact (fun x => T.dens (p, x) • T.Λ x)

end ToricModel

end SymplecticPacking.HighDim
