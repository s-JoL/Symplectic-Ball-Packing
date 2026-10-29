import SymplecticPacking.HighDim.Handle.AngularPackingFormula
import SymplecticPacking.HighDim.Handle.HandleMap
import SymplecticPacking.HighDim.Handle.BackgroundSpec

/-!
# Packing formula for the explicit layer maps

Packing by the finite family of inverse-chart and angular formulas.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport (Ambient closedBall standardForm)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Topology BigOperators Manifold

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [T2Space M]

/-- The normalized planar layer maps, before the common annular unshearing. -/
def weightedLayerMap {m q k : ℕ} (T : ToricModel M m q) (K H : (Fin m → ℝ) → ℝ)
    (γ : ManifoldOneForm Plane M) (a r : Fin k → ℝ) (i : Fin k) :=
  angularReparam (circleClockInv T.hδ) ∘ layerBallMap T K H γ a r i

theorem weightedLayerMap_spec {m q k : ℕ} (T : ToricModel M m q) (hT : T.Spec)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    {K H : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {γ : ManifoldOneForm Plane M} {ε : ℝ} (hε : 0 < ε)
    (hγ : ∀ x ∈ T.handle.chart.target, ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ, Plane) x x))
    (hdγ : ∀ x ∈ T.handle.chart.target, manifoldExteriorOneForm γ x = ε • T.Λ x)
    {a r : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i < a i)
    (hsimplex : ∀ i p, (∀ j, 0 ≤ p j) → ∑ j, p j ≤ r i → p ∈ layerMomentDomain T) :
    let G := surfaceFinalLayer ((K-H) ∘ planeMoments)
      (fun i => smoothCap a r i ∘ planeMoments)
      (surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
        (fun i => smoothCap a r i ∘ planeMoments) (Φ.map 1).symm)
      (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
      (layerClock (k+1) (-T.hb) T.hb (Fin.last k));
    ∃ U : Fin k → Set (Ambient (m+1)),
      (∀ i, IsOpen (U i)) ∧ (∀ i, closedBall (m+1) (r i) ⊆ U i) ∧
      (∀ i, ContDiffOn ℝ ∞ (weightedLayerMap T K H γ a r i) (U i)) ∧
      (∀ i, Topology.IsEmbedding (fun z : U i => weightedLayerMap T K H γ a r i z)) ∧
      (∀ i z, z ∈ U i → weightedLayerMap T K H γ a r i z ∈
        (Ioo (ballLayerLo T i) (ballLayerHi T i) ×ˢ Ioo (1/2-T.hδ) (1/2+T.hδ)) ×ˢ
          (planeMoments ⁻¹' layerMomentDomain T)) ∧
      (∀ i z, z ∈ U i → ∀ v w,
        horizontalCoupling phaseArea (baseCoefficient (T.handle.annularCoverA γ))
          (weightedSecondCoefficient (T.handle.annularCoverB γ)
            (fun z => positiveCircleClock T.hδ (circleTurn z.2)) G)
          (weightedLayerMap T K H γ a r i z)
          (fderiv ℝ (weightedLayerMap T K H γ a r i) z v)
          (fderiv ℝ (weightedLayerMap T K H γ a r i) z w) = standardForm v w) ∧
      Pairwise (fun i j => Disjoint
        (weightedLayerMap T K H γ a r i '' closedBall (m+1) (r i))
        (weightedLayerMap T K H γ a r j '' closedBall (m+1) (r j))) := by
  let G := surfaceFinalLayer ((K-H) ∘ planeMoments)
    (fun i => smoothCap a r i ∘ planeMoments)
    (surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
      (fun i => smoothCap a r i ∘ planeMoments) (Φ.map 1).symm)
    (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
    (layerClock (k+1) (-T.hb) T.hb (Fin.last k))
  have hab : -T.hb < T.hb := by linarith [hT.hb_pos]
  obtain ⟨hbd, hord, hsm, _, _⟩ := layerClocks_spec (k+1) hab
  have hgeo := T.handle.annularPackingGeometry hT.hb_lt hT.hδ_lt hT.handle_orient
    hT.Λ_smooth hT.Λ_skew hT.Λ_pos hε hγ hdγ
  obtain ⟨hg, hm, _, hinv, hnorm, hℓ, hpos⟩ :=
    normalizedArea_spec hT.hδ_pos hT.hδ_lt isOpen_Ioo hgeo.1 hgeo.2.1 hgeo.2.2
  have hls : ContDiffOn ℝ ∞ (layerDensity T γ) (Ioo (-T.hb) T.hb ×ˢ Ioo (0:ℝ) 1) := hℓ
  choose U hU hBU hs he him hf using fun i => layerBallMap_spec T hT hK hH γ hls hpos hr hra hsimplex i
  have hdis : Pairwise (fun i j => Disjoint (layerBallMap T K H γ a r i '' closedBall (m+1) (r i))
      (layerBallMap T K H γ a r j '' closedBall (m+1) (r j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hi := (him i x (hBU i hx)).1.1
    have hj := (him j y (hBU j hy)).1.1
    rw [heq] at hj
    rcases lt_or_gt_of_ne hij with h | h
    · have hh := hord i.castSucc j.castSucc (by simpa using h)
      change layerHi _ _ _ _ < layerLo _ _ _ _ at hh
      dsimp [ballLayerLo, ballLayerHi] at hi hj
      linarith [hi.2, hj.1]
    · have hh := hord j.castSucc i.castSucc (by simpa using h)
      dsimp [ballLayerLo, ballLayerHi] at hi hj
      linarith [hi.1, hj.2]
  have hF (i : Fin k) : ContDiff ℝ ∞ (layerBelow K H a r i) :=
    (hK.sub hH).add (ContDiff.sum fun j _ => smoothCap_smooth a r j)
  have hG : ContDiff ℝ ∞ G := surfaceFinalLayer_smooth
    ((hK.sub hH).comp planeMoments_smooth)
    (surfaceRemainder_smooth (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      (fun i => (smoothCap_smooth a r i).comp planeMoments_smooth) (Φ.map_inverse_smooth 1))
    (fun i => (smoothCap_smooth a r i).comp planeMoments_smooth)
    (fun i => (hsm i.castSucc).1) (hsm _).1
  have hform : ∀ i z, z ∈ U i → ∀ v w,
      areaHamiltonianForm (layerDensity T γ) G (layerBallMap T K H γ a r i z)
        (fderiv ℝ (layerBallMap T K H γ a r i) z v)
        (fderiv ℝ (layerBallMap T K H γ a r i) z w) = standardForm v w := by
    intro i z hz v w
    have heq : ∀ s ∈ Ioo (ballLayerLo T i) (ballLayerHi T i), ∀ v,
        planeMoments v ∈ layerMomentDomain T →
        G (s,v) = layerHamiltonian (layerBelow K H a r i) (smoothCap a r i)
          (layerClock (k+1) (-T.hb) T.hb i.castSucc) (s,v) := by
      intro s hs v _
      exact layerClocks_final k hab _ _ _ i ⟨hs.1.le, hs.2.le⟩ v
    rw [areaHamiltonianForm_layer isOpen_Ioo (convex_Ioo _ _)
      (show ballLayerLo T i ∈ Ioo (-T.hb) T.hb from ⟨(hbd _).1, (hbd _).2.1.trans (hbd _).2.2⟩)
      (show ballLayerHi T i ∈ Ioo (-T.hb) T.hb from ⟨(hbd _).1.trans (hbd _).2.1, (hbd _).2.2⟩)
      (hbd i.castSucc).2.1 hls (hF i) (smoothCap_smooth a r i) (hsm i.castSucc).1
      (layerMomentDomain_open T) heq (him i z hz)]
    exact hf i z hz v w
  have hw : ContDiff ℝ ∞ (fun t => positiveCircleClock T.hδ (circleTurn t)) :=
    ((positiveCircleClock_smooth hT.hδ_pos hT.hδ_lt).comp circleTurn_smooth).contDiff
  have hC : Continuous (fun t => intervalClock (-T.hδ) T.hδ (t-1/2)) :=
    (intervalClock_smooth _ _).continuous.comp (continuous_id.sub continuous_const)
  have hasub (i : Fin k) : Ioo (ballLayerLo T i) (ballLayerHi T i) ⊆ Ioo (-T.hb) T.hb :=
    fun _ hs => ⟨(hbd _).1.trans hs.1, hs.2.trans (hbd _).2.2⟩
  have hout := angular_packing_transport_formula isOpen_Ioo isOpen_Ioo hgeo.1 hgeo.2.1 hw hg hm hC
    hinv hnorm hG (ballLayerLo T) (ballLayerHi T) r hasub U (layerBallMap T K H γ a r)
    hU hBU hs he him hform hdis
  exact ⟨U, hU, hBU, hout⟩

/-- The defined layer maps satisfy the packing specification once the normalized primitive
has the stated local background form. All maps in this conclusion are the formulas. -/
theorem layerMapsOf_spec_of_background {m q k : ℕ} (T : ToricModel M m q) (hT : T.Spec)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    {K H : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Γ : (Fin m → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {ε : ℝ} (hε : 0 < ε)
    (hγ : ∀ x ∈ T.handle.chart.target, ContDiffAt ℝ ∞
      (chartOneForm (handleBackground T Γ H) x) (extChartAt 𝓘(ℝ, Plane) x x))
    (hdγ : ∀ x ∈ T.handle.chart.target,
      manifoldExteriorOneForm (handleBackground T Γ H) x = ε • T.Λ x)
    {W : Set M} (hW : IsOpen W) (hBW : T.handle.chart '' band T.hb ⊆ W)
    (hN : ∀ p x, x ∈ W → Γ p x = handleBackground T Γ H x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x)
    (hΦ : ∀ t ∈ Icc (0:ℝ) 1,
      MapsTo (Φ.map t) (planeMoments ⁻¹' T.Δ.set) (planeMoments ⁻¹' T.Δ.set) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' T.Δ.set) (planeMoments ⁻¹' T.Δ.set))
    {a r : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i < a i)
    (hsimplex : ∀ i p, (∀ j, 0 ≤ p j) → ∑ j, p j ≤ r i → p ∈ layerMomentDomain T) :
    (∀ i, FormNeighborhoodEmbedding (closedBall (m+1) (r i))
      (fun _ => successorStandardForm m) (layerFormOf T Φ K H Γ a r) (layerMapsOf T Φ K H Γ a r i)) ∧
    (∀ i, MapsTo (layerMapsOf T Φ K H Γ a r i) (closedBall (m+1) (r i)) (interior T.region)) ∧
    Pairwise (fun i j => Disjoint
      (layerMapsOf T Φ K H Γ a r i '' closedBall (m+1) (r i))
      (layerMapsOf T Φ K H Γ a r j '' closedBall (m+1) (r j))) := by
  let γ := handleBackground T Γ H
  let G := surfaceFinalLayer ((K-H) ∘ planeMoments)
    (fun i => smoothCap a r i ∘ planeMoments)
    (surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
      (fun i => smoothCap a r i ∘ planeMoments) (Φ.map 1).symm)
    (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
    (layerClock (k+1) (-T.hb) T.hb (Fin.last k))
  let φ := weightedLayerMap T K H γ a r
  obtain ⟨U, hU, hBU, hφ, hemb, him, hform, hdis⟩ :=
    weightedLayerMap_spec T hT Φ hK hH hε hγ hdγ hr hra hsimplex
  have hab : -T.hb < T.hb := by linarith [hT.hb_pos]
  obtain ⟨hbd, _, hsm, _, _⟩ := layerClocks_spec (k+1) hab
  have hgeo := T.handle.annularPackingGeometry hT.hb_lt hT.hδ_lt hT.handle_orient
    hT.Λ_smooth hT.Λ_skew hT.Λ_pos hε hγ hdγ
  let S : Set Plane := Ioo (-T.hb) T.hb ×ˢ Ioo (1/2-T.hδ) (1/2+T.hδ)
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have hsub := T.handle.handleAnnularCover_rectangle_domain
    (annularPackingRectangle_subset hT.hb_lt hT.hδ_lt)
  have himS : ∀ i z, z ∈ U i → φ i z ∈ S ×ˢ (planeMoments ⁻¹' layerMomentDomain T) := by
    intro i z hz
    have hp := him i z hz
    exact ⟨⟨⟨(hbd _).1.trans hp.1.1.1, hp.1.1.2.trans (hbd _).2.2⟩, hp.1.2⟩, hp.2⟩
  have hlo : ∀ s, s ≤ -T.hb → ∀ i, layerClock (k+1) (-T.hb) T.hb i s = 0 :=
    fun s hs i => layerClock_lo hT.hb_pos i hs
  have hhi : ∀ s, T.hb ≤ s → ∀ i, layerClock (k+1) (-T.hb) T.hb i s = 1 :=
    fun s hs i => layerClock_hi hT.hb_pos i hs
  have hΓf : SmoothOneFormFamily (fun v => T.handle.globalSurfaceSecondPrimitive T.hb Φ
      (K ∘ planeMoments) (H ∘ planeMoments)
      (fun i => smoothCap a r i ∘ planeMoments)
      (fun i => layerClock (k+1) (-T.hb) T.hb i.castSucc)
      (layerClock (k+1) (-T.hb) T.hb (Fin.last k)) (Γ ∘ planeMoments) (1,v)) :=
    (globalSurfaceSecondPrimitive_smooth T.handle hT.hb_pos hT.hb_lt Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      (fun i => (smoothCap_smooth a r i).comp planeMoments_smooth)
      (fun i => (hsm i.castSucc).1) (hsm _).1
      (fun s hs => ⟨fun i => hlo s hs i.castSucc, hlo s hs _⟩)
      (fun s hs => ⟨fun i => hhi s hs i.castSucc, hhi s hs _⟩)
      (hΓ.comp planeMoments_smooth)).comp (contDiff_const.prodMk contDiff_id)
  let Ω₀ := horizontalCoupling phaseArea (baseCoefficient (T.handle.annularCoverA γ))
    (weightedSecondCoefficient (T.handle.annularCoverB γ)
      (fun z => positiveCircleClock T.hδ (circleTurn z.2)) G)
  have hφform : ∀ i, FormNeighborhoodEmbedding (closedBall (m+1) (r i))
      (fun _ => successorStandardForm m) Ω₀ (φ i) := by
    intro i
    refine ⟨U i, hU i, hBU i, (hφ i).contMDiffOn, hemb i, ?_⟩
    intro z hz v w
    rw [mfderiv_eq_fderiv]
    change Ω₀ (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z w) = successorStandardForm m v w
    erw [successorStandardForm_apply]
    exact hform i z hz v w
  have hgform : ∀ p ∈ S ×ˢ (univ : Set (PlanePhase (Fin m))), ∀ v w,
      layerFormOf T Φ K H Γ a r (T.handle.annularUnshearMap T.hb Φ p)
        (mfderiv 𝓘(ℝ, Plane × PlanePhase (Fin m)) 𝓘(ℝ, Plane × PlanePhase (Fin m))
          (T.handle.annularUnshearMap T.hb Φ) p v)
        (mfderiv 𝓘(ℝ, Plane × PlanePhase (Fin m)) 𝓘(ℝ, Plane × PlanePhase (Fin m))
          (T.handle.annularUnshearMap T.hb Φ) p w) = Ω₀ p v w := by
    intro p hp v w
    have Hpull := annularUnshearMap_pullback T.handle T.hb phaseArea_isInvertible phaseArea_skew Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      (fun i => (smoothCap_smooth a r i).comp planeMoments_smooth)
      (fun i => (hsm i.castSucc).1) (hsm _).1 (Γ ∘ planeMoments) γ hW
      (fun v x hx => hN (planeMoments v) x hx) hΓf hS hgeo.1 hgeo.2.1
      (hsub hp.1) hp.1
      (hBW (T.handle.handleAnnularCover_mem_band T.hb ⟨hp.1.1.1.le, hp.1.1.2.le⟩)) v w
    dsimp only [Ω₀, G]
    rw [← hT.clock]
    exact Hpull
  obtain ⟨hemb', hdis'⟩ := postcompose_form_packing (fun i => closedBall (m+1) (r i))
    (fun _ => successorStandardForm m) Ω₀ (layerFormOf T Φ K H Γ a r)
    (hS.prod isOpen_univ) (T.handle.annularUnshearMap T.hb Φ)
    (T.handle.annularUnshearMap_smoothOn T.hb Φ hsub)
    (T.handle.annularUnshearMap_isEmbedding T.hb Φ
      (annularPackingRectangle_subset hT.hb_lt hT.hδ_lt)) hgform
    φ hφform (fun i z hz => ⟨(himS i z (hBU i hz)).1, mem_univ _⟩) hdis
  refine ⟨hemb', ?_, hdis'⟩
  intro i z hz
  have hp := himS i z (hBU i hz)
  apply T.handle.annularUnshearMap_mem_interior T.hb Φ
    ((T.handle.image_band_subset_target hT.hb_lt).trans (subset_closure.trans hT.handle_in_base))
    hΦ ⟨hp.1.1.1.le, hp.1.1.2.le⟩
  exact interior_mono (preimage_mono (layerMomentDomain_subset T))
    ((layerMomentDomain_open T).interior_eq.symm ▸ hp.2)

/-- Geometric input form of the layer-map theorem: curvature and annular normal
form suffice, with the background itself read by a fixed formula. -/
theorem layerMapsOf_spec_of_normal_form {m q k : ℕ} (T : ToricModel M m q) (hT : T.Spec)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    {K H : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Γ : (Fin m → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {ε : ℝ} (hε : 0 < ε)
    (hdΓ : ∀ x ∈ T.handle.chart.target,
      manifoldExteriorOneForm (Γ 0) x = ε • T.Λ x + H 0 • T.handle.density T.hb x)
    {γ : ManifoldOneForm Plane M} {W : Set M} (hW : IsOpen W)
    (hBW : T.handle.chart '' band T.hb ⊆ W) (hWA : W ⊆ T.handle.chart.target)
    (hN : ∀ p x, x ∈ W → Γ p x = γ x +
      (intervalClock (-T.hb) T.hb (T.handle.chart.symm x).1 * H p) • T.handle.dual x)
    (hΦ : ∀ t ∈ Icc (0:ℝ) 1,
      MapsTo (Φ.map t) (planeMoments ⁻¹' T.Δ.set) (planeMoments ⁻¹' T.Δ.set) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' T.Δ.set) (planeMoments ⁻¹' T.Δ.set))
    {a r : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i < a i)
    (hsimplex : ∀ i p, (∀ j, 0 ≤ p j) → ∑ j, p j ≤ r i → p ∈ layerMomentDomain T) :
    (∀ i, FormNeighborhoodEmbedding (closedBall (m+1) (r i))
      (fun _ => successorStandardForm m) (layerFormOf T Φ K H Γ a r) (layerMapsOf T Φ K H Γ a r i)) ∧
    (∀ i, MapsTo (layerMapsOf T Φ K H Γ a r i) (closedBall (m+1) (r i)) (interior T.region)) ∧
    Pairwise (fun i j => Disjoint
      (layerMapsOf T Φ K H Γ a r i '' closedBall (m+1) (r i))
      (layerMapsOf T Φ K H Γ a r j '' closedBall (m+1) (r j))) := by
  have hbg := handleBackground_spec T hΓ H hdΓ
  exact layerMapsOf_spec_of_background T hT Φ hK hH hΓ hε hbg.1 hbg.2 hW hBW
    (handleBackground_normal T Γ H hWA hN) hΦ hr hra hsimplex

end SymplecticPacking.HighDim.ToricPackingStages
