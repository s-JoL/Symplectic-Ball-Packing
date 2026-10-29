import SymplecticPacking.HighDim.Handle.ThinPlanarSpec

/-!
# Explicit ball embeddings into a layer

The inverse-chart and strip formula embeds a closed ball in a layer.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function Manifold
open OAI.PackingSufficiencySupport (Ambient closedBall standardForm)
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- This proves the formula itself, with a fixed strip map and unique inverse, rather than
choosing a ball embedding from an existence theorem. -/
theorem explicit_split_ball_in_layer {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v))
    {r r' : ℝ} (hr' : 0 ≤ r') (hrr : r' < r)
    (hsimplex : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) ≤ r' → p ∈ V)
    (hheight : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → p ∈ V → r-∑ i, p i ≤ H p) :
    let φ := layerChartInv F f a b V ∘ thinProduct ((r-r')/2)
    ∃ N : Set (Plane × PlanePhase ι), IsOpen N ∧ splitCapacityBall r' ⊆ N ∧
      ContDiffOn ℝ ∞ φ N ∧ Topology.IsEmbedding (fun z : N => φ z) ∧
      (∀ z ∈ N, φ z ∈ layerDomain a b V) ∧
      (∀ z ∈ N, ∀ v w, layerForm F f (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w) =
        productForm phaseArea v w) := by
  let U := layerDomain a b V
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).prod hV
  have hfU : ContDiffOn ℝ ∞ f U := hf.mono
    (prod_mono (prod_mono Ioo_subset_Icc_self Subset.rfl) Subset.rfl)
  have hchart : ContDiffOn ℝ ∞ (layerChart F f) U :=
    (toricSuspension_smooth hF).contDiffOn.comp
      ((hfU.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn)
      (fun _ _ => mem_univ _)
  let W := layerChart F f '' U
  let g := layerChartInv F f a b V
  obtain ⟨hW, hg, ha, hl, hr⟩ := layerChartInv_local_spec hF hV hab hf H hderiv hlo hhi
  let δ := (r-r')/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let Q := thinProduct (ι := ι) δ
  have hQ : ContDiff ℝ ∞ Q := thinProduct_smooth hδ
  let N := Q ⁻¹' W
  have hN : IsOpen N := hW.preimage hQ.continuous
  have hball : splitCapacityBall r' ⊆ N := by
    intro z hz
    have hz' : radialArea z.1 + ∑ i, planeMoments z.2 i ≤ r' := hz
    have hps : (∑ i, planeMoments z.2 i) ≤ r' := by linarith [radialArea_nonneg z.1]
    have hpV := hsimplex (planeMoments z.2) (planeMoments_nonneg z.2) hps
    have hqb := thinPlanar_bound hδ z.1
    apply ha (Q z) hqb.2.2 hpV hqb.1
    change (thinPlanar δ z.1).1 < H (planeMoments z.2)
    have hh := hheight (planeMoments z.2) (planeMoments_nonneg z.2) hpV
    dsimp [δ] at hqb
    linarith [hqb.2.1]
  have hsφ : ContDiffOn ℝ ∞ (g ∘ Q) N := hg.comp hQ.contDiffOn (fun _ hz => hz)
  have hge : Topology.IsEmbedding (fun y : W => g y) :=
    inverse_chart_isEmbedding hchart.continuousOn hg.continuousOn rfl hl hr
  let j : N → W := fun z => ⟨Q z,z.property⟩
  have hje : Topology.IsEmbedding j :=
    ((thinProduct_isEmbedding hδ).comp Topology.IsEmbedding.subtypeVal).codRestrict W
      (fun z => z.property)
  refine ⟨N, hN, hball, hsφ, hge.comp hje, ?_, ?_⟩
  · intro z hz
    exact (hr (Q z) hz).1
  · intro z hz v w
    exact inverse_chart_composition_pullback hU hW hchart hg hr
      (layerForm F f) (productForm phaseArea)
      (fun x hx u t => layerChart_pullback_at hF x (hfU.contDiffAt (hU.mem_nhds hx)) u t)
      hQ (thinProduct_symplectic hδ) hz v w

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]

/-- The defined ball map has the required neighbourhood embedding and layer image. -/
theorem layerBallMap_spec {m q k : ℕ} (T : ToricModel M m q) (hT : T.Spec)
    {K H : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (γ : ManifoldOneForm Plane M)
    (hℓ : ContDiffOn ℝ ∞ (layerDensity T γ) (Ioo (-T.hb) T.hb ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ z ∈ Ioo (-T.hb) T.hb ×ˢ Ioo (0:ℝ) 1, 0 < layerDensity T γ z)
    {a r : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i < a i)
    (hsimplex : ∀ i p, (∀ j, 0 ≤ p j) → ∑ j, p j ≤ r i → p ∈ layerMomentDomain T)
    (i : Fin k) :
    ∃ N : Set (Ambient (m+1)), IsOpen N ∧ closedBall (m+1) (r i) ⊆ N ∧
      ContDiffOn ℝ ∞ (layerBallMap T K H γ a r i) N ∧
      Topology.IsEmbedding (fun z : N => layerBallMap T K H γ a r i z) ∧
      (∀ z ∈ N, layerBallMap T K H γ a r i z ∈
        layerDomain (ballLayerLo T i) (ballLayerHi T i) (layerMomentDomain T)) ∧
      (∀ z ∈ N, ∀ v w,
        OAI.PackingSufficiencySupport.Hamiltonian.layerForm (layerBelow K H a r i)
          (layerCoord T γ a r i) (layerBallMap T K H γ a r i z)
          (fderiv ℝ (layerBallMap T K H γ a r i) z v)
          (fderiv ℝ (layerBallMap T K H γ a r i) z w) = standardForm v w) := by
  have hab : -T.hb < T.hb := by linarith [hT.hb_pos]
  obtain ⟨hbd, _, hsm, hnon, hcoll⟩ := layerClocks_spec (k+1) hab
  have hρa : layerClock (k+1) (-T.hb) T.hb i.castSucc (ballLayerLo T i) = 0 := by
    obtain ⟨ε, hε, hlo, _⟩ := hcoll i.castSucc
    exact hlo _ (by dsimp [ballLayerLo]; linarith)
  have hρb : layerClock (k+1) (-T.hb) T.hb i.castSucc (ballLayerHi T i) = 1 := by
    obtain ⟨ε, hε, _, hhi⟩ := hcoll i.castSucc
    exact hhi _ (by dsimp [ballLayerHi]; linarith)
  have hd := areaLayerCoordinate_data isOpen_Ioo (convex_Ioo _ _)
    (show ballLayerLo T i ∈ Ioo (-T.hb) T.hb from
      ⟨(hbd _).1, ((hbd _).2.1.trans (hbd _).2.2)⟩)
    (show ballLayerHi T i ∈ Ioo (-T.hb) T.hb from
      ⟨((hbd _).1.trans (hbd _).2.1), (hbd _).2.2⟩)
    (hbd i.castSucc).2.1 hℓ hpos (hsm i.castSucc).1 (fun s => (hnon _ s).2.2)
    hρa hρb (smoothCap_smooth a r i)
    (V := layerMomentDomain T) (fun p _ => smoothCap_nonneg (hra i) p)
  have hF : ContDiff ℝ ∞ (layerBelow K H a r i) :=
    (hK.sub hH).add (ContDiff.sum fun j _ => smoothCap_smooth a r j)
  obtain ⟨N, hN, hbN, hsN, heN, himN, hfN⟩ := explicit_split_ball_in_layer hF
    (layerMomentDomain_open T) (hbd i.castSucc).2.1 hd.1 (smoothCap a r i)
    hd.2.1 hd.2.2.1 hd.2.2.2 (hr i)
    (show r i < (a i+r i)/2 by linarith [hra i]) (hsimplex i)
    (fun p _ _ => smoothCap_ge (hra i) p)
  have hmargin : (((a i+r i)/2-r i)/2) = (a i-r i)/4 := by ring
  rw [hmargin] at hsN heN himN hfN
  obtain ⟨U, hU, hbU, hsU, heU, himU, hfU⟩ :=
    complex_ball_of_split_embedding hN hbN hsN heN hfN
  refine ⟨U, hU, hbU, hsU, heU, ?_, hfU⟩
  intro z hz
  obtain ⟨y, hy, heq⟩ := himU z hz
  change (layerChartInv (layerBelow K H a r i) (layerCoord T γ a r i)
      (ballLayerLo T i) (ballLayerHi T i) (layerMomentDomain T) ∘
      thinProduct ((a i-r i)/4)) y =
    (layerChartInv (layerBelow K H a r i) (layerCoord T γ a r i)
      (ballLayerLo T i) (ballLayerHi T i) (layerMomentDomain T) ∘
      thinProduct ((a i-r i)/4)) (complexSplitPhase m z) at heq
  change (layerChartInv (layerBelow K H a r i) (layerCoord T γ a r i)
    (ballLayerLo T i) (ballLayerHi T i) (layerMomentDomain T) ∘
    thinProduct ((a i-r i)/4)) (complexSplitPhase m z) ∈ _
  rw [← heq]
  exact himN y hy

end SymplecticPacking.HighDim.ToricPackingStages
