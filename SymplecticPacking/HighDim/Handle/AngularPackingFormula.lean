import SymplecticPacking.HighDim.Handle.ExplicitBallLayerSpec

/-!
# Angular transport of the layer packing formula

Angular transport for the displayed reparametrization formula.

Coordinate-integral proof adapted from `vendor/OAI/Geometry/BallPacking/Layers/LayerAreaForm.lean`.
Original source: OpenAI, Apache-2.0; see vendor/LICENSE and vendor/NOTICE.
The formulas here use fixed transition functions in place of existential bump data.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport (Ambient closedBall standardForm)
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators

theorem angular_packing_transport_formula {m : ℕ} {ι : Type*} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ J)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ J))
    {w g C : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1))
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) (hC : Continuous C)
    (hinv : ∀ T∈Ioo (0:ℝ) 1,C (g T)=T)
    (hnorm : ∀ T∈Ioo (0:ℝ) 1,w (g T)*deriv g T=1)
    {G : ℝ × PlanePhase (Fin m) → ℝ} (hG : ContDiff ℝ ∞ G)
    (a b r : ι → ℝ) (ha : ∀ i,Ioo (a i) (b i)⊆I) {V : Set (Fin m → ℝ)}
    (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m))
    (hU : ∀ i,IsOpen (U i)) (hBU : ∀ i,closedBall (m+1) (r i)⊆U i)
    (hφ : ∀ i,ContDiffOn ℝ ∞ (φ i) (U i))
    (hemb : ∀ i,Topology.IsEmbedding (fun z : U i => φ i z))
    (him : ∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V))
    (hform : ∀ i,∀ z∈U i,∀ v u,
      areaHamiltonianForm (normalizedAreaDensity A B g) G (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u)
    (hdis : Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r i))
      (φ j '' closedBall (m+1) (r j)))) :
    let ψ := fun i => angularReparam g ∘ φ i;
      (∀ i,ContDiffOn ℝ ∞ (ψ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => ψ i z)) ∧
      (∀ i,∀ z∈U i,ψ i z∈(Ioo (a i) (b i) ×ˢ J) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v u,
        horizontalCoupling phaseArea (baseCoefficient A) (weightedSecondCoefficient B (fun q => w q.2) G)
          (ψ i z) (fderiv ℝ (ψ i) z v) (fderiv ℝ (ψ i) z u)=standardForm v u) ∧
      Pairwise (fun i j => Disjoint (ψ i '' closedBall (m+1) (r i))
        (ψ j '' closedBall (m+1) (r j))) := by
  let S : Set (Plane × PlanePhase (Fin m)) := (I ×ˢ Ioo (0:ℝ) 1) ×ˢ (Set.univ : Set (PlanePhase (Fin m)))
  have hS : IsOpen S := (hI.prod isOpen_Ioo).prod isOpen_univ
  have hmS : ∀ i,MapsTo (φ i) (U i) S := fun i z hz =>
    ⟨⟨ha i (him i z hz).1.1,(him i z hz).1.2⟩,mem_univ _⟩
  have hgs : ContDiffOn ℝ ∞ (angularReparam g) S := angularReparam_smoothOn hg (fun _ h => h.1.2)
  let ψ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m) := fun i => angularReparam g ∘ φ i
  have hψ : ∀ i,ContDiffOn ℝ ∞ (ψ i) (U i) := fun i => hgs.comp (hφ i) (hmS i)
  have hCs : Continuous (angularReparam (E := PlanePhase (Fin m)) C) :=
    (continuous_fst.fst.prodMk (hC.comp continuous_fst.snd)).prodMk continuous_snd
  refine ⟨hψ,?_,?_,?_,?_⟩
  · intro i
    have he : angularReparam (E := PlanePhase (Fin m)) C ∘ (fun z : U i => ψ i z)=
        (fun z : U i => φ i z) := by
      funext z
      change (((φ i z).1.1,C (g (φ i z).1.2)),(φ i z).2)=φ i z
      rw [hinv _ (him i z z.property).1.2]
    apply Topology.IsEmbedding.of_comp (hψ i).continuousOn.domRestrict hCs
    change Topology.IsEmbedding (angularReparam C ∘ (fun z : U i => ψ i z))
    rw [he]
    exact hemb i
  · intro i z hz
    exact ⟨⟨(him i z hz).1.1,hmap (him i z hz).1.2⟩,(him i z hz).2⟩
  · intro i z hz v u
    have hp := hmS i hz
    have hq : ((φ i z).1.1,g (φ i z).1.2)∈I ×ˢ J := ⟨hp.1.1,hmap hp.1.2⟩
    have hgd := (hg.contDiffAt (isOpen_Ioo.mem_nhds hp.1.2)).differentiableAt (by simp)
    have hψd : fderiv ℝ (ψ i) z=
        (fderiv ℝ (angularReparam g) (φ i z)).comp (fderiv ℝ (φ i) z) :=
      fderiv_comp z ((hgs.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))
        (((hφ i).contDiffAt ((hU i).mem_nhds hz)).differentiableAt (by simp))
    rw [hψd]
    simp only [ContinuousLinearMap.comp_apply]
    dsimp only [ψ,Function.comp_apply]
    rw [angularReparam_weighted_pullback phaseArea
      ((hA.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by simp))
      ((hB.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by simp))
      (hw.differentiable (by simp) _) hgd (hG.differentiable (by simp) _) (hnorm _ hp.1.2)]
    simpa only [areaHamiltonianForm_apply] using hform i z hz v u
  · intro i j hij
    change Disjoint (ψ i '' closedBall (m+1) (r i)) (ψ j '' closedBall (m+1) (r j))
    rw [show ψ i=angularReparam g ∘ φ i from rfl,show ψ j=angularReparam g ∘ φ j from rfl,
      Set.image_comp,Set.image_comp]
    apply (hdis hij).image (angularReparam_injOn hinv (fun _ hp => hp.1.2) (U := S))
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS i (hBU i hz)
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS j (hBU j hz)

end SymplecticPacking.HighDim.ToricPackingStages
