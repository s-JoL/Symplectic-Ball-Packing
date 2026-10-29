import SymplecticPacking.HighDim.Handle.RawLayerMaps

/-!
# Locality of the native layer inversion

Layer inversion depends only on the displayed coordinates inside its source domain.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter Topology
open scoped Topology
open OAI.PackingSufficiencySupport.Hamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem layerChartInv_congr_domain {F : (ι → ℝ) → ℝ}
    {f g : Plane × PlanePhase ι → ℝ} {a b : ℝ} {V : Set (ι → ℝ)}
    (hfg : EqOn f g (layerDomain a b V)) :
    layerChartInv F f a b V=layerChartInv F g a b V := by
  classical
  have hc : EqOn (layerChart F f) (layerChart F g) (layerDomain a b V) := by
    intro x hx
    simp only [layerChart,Function.comp_apply,stripChart,hfg hx]
  have hp (p : Plane × PlanePhase ι) (x : Plane × PlanePhase ι) :
      (x ∈ layerDomain a b V ∧ layerChart F f x=p) ↔
      (x ∈ layerDomain a b V ∧ layerChart F g x=p) := by
    constructor
    · rintro ⟨hx,he⟩
      exact ⟨hx,(hc hx).symm.trans he⟩
    · rintro ⟨hx,he⟩
      exact ⟨hx,(hc hx).trans he⟩
  funext p
  have he : (fun x => x ∈ layerDomain a b V ∧ layerChart F f x=p)=
      (fun x => x ∈ layerDomain a b V ∧ layerChart F g x=p) :=
    funext fun x => propext (hp p x)
  unfold layerChartInv
  simp only [he]


/-- Only the coefficient germs inside the annular strip enter the density. -/
theorem normalizedAreaDensity_congr_on {I J T : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) {A A' B B' : Plane → ℝ} {g : ℝ → ℝ}
    (hA : EqOn A A' (I ×ˢ J)) (hB : EqOn B B' (I ×ˢ J)) (hg : MapsTo g T J) :
    EqOn (normalizedAreaDensity A B g) (normalizedAreaDensity A' B' g) (I ×ˢ T) := by
  intro q hq
  have hp : (q.1,g q.2)∈I ×ˢ J := ⟨hq.1,hg hq.2⟩
  have ha : A =ᶠ[nhds (q.1,g q.2)] A' := by
    filter_upwards [(hI.prod hJ).mem_nhds hp] with y hy
    exact hA hy
  have hb : B =ᶠ[nhds (q.1,g q.2)] B' := by
    filter_upwards [(hI.prod hJ).mem_nhds hp] with y hy
    exact hB hy
  simp only [normalizedAreaDensity,ha.fderiv_eq,hb.fderiv_eq]

/-- The area integral uses no values outside the interval joining its endpoints. -/
theorem areaLayerCoordinate_congr_on {I J : Set ℝ} (hI : OrdConnected I)
    {L L' : Plane → ℝ} (hL : EqOn L L' (I ×ˢ J)) {a : ℝ} (ha : a∈I)
    (ρ : ℝ → ℝ) (H : (ι → ℝ) → ℝ) :
    EqOn (areaLayerCoordinate L a ρ H) (areaLayerCoordinate L' a ρ H)
      ((I ×ˢ J) ×ˢ (univ : Set (PlanePhase ι))) := by
  intro p hp
  unfold areaLayerCoordinate layerAreaIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact hL ⟨hI.uIcc_subset ha hp.1.1 hs,hp.1.2⟩

end SymplecticPacking.HighDim.ToricPackingStages
