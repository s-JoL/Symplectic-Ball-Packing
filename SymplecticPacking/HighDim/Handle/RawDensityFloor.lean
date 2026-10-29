import SymplecticPacking.HighDim.Handle.RawSurfaceTree
import SymplecticPacking.HighDim.Polytope
import SymplecticPacking.Explicit

/-!
# A positive floor for native chart densities

A canonical positive floor from finitely many native chart coefficient images.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope

section Minimum
variable {I X : Type} [Fintype I] [Nonempty I] [TopologicalSpace X]

def finiteCoefficientImage (K : I → Set X) (f : I → X → ℝ) : Set ℝ := ⋃ i, f i '' K i

theorem existsUnique_finiteMinimum (K : I → Set X) (f : I → X → ℝ)
    (hK : ∀ i,IsCompact (K i)) (hN : ∀ i,(K i).Nonempty)
    (hf : ∀ i,ContinuousOn (f i) (K i)) : ∃! c,IsLeast (finiteCoefficientImage K f) c := by
  classical
  have hc : IsCompact (finiteCoefficientImage K f) :=
    isCompact_iUnion (fun i => (hK i).image_of_continuousOn (hf i))
  have hn : (finiteCoefficientImage K f).Nonempty := by
    let i : I := Classical.choice inferInstance
    obtain ⟨x,hx⟩ := hN i
    exact ⟨f i x,mem_iUnion.mpr ⟨i,⟨x,hx,rfl⟩⟩⟩
  obtain ⟨c,hc⟩ := hc.exists_isLeast hn
  exact ⟨c,hc,fun y hy => hy.unique hc⟩

def finiteCoefficientMinimum (K : I → Set X) (f : I → X → ℝ)
    (hK : ∀ i,IsCompact (K i)) (hN : ∀ i,(K i).Nonempty)
    (hf : ∀ i,ContinuousOn (f i) (K i)) : ℝ :=
  SymplecticPacking.Explicit.the (existsUnique_finiteMinimum K f hK hN hf)

theorem finiteCoefficientMinimum_spec (K : I → Set X) (f : I → X → ℝ)
    (hK : ∀ i,IsCompact (K i)) (hN : ∀ i,(K i).Nonempty)
    (hf : ∀ i,ContinuousOn (f i) (K i)) :
    IsLeast (finiteCoefficientImage K f) (finiteCoefficientMinimum K f hK hN hf) :=
  SymplecticPacking.Explicit.the_spec (existsUnique_finiteMinimum K f hK hN hf)

theorem finiteCoefficientMinimum_pos (K : I → Set X) (f : I → X → ℝ)
    (hK : ∀ i,IsCompact (K i)) (hN : ∀ i,(K i).Nonempty)
    (hf : ∀ i,ContinuousOn (f i) (K i)) (hp : ∀ i x,x∈K i → 0<f i x) :
    0<finiteCoefficientMinimum K f hK hN hf := by
  have hm := (finiteCoefficientMinimum_spec K f hK hN hf).1
  obtain ⟨i,x,hx,he⟩ := mem_iUnion.mp hm
  simpa only [he] using hp i x hx
end Minimum

namespace RawSurfacePresentation
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] {U : Set M} (D : RawSurfacePresentation E M U)

def rawFrameDensity {n : ℕ}
    (Ω : Moments n → M → E →L[ℝ] E →L[ℝ] ℝ) (Λ : M → E →L[ℝ] E →L[ℝ] ℝ)
    (i : Fin (D.size+1)) (q : Moments n × Plane) : ℝ :=
  let B := D.boxes i
  let x := B.box.chart.symm q.2
  Ω q.1 x (B.frame q.2 (1,0)) (B.frame q.2 (0,1)) /
    Λ x (B.frame q.2 (1,0)) (B.frame q.2 (0,1))

def rawFrameDomain {n q : ℕ} (Δ : Polytope n q) (i : Fin (D.size+1)) : Set (Moments n × Plane) :=
  Δ.set ×ˢ Metric.closedBall (D.boxes i).box.point (D.boxes i).box.radius

def rawDensityFloor {n q : ℕ} (Δ : Polytope n q)
    (Ω : Moments n → M → E →L[ℝ] E →L[ℝ] ℝ) (Λ : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
    (hc : ∀ i,ContinuousOn (D.rawFrameDensity Ω Λ i) (D.rawFrameDomain Δ i)) : ℝ :=
  finiteCoefficientMinimum (D.rawFrameDomain Δ) (D.rawFrameDensity Ω Λ)
    (fun i => hΔc.prod (isCompact_closedBall _ _))
    (fun i => hΔn.prod ⟨(D.boxes i).box.point,Metric.mem_closedBall_self (D.boxes i).box.radius_pos.le⟩)
    hc

theorem rawDensityFloor_pos {n q : ℕ} (Δ : Polytope n q)
    (Ω : Moments n → M → E →L[ℝ] E →L[ℝ] ℝ) (Λ : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
    (hc : ∀ i,ContinuousOn (D.rawFrameDensity Ω Λ i) (D.rawFrameDomain Δ i))
    (hp : ∀ i z,z∈D.rawFrameDomain Δ i → 0<D.rawFrameDensity Ω Λ i z) :
    0<D.rawDensityFloor Δ Ω Λ hΔc hΔn hc :=
  finiteCoefficientMinimum_pos _ _ _ _ _ hp

open Manifold
open scoped ContDiff Manifold Topology
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem rawFrameDensity_continuousOn {n q : ℕ} (Δ : Polytope n q) (hG : D.Geometry)
    {Ω : Moments n → M → E →L[ℝ] E →L[ℝ] ℝ} {Λ : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : Moments n × M => Ω q.1 q.2))
    (hΛ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Λ)
    (i : Fin (D.size+1))
    (hden : ∀ z∈(D.boxes i).box.chart.target,
      Λ ((D.boxes i).box.chart.symm z) ((D.boxes i).frame z (1,0)) ((D.boxes i).frame z (0,1))≠0) :
    ContinuousOn (D.rawFrameDensity Ω Λ i) (D.rawFrameDomain Δ i) := by
  let B := D.boxes i
  let V := (univ : Set (Moments n)) ×ˢ B.box.chart.target
  have hi := (hG.box_smooth i).inverse
  have hmap : ContMDiffOn ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane))
      ((𝓘(ℝ,Moments n)).prod 𝓘(ℝ,Plane)) ∞
      (fun q : Moments n × Plane => (q.1,B.box.chart.symm q.2)) V :=
    contMDiffOn_fst.prodMk (hi.comp contMDiffOn_snd (fun q hq => hq.2))
  have hΩMD := hΩ.comp_contMDiffOn hmap
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΩMD
  have hΛc := (hΛ.comp_contMDiffOn hi).contDiffOn.continuousOn
  have hΛV := hΛc.comp (continuous_snd.continuousOn : ContinuousOn
    (Prod.snd : Moments n × Plane → Plane) V) (fun q hq => hq.2)
  have hJ : ContinuousOn B.frame B.box.chart.target :=
    ((hG.box_inverse i).fderiv_of_isOpen B.box.chart.open_target (m := ∞) (by simp)).continuousOn
  have hJV := hJ.comp (continuous_snd.continuousOn : ContinuousOn
    (Prod.snd : Moments n × Plane → Plane) V) (fun q hq => hq.2)
  have h1 := hJV.clm_apply (continuousOn_const (c := ((1,0):Plane)))
  have h2 := hJV.clm_apply (continuousOn_const (c := ((0,1):Plane)))
  have hnum := (hΩMD.contDiffOn.continuousOn.clm_apply h1).clm_apply h2
  have hdenC := (hΛV.clm_apply h1).clm_apply h2
  exact (hnum.div hdenC (fun z hz => hden z.2 hz.2)).mono
    (fun z hz => ⟨mem_univ _,B.box.closed_subset hz.2⟩)

end RawSurfacePresentation

#check_explicit finiteCoefficientMinimum
#check_explicit RawSurfacePresentation.rawDensityFloor
#check_explicit RawSurfacePresentation.rawFrameDensity
end SymplecticPacking.HighDim.ToricPackingStages
