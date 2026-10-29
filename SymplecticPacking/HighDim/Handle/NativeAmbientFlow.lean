import SymplecticPacking.HighDim.Handle.RawMoser

/-!
# Native ambient flow endpoints

An ambient ODE endpoint whose data does not read a preferred manifold atlas.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

def IsNativeAmbientCurve (ι : M → E) (F : ℝ × M → E) (x : M) (γ : ℝ → M) : Prop :=
  γ 0=x ∧ ContinuousOn γ (Ioo (-2:ℝ) 2) ∧
    ∀ t ∈ Ioo (-2:ℝ) 2,HasDerivAt (fun s => ι (γ s)) (F (t,γ t)) t

open Classical in
def nativeAmbientFlow (ι : M → E) (F : ℝ × M → E) (t : ℝ) (x : M) : M :=
  if h : ∃! y,∃ γ,IsNativeAmbientCurve ι F x γ ∧ γ t=y then Explicit.the h else x

open Classical in
/-- The inverse of an explicitly supplied bijection, with identity fallback. -/
def nativeInverse (f : M → M) (y : M) : M :=
  if h : ∃! x,f x=y then Explicit.the h else y

theorem nativeInverse_eq_symm {f : M → M} (e : M ≃ M) (he : ⇑e=f) :
    nativeInverse f=e.symm := by
  funext y
  have hs : f (e.symm y)=y := by simpa only [←he] using e.apply_symm_apply y
  have hu : ∃! x,f x=y := ⟨e.symm y,hs,fun z hz => by
    apply e.injective
    simpa only [←he,e.apply_symm_apply] using hz⟩
  unfold nativeInverse
  rw [dif_pos hu]
  exact Explicit.the_eq hu hs

section comparison
variable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [ChartedSpace K M] [IsManifold 𝓘(ℝ,K) ∞ M]

/-- A proof-only regularity statement for the specified embedding. -/
def AmbientRegularity (ι : M → E) : Prop :=
  ∀ γ : ℝ → M,ContinuousOn γ (Ioo (-2:ℝ) 2) →
    DifferentiableOn ℝ (ι ∘ γ) (Ioo (-2:ℝ) 2) →
    MDifferentiableOn 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ (Ioo (-2:ℝ) 2)

theorem nativeAmbientCurve_iff {ι : M → E} (hregular : AmbientRegularity (K:=K) ι)
    (F : ℝ × M → E) (x : M) (γ : ℝ → M) :
    IsNativeAmbientCurve ι F x γ ↔ IsAmbientFieldCurve (K:=K) ι F x γ := by
  constructor
  · rintro ⟨h0,hc,hd⟩
    exact ⟨h0,hregular γ hc (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt),hd⟩
  · rintro ⟨h0,hd,hODE⟩
    exact ⟨h0,hd.continuousOn,hODE⟩

theorem nativeAmbientFlow_eq_ambientFieldFlow {ι : M → E}
    (hregular : AmbientRegularity (K:=K) ι) (F : ℝ × M → E) (t : ℝ) (x : M) :
    nativeAmbientFlow ι F t x=ambientFieldFlow (K:=K) ι F t x := by
  have he : IsNativeAmbientCurve ι F x=IsAmbientFieldCurve (K:=K) ι F x := by
    funext γ
    exact propext (nativeAmbientCurve_iff hregular F x γ)
  unfold nativeAmbientFlow ambientFieldFlow
  rw [he]
end comparison

section rawCover
variable [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productAmbientRegularity_of_rawCover {ι : M → E}
    (hcover : ∀ x : M,∃ B : RawAmbientBox E M,
      B.inclusion=ι ∧ B.box.Smooth ∧ x∈B.box.chart.source) :
    AmbientRegularity (K:=Plane × V) (fun x : M × V => (ι x.1,x.2)) := by
  intro γ hc hd t ht
  obtain ⟨B,hinc,hB,hx⟩ := hcover (γ t).1
  have hγ := hc.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hcoord : DifferentiableAt ℝ (fun s => (B.coordinate (ι (γ s).1),(γ s).2)) t :=
    (B.coordinate.prodMap (ContinuousLinearMap.id ℝ V)).differentiableAt.comp t
      ((hd t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  have hy : B.box.chart (γ t).1∈B.box.chart.target := B.box.chart.map_source hx
  have hi := ((hB.inverse _ hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hinv := hi.prodMap (mdifferentiableAt_id (I:=𝓘(ℝ,V)) (x:=(γ t).2))
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hinv
  have hcEq : B.coordinate (ι (γ t).1)=B.box.chart (γ t).1 := by
    rw [←hinc]
    exact B.coordinate_eq _
  rw [←hcEq] at hinv
  have hm := hinv.comp t hcoord.mdifferentiableAt
  have he : (fun s => (B.box.chart.symm (B.coordinate (ι (γ s).1)),(γ s).2)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hγ.fst.preimage_mem_nhds (B.box.chart.open_source.mem_nhds hx)] with s hs
    apply Prod.ext
    · rw [←hinc,B.coordinate_eq,B.box.chart.left_inv hs]
    · rfl
  exact (he.mdifferentiableAt_iff.mp hm).mdifferentiableWithinAt
end rawCover
#check_explicit nativeAmbientFlow
#check_explicit nativeInverse
end SymplecticPacking.HighDim.ToricPackingStages
