import SymplecticPacking.HighDim.Handle.CubicRawModel

/-!
# A total native cubic model

A total native cubic model: the finite coefficient minimum is zero only when
its defining finite coefficient image has no least element. Inputs have a
positive least element, proved independently by the provider.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] RawCubic.physicalExtension quadricTreeAt quadricTreeOrder quadricTreePrefix

section Minimum
variable {I X : Type} [Fintype I] [Nonempty I] [TopologicalSpace X]

def FiniteMinimumOrZero (K : I → Set X) (f : I → X → ℝ) (c : ℝ) : Prop :=
  (∀ d,IsLeast (finiteCoefficientImage K f) d → c=d) ∧
    ((¬∃ d,IsLeast (finiteCoefficientImage K f) d) → c=0)

theorem existsUnique_finiteMinimumOrZero (K : I → Set X) (f : I → X → ℝ) :
    ∃! c,FiniteMinimumOrZero K f c := by
  classical
  by_cases h : ∃ d,IsLeast (finiteCoefficientImage K f) d
  · obtain ⟨d,hd⟩ := h
    refine ⟨d,⟨fun e he => hd.unique he,fun hn => False.elim (hn ⟨d,hd⟩)⟩,?_⟩
    intro e he
    exact he.1 d hd
  · exact ⟨0,⟨fun d hd => False.elim (h ⟨d,hd⟩),fun _ => rfl⟩,fun e he => he.2 h⟩

def finiteMinimumOrZero (K : I → Set X) (f : I → X → ℝ) : ℝ :=
  SymplecticPacking.Explicit.the (existsUnique_finiteMinimumOrZero K f)

theorem finiteMinimumOrZero_eq_minimum (K : I → Set X) (f : I → X → ℝ)
    (hK : ∀ i,IsCompact (K i)) (hN : ∀ i,(K i).Nonempty)
    (hf : ∀ i,ContinuousOn (f i) (K i)) :
    finiteMinimumOrZero K f=finiteCoefficientMinimum K f hK hN hf :=
  (SymplecticPacking.Explicit.the_spec (existsUnique_finiteMinimumOrZero K f)).1 _
    (finiteCoefficientMinimum_spec K f hK hN hf)
end Minimum

/-- This constructor has no proof inputs and no geometric tensor inputs. -/
def cubicRawTotalModel (A B D S : ℕ) (c L : ℝ) (q ℓ : ℕ) (Δ : Polytope 2 q) :
    RawToricModel (Affine 2) BaseCurve 2 q :=
  let Ω := fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val
  let F := quadricModelRawPresentation 0 ℓ
  { quadricScalarRawModel 0 2 q ℓ Δ (fun _ => 0) 0 with
    physicalPrimitive p x := RawCubic.physicalExtension A B D S c L Δ.set ℓ p x.val
    physicalForm := Ω
    densityFloor := finiteMinimumOrZero (F.rawFrameDomain Δ) (F.rawFrameDensity Ω (quadricReferenceForm 0)) }

theorem cubicRawTotalModel_eq {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ) (c L : ℝ)
    (q ℓ : ℕ) (Δ : Polytope 2 q) (hΔc : IsCompact Δ.set) (hΔn : Δ.set.Nonempty)
    (hm : 0<PrimExt.margin A B L Δ.set) (hmA : PrimExt.margin A B L Δ.set≤A) :
    cubicRawTotalModel A B D S c L q ℓ Δ=cubicRawModel hA hAB D S c L q ℓ Δ hΔc hΔn hm hmA := by
  have he := finiteMinimumOrZero_eq_minimum
    ((quadricModelRawPresentation 0 ℓ).rawFrameDomain Δ)
    ((quadricModelRawPresentation 0 ℓ).rawFrameDensity
      (fun p (x : BaseCurve) => CubicRawPhysical.form A B D S c L Δ.set ℓ p x.val) (quadricReferenceForm 0))
    (fun i => hΔc.prod (isCompact_closedBall _ _))
    (fun i => hΔn.prod ⟨((quadricModelRawPresentation 0 ℓ).boxes i).box.point,
      Metric.mem_closedBall_self ((quadricModelRawPresentation 0 ℓ).boxes i).box.radius_pos.le⟩)
    (quadricNativeFloor_continuous ℓ Δ _ (CubicRawPhysical.form_restriction_smooth hA hAB D S c L Δ.set ℓ hm hmA))
  dsimp only [cubicRawTotalModel,cubicRawModel]
  congr 1

#check_explicit finiteMinimumOrZero
#check_explicit cubicRawTotalModel
end SymplecticPacking.HighDim.ToricPackingStages
