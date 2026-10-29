import SymplecticPacking.HighDim.Handle.RawFullProductMoserSpec
import SymplecticPacking.HighDim.Handle.NativeAmbientFlow

/-!
# The finite-chart full product Moser flow

Finite chart selection and coordinate ODE for a general ambient one-form path.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M] {U : Set M}
namespace RawSurfacePresentation
variable (D : RawSurfacePresentation E M U)

def fullMoserField (α : ℝ → M × V → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) : E × V := by
  classical
  exact (List.finRange (D.size+1)).foldr (fun i rest =>
    if p.2.1 ∈ (D.boxes i).box.chart.source then
      (D.boxes i).fullMoserField α p.1 p.2 else rest) 0

def cutFullMoserField (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (χ : ℝ × (M × V) → ℝ) (p : ℝ × (M × V)) : E × V := χ p • D.fullMoserField α p

section manifold
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

def fullMoserFlow (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (χ : ℝ × (M × V) → ℝ) (t : ℝ) (x : M × V) : M × V :=
  nativeAmbientFlow D.productInclusion (D.cutFullMoserField α χ) t x

/-- The inverse endpoint uses the reversed ambient field, with no chosen diffeomorphism. -/
def fullMoserInverse (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (χ : ℝ × (M × V) → ℝ) (x : M × V) : M × V :=
  nativeAmbientFlow D.productInclusion
    (fun p => -D.cutFullMoserField α χ (1-p.1,p.2)) 1 x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productInclusion_contMDiff
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion) :
    ContMDiff 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) ∞ (D.productInclusion (V:=V)) := by
  have hid : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (id : V → V) := contMDiff_id
  have h := hι.prodMap hid
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem productInclusion_mfderiv
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion) (x : M × V) :
    mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) D.productInclusion x =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
  rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (mfderiv_prodMap (hι.mdifferentiable (by simp) x.1)
    (mdifferentiableAt_id (I:=𝓘(ℝ,V)) (x:=x.2))).trans (by rw [mfderiv_id]; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullMoserField_eq_manifoldMoserField
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (p : ℝ × (M × V)) (hcover : ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible) :
    D.fullMoserField α p =
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion p.2.1).prodMap (ContinuousLinearMap.id ℝ V))
        (manifoldMoserField (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
          (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s))) p) := by
  classical
  unfold fullMoserField
  apply fold_first_eq
  · intro i _ hi
    let y : Plane × V := ((D.boxes i).box.chart p.2.1,p.2.2)
    have hy : y.1 ∈ (D.boxes i).box.chart.target := (D.boxes i).box.chart.map_source hi
    have he : flatProductMap (D.boxes i).box.chart.symm y = p.2 := by
      apply Prod.ext
      · exact (D.boxes i).box.chart.left_inv hi
      · rfl
    have hh := (D.boxes i).fullMoserField_eq_manifoldMoserField hι (D.box_inclusion i)
      (hB i) α hα p.1 hy (he.symm ▸ hinv)
    rw [he] at hh
    have hxy : (D.boxes i).box.chart.symm y.1 = p.2.1 := (D.boxes i).box.chart.left_inv hi
    rw [hxy] at hh
    exact hh
  · intro hn
    obtain ⟨i,hi⟩ := hcover
    exact False.elim (hn ⟨i,by simp,hi⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem cutFullMoserField_eq_cutField
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (χ : ℝ × (M × V) → ℝ) (p : ℝ × (M × V))
    (hcover : χ p ≠ 0 → ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source)
    (hinv : χ p ≠ 0 → (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible) :
    D.cutFullMoserField α χ p = mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) D.productInclusion p.2
      (cutField χ (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
        (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s))) p) := by
  by_cases hz : χ p = 0
  · simp only [cutFullMoserField,cutField,hz,zero_smul,map_zero]
  · rw [D.productInclusion_mfderiv hι,cutFullMoserField,
      D.fullMoserField_eq_manifoldMoserField hι hB α hα p (hcover hz) (hinv hz),
      cutField,moserVec_eq (hinv hz)]
    exact (map_smul _ _ _).symm

theorem fullMoserFlow_eq_fieldFlow
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion x))
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (hregular : AmbientRegularity (K:=Plane × V) (D.productInclusion (V:=V)))
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (χ : ℝ × (M × V) → ℝ)
    (hcover : ∀ p, χ p ≠ 0 → ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source)
    (hinv : ∀ p, χ p ≠ 0 → (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible)
    (t : ℝ) (x : M × V) :
    D.fullMoserFlow α χ t x = fieldFlow
      (cutField χ (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
        (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s)))) t x := by
  unfold fullMoserFlow
  rw [nativeAmbientFlow_eq_ambientFieldFlow hregular]
  apply ambientFieldFlow_eq_fieldFlow (D.productInclusion_contMDiff hι)
  · intro z u v h
    rw [D.productInclusion_mfderiv hι] at h
    have hf := congrArg (fun w : E × V => w.1) h
    have hs := congrArg (fun w : E × V => w.2) h
    exact Prod.ext (hinj z.1 hf) hs
  · intro p
    exact D.cutFullMoserField_eq_cutField hι hB α hα χ p (hcover p) (hinv p)

/-- The strong support condition, rather than non-vanishing alone, gives smoothness
across the singular-form boundary. The native field has the same trajectories by the
preceding correspondence theorem. -/
theorem semantic_cut_field_smooth [FiniteDimensional ℝ V]
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (χ : ℝ × (M × V) → ℝ)
    (hχs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ χ)
    {G : Set (ℝ × (M × V))} (hG : IsOpen G)
    (hinv : ∀ p ∈ G, (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible)
    (hχG : tsupport χ ⊆ G) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) (𝓘(ℝ,Plane × V)).tangent ∞
      (fun p => (⟨p.2,cutField χ
        (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
        (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s))) p⟩ :
        TangentBundle 𝓘(ℝ,Plane × V) (M × V))) := by
  have he := cutField_eq_inv (E:=Plane × V) (M:=M × V)
    (Ω:=fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
    (α:=manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s))) hinv hχG
  simp_rw [he]
  have hΩ := manifoldExteriorOneForm_path_smooth (E:=Plane × V) (M:=M × V) hα
  have ha := manifoldTimePrimitive_smooth (E:=Plane × V) (M:=M × V) hα
  exact cutField_smooth (E:=Plane × V) (M:=M × V)
    (Ω:=fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
    (α:=manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s)))
    hΩ ha hG hinv hχs hχG

end manifold
end RawSurfacePresentation
#check_explicit RawSurfacePresentation.fullMoserField
#check_explicit RawSurfacePresentation.cutFullMoserField
#check_explicit RawSurfacePresentation.fullMoserFlow
#check_explicit RawSurfacePresentation.fullMoserInverse
end SymplecticPacking.HighDim.ToricPackingStages
