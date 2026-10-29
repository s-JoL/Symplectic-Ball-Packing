import SymplecticPacking.HighDim.Handle.RawSurfaceOperator
import SymplecticPacking.HighDim.Handle.RawAmbientFamily

/-!
# Smooth parameter dependence of the raw partition integral

Smooth parameter dependence of the raw finite partition integral.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)

theorem weightedForm_zero {K : Set M} {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hzΩ : ∀ p x, x ∉ K → Ω p x = 0)
    (p : P) (i : Fin (D.size+1)) (x : M) (hx : x ∉ K ∩ tsupport (D.partitionWeight i)) :
    D.weightedForm (Ω p) i x = 0 := by
  by_cases hxK : x ∈ K
  · have hp : D.partitionWeight i x = 0 := by
      by_contra hn
      exact hx ⟨hxK,subset_closure hn⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change D.partitionWeight i x*Ω p x u v=0
    rw [hp,zero_mul]
  · unfold weightedForm
    rw [hzΩ p x hxK]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change _*(0:ℝ)=0
    ring

theorem weightedForm_family_smooth (hG : D.Geometry)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2)) (i : Fin (D.size+1)) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => D.weightedForm (Ω q.1) i q.2) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hρ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (D.partitionWeight i) :=
    RawBoxFamily.partitionWeight_smooth (fun j => (D.boxes j).box) hG.box_smooth i
  exact (hρ.comp contMDiff_snd).smul hΩ

theorem weightedMass_family_smooth (hG : D.Geometry)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hzΩ : ∀ p x, x ∉ K → Ω p x = 0)
    (i : Fin (D.size+1)) : ContDiff ℝ ∞ (fun p => D.weightedMass (Ω p) i) :=
  (D.boxes i).mass_family_smooth (hG.box_smooth i) (hG.box_inverse i)
    (D.weightedForm_family_smooth hG hΩ i) (hK.inter_right (isClosed_tsupport _))
    (fun x hx => (D.partitionWeight_support i hx.2).1) (fun p x hx => D.weightedForm_zero hzΩ p i x hx)

theorem primitiveOperator_family_smooth (hG : D.Geometry)
    {Ω : P → M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => Ω q.1 q.2))
    {K : Set M} (hK : IsCompact K) (hzΩ : ∀ p x, x ∉ K → Ω p x = 0) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => D.primitiveOperator (Ω q.1) q.2) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  let : MulActionWithZero ℝ (E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
  let L (i) := K ∩ tsupport (D.partitionWeight i)
  have hLc (i) : IsCompact (L i) := hK.inter_right (isClosed_tsupport _)
  have hLB (i) : L i ⊆ (D.boxes i).box.carrier :=
    fun x hx => D.partitionWeight_support i hx.2
  have hWp (p : P) (i : Fin (D.size+1)) :
      ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (D.weightedForm (Ω p) i) := by
    have hconst : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,P) ∞ (fun _ : M => p) := contMDiff_const
    have hpair := hconst.prodMk (contMDiff_id (I := 𝓘(ℝ,Plane)))
    exact (D.weightedForm_family_smooth hG hΩ i).comp hpair
  have hM (i) : ContDiff ℝ ∞ (fun p => D.weightedMass (Ω p) i) :=
    D.weightedMass_family_smooth hG hΩ hK hzΩ i
  have hlocal (i : Fin (D.size+1)) :
      ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
        (fun q : P × M => (D.boxes i).formPrimitive
          (D.weightedForm (Ω q.1) i-D.weightedMass (Ω q.1) i • (D.boxes i).unitBump) q.2) := by
    let B := D.boxes i
    have hms : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
        (fun q : P × M => D.weightedMass (Ω q.1) i) := (hM i).contMDiff.comp contMDiff_fst
    have hbs : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun q : P × M => B.unitBump q.2) :=
      (B.unitBump_smooth (hG.box_smooth i)).comp contMDiff_snd
    let Ξ : P → M → E →L[ℝ] E →L[ℝ] ℝ := fun p x =>
      D.weightedForm (Ω p) i x-D.weightedMass (Ω p) i • B.unitBump x
    have hΞ : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun q : P × M => Ξ q.1 q.2) :=
      (D.weightedForm_family_smooth hG hΩ i).sub (hms.smul hbs)
    have hzero : ∀ p x, x ∉ L i ∪ B.unitSupport → Ξ p x=0 := by
      intro p x hx
      change D.weightedForm (Ω p) i x-D.weightedMass (Ω p) i • B.unitBump x=0
      rw [D.weightedForm_zero hzΩ p i x (fun hh => hx (Or.inl hh)),
        B.unitBump_zero (fun hh => hx (Or.inr hh))]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change (0:ℝ)-D.weightedMass (Ω p) i*0=0
      ring
    have hmass : ∀ p, B.mass (Ξ p)=0 := by
      intro p
      have hWI := B.coefficient_integrable (hG.box_smooth i) (hG.box_inverse i)
        (hWp p i) (hLc i) (fun x hx => (hLB i hx).1) (D.weightedForm_zero hzΩ p i)
      have hBI := B.coefficient_integrable (hG.box_smooth i) (hG.box_inverse i)
        (B.unitBump_smooth (hG.box_smooth i)) B.unitSupport_compact
        (fun x hx => (B.unitSupport_subset hx).1) (fun x hx => B.unitBump_zero hx)
      have hSI : MeasureTheory.Integrable
          (B.coefficient (D.weightedMass (Ω p) i • B.unitBump)) := by
        rw [B.coefficient_smul]
        exact hBI.const_mul _
      change B.mass (D.weightedForm (Ω p) i-D.weightedMass (Ω p) i • B.unitBump)=0
      rw [B.mass_sub hWI hSI,B.mass_smul,B.unitBump_mass (hG.box_inverse i),mul_one]
      change D.weightedMass (Ω p) i-D.weightedMass (Ω p) i=0
      ring
    change ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun q : P × M => B.formPrimitive (Ξ q.1) q.2)
    exact B.formPrimitive_family_smooth (hG.box_smooth i) (hG.box_inverse i) (Ω := Ξ)
      hΞ ((hLc i).union B.unitSupport_compact) (union_subset (hLB i) B.unitSupport_subset)
      hzero hmass
  have ht (i : Fin (D.size+1)) :
      ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
        (fun q : P × M => D.weightedMass (Ω q.1) i • D.treePrimitive i q.2) :=
    ((hM i).contMDiff.comp contMDiff_fst).smul
      ((D.treePrimitive_isPrimitive hG i).smooth.comp contMDiff_snd)
  have hs := ContMDiff.sum (fun i (_ : i ∈ Finset.univ) => (hlocal i).add (ht i))
  simpa only [primitiveOperator,Finset.sum_apply,Pi.add_apply,Pi.smul_apply] using hs

end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
