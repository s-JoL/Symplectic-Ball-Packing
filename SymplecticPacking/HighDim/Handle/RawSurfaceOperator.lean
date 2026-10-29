import SymplecticPacking.HighDim.Handle.RawSurfaceTreeSupport

/-!
# Correctness of the raw primitive operator

Correctness of the raw finite partition and mass-redistribution formula.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology Manifold
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
namespace RawSurfacePresentation
variable {U : Set M} (D : RawSurfacePresentation E M U)

theorem partitionWeight_support (i : Fin (D.size+1)) :
    tsupport (D.partitionWeight i) ⊆ (D.boxes i).box.carrier := by
  apply Subset.trans (closure_mono ?_) (RawCoordinateBox.weight_support (D.boxes i).box)
  intro x hx
  change RawCoordinateBox.weight (D.boxes i).box x ≠ 0
  intro hz
  apply hx
  change RawCoordinateBox.weight (D.boxes i).box x /
    RawBoxFamily.partitionDenom (fun j => (D.boxes j).box) x = 0
  rw [hz,zero_div]

theorem primitiveOperator_data (hG : D.Geometry)
    {K : Set M} (hK : IsCompact K)
    (hcover : K ⊆ ⋃ i, (D.boxes i).box.inner)
    {Ω : M → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v, Ω x u v = -Ω x v u)
    (hzΩ : ∀ x, x ∉ K → Ω x = 0)
    (hm : (∑ i, D.weightedMass Ω i) = 0) :
    RawIsPrimitive D.inclusion Ω (D.primitiveOperator Ω) ∧
      (∀ x, x ∉ D.support → D.primitiveOperator Ω x = 0) := by
  let : MulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hρ (i) : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (D.partitionWeight i) :=
    RawBoxFamily.partitionWeight_smooth (fun j => (D.boxes j).box) hG.box_smooth i
  have hw (i) : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (D.weightedForm Ω i) :=
    (hρ i).smul hΩ
  let L (i) := K ∩ tsupport (D.partitionWeight i)
  have hLc (i) : IsCompact (L i) := hK.inter_right (isClosed_tsupport _)
  have hLB (i) : L i ⊆ (D.boxes i).box.carrier :=
    fun x hx => D.partitionWeight_support i hx.2
  have hwz (i) (x) (hx : x ∉ L i) : D.weightedForm Ω i x = 0 := by
    by_cases hxK : x ∈ K
    · have hp : D.partitionWeight i x = 0 := by
        by_contra hn
        exact hx ⟨hxK, subset_closure hn⟩
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change D.partitionWeight i x*Ω x u v = 0
      rw [hp,zero_mul]
    · unfold weightedForm
      rw [hzΩ x hxK]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change _ * (0:ℝ) = 0
      ring
  have hlocal (i : Fin (D.size+1)) : RawIsPrimitive D.inclusion
      (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump)
      ((D.boxes i).formPrimitive
        (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump)) ∧
      (∀ x, x ∉ (D.boxes i).box.compactCarrier →
        (D.boxes i).formPrimitive
          (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump) x = 0) := by
    let B := D.boxes i
    let a := D.weightedMass Ω i
    have hconst : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun _ : M => a) := contMDiff_const
    have hscaled : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (a • B.unitBump) :=
      hconst.smul (B.unitBump_smooth (hG.box_smooth i))
    have hh := B.difference_data (hG.box_smooth i) (hG.box_inverse i)
      (hw i) hscaled
      (by
        intro x u v
        change D.partitionWeight i x*Ω x u v = -(D.partitionWeight i x*Ω x v u)
        rw [hsk x u v]
        ring)
      (by
        intro x u v
        change a*B.unitBump x u v = -(a*B.unitBump x v u)
        have hbu : B.unitBump x u v = -B.unitBump x v u :=
          B.supportedForm_skew B.unitBumpCoefficient x u v
        rw [hbu]
        ring)
      (hLc i) B.unitSupport_compact (hLB i) B.unitSupport_subset (hwz i)
      (by
        intro x hx
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        change a*B.unitBump x u v = 0
        rw [B.unitBump_zero hx]
        change a*0 = 0
        ring)
      (by
        rw [B.mass_smul, B.unitBump_mass (hG.box_inverse i), mul_one]
        rfl)
    change RawIsPrimitive (D.boxes i).inclusion _ _ ∧ _ at hh
    rw [D.box_inclusion i] at hh
    exact hh
  have hall := RawIsPrimitive.sum Finset.univ
    (fun i => (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump)+
      D.weightedMass Ω i • ((D.boxes i).unitBump-(D.boxes D.root).unitBump))
    (fun i => (D.boxes i).formPrimitive
      (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump)+
      D.weightedMass Ω i • D.treePrimitive i)
    (fun i _ => (hlocal i).1.add ((D.treePrimitive_isPrimitive hG i).smul (D.weightedMass Ω i)))
  have hsum : (∑ i, ((D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump)+
      D.weightedMass Ω i • ((D.boxes i).unitBump-(D.boxes D.root).unitBump))) = Ω := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [Finset.sum_apply, ContinuousLinearMap.sum_apply]
    change (∑ i, ((D.partitionWeight i x*Ω x u v-D.weightedMass Ω i*(D.boxes i).unitBump x u v)+
      D.weightedMass Ω i*((D.boxes i).unitBump x u v-(D.boxes D.root).unitBump x u v))) = Ω x u v
    simp_rw [show ∀ i, (D.partitionWeight i x*Ω x u v-D.weightedMass Ω i*(D.boxes i).unitBump x u v)+
        D.weightedMass Ω i*((D.boxes i).unitBump x u v-(D.boxes D.root).unitBump x u v) =
        D.partitionWeight i x*Ω x u v-D.weightedMass Ω i*(D.boxes D.root).unitBump x u v by
      intro i; ring]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hm, zero_mul, sub_zero]
    by_cases hx : x ∈ K
    · have hs := (RawBoxFamily.partition (fun j => (D.boxes j).box) hG.box_smooth hcover).sum_eq_one hx
      change (∑ᶠ i, D.partitionWeight i x) = 1 at hs
      rw [finsum_eq_sum_of_fintype] at hs
      rw [hs,one_mul]
    · rw [hzΩ x hx]
      simp only [zero_apply, mul_zero]
  rw [hsum] at hall
  refine ⟨hall, ?_⟩
  intro x hx
  unfold primitiveOperator
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hxB : x ∉ (D.boxes i).box.compactCarrier :=
    fun hh => hx (mem_iUnion.mpr ⟨i,hh⟩)
  change (D.boxes i).formPrimitive
    (D.weightedForm Ω i-D.weightedMass Ω i • (D.boxes i).unitBump) x +
    D.weightedMass Ω i • D.treePrimitive i x = 0
  rw [(hlocal i).2 x hxB, D.treePrimitive_zero hG i x hx]
  apply ContinuousLinearMap.ext
  intro u
  change (0:ℝ)+D.weightedMass Ω i*0=0
  ring

end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
