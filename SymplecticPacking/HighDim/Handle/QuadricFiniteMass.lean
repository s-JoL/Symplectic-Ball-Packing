import SymplecticPacking.HighDim.Handle.QuadricFinitePresentation
import SymplecticPacking.HighDim.Handle.QuadricRawUnitBumpMass
import SymplecticPacking.HighDim.Handle.RawUnitSupportProjection
import SymplecticPacking.HighDim.Handle.RawSurfaceIntrinsicMass
import SymplecticPacking.HighDim.Handle.QuadricRawGlobalCover

/-!
# Calibrated mass of the finite quadric presentation

The finite root-chart integral is calibrated without an area oracle.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
attribute [local irreducible] quadricTreeAt quadricTreeOrder quadricTreePrefix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j,(a j:ℂ)≠0)]
variable {R : ℚ} (hR : 0<R)
  (hsep₀ : ∀ i,1≤‖(a i:ℂ)‖)
  (hsep : ∀ i j,j≠i → 1≤‖(a i:ℂ)-(a j:ℂ)‖)
  (hbranch : ∀ i,‖(a i:ℂ)‖<(R:ℝ)^2)

local instance : SigmaCompactSpace (locus (fun j => (a j:ℂ))) := curveSigmaCompact _

local notation "D" => quadricFinitePresentation a hR hsep₀ hsep hbranch

theorem quadricFinitePresentation_root_unit_mass
    {I : Type} [Fintype I] {L : Set (locus (fun j => (a j:ℂ)))}
    (Boxes : I → SurfaceCoordinateBox (locus (fun j => (a j:ℂ))))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus (fun j => (a j:ℂ))) L)
    (hρ : ρ.IsSubordinate (fun i => (Boxes i).carrier))
    (hUL : ((D).boxes (D).root).unitSupport ⊆ L) :
    partitionFormMass Boxes ρ (semanticTwoForm (D).inclusion ((D).boxes (D).root).unitBump)=1 := by
  let C := quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch 0)
  have hC : ((D).boxes (D).root).box.chart=C.chart :=
    quadricTightRootChart_chart a hR.le hsep₀ hsep _
  have hc : C.chart=rawQuadricRealChart C.centre C.tag C.regular := by
    rcases C with ⟨c,tag,hc⟩
    cases tag <;> rfl
  exact quadricRawUnitBump_partition_mass ((D).boxes (D).root) C.centre C.tag C.regular
    (hC.trans hc) rfl ((quadricFinitePresentation_geometry a hR hsep₀ hsep hbranch).box_smooth (D).root)
    ((quadricFinitePresentation_geometry a hR hsep₀ hsep hbranch).box_inverse (D).root) Boxes ρ hρ hUL

theorem quadricFinitePresentation_root_core (hR1 : (1:ℚ)≤R) :
    ((D).boxes (D).root).unitSupport ⊆ projectionDomain (fun j => (a j:ℂ)) R := by
  apply unitSupport_projection_subset
  · intro x
    change (quadricTightFiniteBox a hR.le hsep₀ hsep
      (quadricTreeAt a hR hsep₀ hsep hbranch 0)).chart x=Complex.equivRealProdCLM x.val.1
    rw [quadricTreeAt_zero a hR hsep₀ hsep hbranch]
    rfl
  · change ‖Complex.equivRealProdCLM.symm (quadricTightFiniteBox a hR.le hsep₀ hsep
        (quadricTreeAt a hR hsep₀ hsep hbranch 0)).point‖+
      (quadricTightFiniteBox a hR.le hsep₀ hsep
        (quadricTreeAt a hR hsep₀ hsep hbranch 0)).radius≤(R:ℝ)
    rw [quadricTreeAt_zero a hR hsep₀ hsep hbranch,quadricTightRoot_point,quadricTightRoot_radius]
    simp only [map_zero,norm_zero,zero_add]
    have hle : quadricGridRadius R≤R := (quadricGridRadius_bound hR.le).trans (by linarith)
    exact_mod_cast hle

theorem quadricFinitePresentation_root_support : ((D).boxes (D).root).unitSupport⊆(D).support := by
  intro x hx
  exact mem_iUnion.mpr ⟨(D).root,((D).boxes (D).root).box.carrier_subset_compactCarrier
    (((D).boxes (D).root).unitSupport_subset hx)⟩

theorem quadricFinitePresentation_calibration_ne_zero (hR1 : (1:ℚ)≤R) : (D).massCalibration≠0 := by
  classical
  let hL := (D).support_compact
  let Boxes := fun b : compactSurfaceBoxes hL => b.1
  let ρ := compactSurfacePartition hL
  have hρ := compactSurfacePartition_subordinate hL
  have hu := quadricFinitePresentation_root_unit_mass a hR hsep₀ hsep hbranch Boxes ρ hρ
    (quadricFinitePresentation_root_support a hR hsep₀ hsep hbranch)
  apply (D).massCalibration_ne_zero (quadricFinitePresentation_geometry a hR hsep₀ hsep hbranch)
    (real_inclusion_contMDiff _) (quadric_raw_global_cover _) (positivePlaneTransitions _)
    hL _ Subset.rfl Boxes ρ hρ hu
  exact (quadricFinitePresentation_root_core a hR hsep₀ hsep hbranch hR1).trans
    (quadricFinitePresentation_cover a hR hsep₀ hsep hbranch)

theorem quadricFinitePresentation_calibratedMass_eq (hR1 : (1:ℚ)≤R)
    {Ω : locus (fun j => (a j:ℂ)) → Affine m →L[ℝ] Affine m →L[ℝ] ℝ}
    (hΩ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Affine m →L[ℝ] Affine m →L[ℝ] ℝ) ∞ Ω)
    (hsk : ∀ x u v,Ω x u v = -Ω x v u)
    (hz : ∀ x,x∉projectionDomain (fun j => (a j:ℂ)) R → Ω x=0) :
    (D).calibratedMass Ω=compactSurfaceFormIntegral
      (projectionDomain_compact (fun j => (a j:ℂ)) R) (semanticTwoForm Subtype.val Ω) := by
  classical
  let K := projectionDomain (fun j => (a j:ℂ)) (R:ℝ)
  have hK : IsCompact K := projectionDomain_compact _ _
  let L := (D).support ∪ K
  have hL : IsCompact L := (D).support_compact.union hK
  let Boxes := fun b : compactSurfaceBoxes hL => b.1
  let ρ := compactSurfacePartition hL
  have hρ := compactSurfacePartition_subordinate hL
  have hu := quadricFinitePresentation_root_unit_mass a hR hsep₀ hsep hbranch Boxes ρ hρ
    ((quadricFinitePresentation_root_support a hR hsep₀ hsep hbranch).trans subset_union_left)
  have hm := (D).calibratedMass_eq_partition (quadricFinitePresentation_geometry a hR hsep₀ hsep hbranch)
    (real_inclusion_contMDiff _) (quadric_raw_global_cover _) (positivePlaneTransitions _)
    hK hL (quadricFinitePresentation_cover a hR hsep₀ hsep hbranch)
    subset_union_right subset_union_left (quadricFinitePresentation_root_core a hR hsep₀ hsep hbranch hR1)
    Boxes ρ hρ hu hΩ hsk hz
  have hs := semanticTwoForm_smooth (real_inclusion_contMDiff _) hΩ
  have ha (x) (u v : Plane) : semanticTwoForm Subtype.val Ω x u v = -semanticTwoForm Subtype.val Ω x v u :=
    hsk x _ _
  have hind : K.indicator (semanticTwoForm Subtype.val Ω)=semanticTwoForm Subtype.val Ω := by
    funext x
    by_cases hx : x∈K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,semanticTwoForm_zero_at _ (hz x hx)]
  have hi := compactSurfaceFormIntegral_eq_larger_partition hK (positivePlaneTransitions _)
    (show K⊆L from subset_union_right) Boxes ρ hρ hs ha
  rw [restrictedPartitionFormMass_eq_indicator _ _ hK.measurableSet,hind] at hi
  exact hm.trans hi.symm

end SymplecticPacking.HighDim.ToricPackingStages
