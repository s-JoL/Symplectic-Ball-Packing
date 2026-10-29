import SymplecticPacking.BranchLarge3.PrimitiveExtension

/-!
# Extension margins of the cubic moment region

The compact moment region supplies the explicit extension-margin inequalities.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3

theorem cubicRaw_margin_bounds {A B : ℕ} (hA : 0<A) (hAB : A≤B) (L : ℝ)
    {P : Set (Moments 2)} (hP : IsCompact P) (hn : P.Nonempty)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B)) :
    0<PrimExt.margin A B L P ∧ PrimExt.margin A B L P≤A := by
  have hpc := (physicalParameter_smooth L).continuous
  have hc1 : Continuous (fun p => (physicalParameter L p).1) := hpc.fst
  have hc2 : Continuous (fun p => (physicalParameter L p).1+(physicalParameter L p).2) := hpc.fst.add hpc.snd
  have hs1lt : PrimExt.sOne L P<A ∧ 0≤PrimExt.sOne L P := by
    obtain ⟨p,hp,he⟩ := (hP.image hc1).sSup_mem (hn.image _)
    unfold PrimExt.sOne
    rw [←he]
    exact ⟨(hPS hp).2.1,(hPS hp).1⟩
  have hs2lt : PrimExt.sTwo L P<B := by
    obtain ⟨p,hp,he⟩ := (hP.image hc2).sSup_mem (hn.image _)
    unfold PrimExt.sTwo
    rw [←he]
    exact (hPS hp).2.2.2
  constructor
  · unfold PrimExt.margin
    have h := lt_min (sub_pos.mpr hs1lt.1) (sub_pos.mpr hs2lt)
    linarith
  · unfold PrimExt.margin
    have h := min_le_left ((A:ℝ)-PrimExt.sOne L P) ((B:ℝ)-PrimExt.sTwo L P)
    have hp : (0:ℝ)<A := by exact_mod_cast hA
    linarith [hs1lt.2]

end SymplecticPacking.HighDim.ToricPackingStages
