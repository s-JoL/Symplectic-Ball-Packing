import SymplecticPacking.BranchSmall.VectorTransferSpecFlow

/-!
# Gluing of solution segments

Gluing two solution segments at a common endpoint.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def glueTrajectory (δ : ℝ) (f g : ℝ → E) (t : ℝ) : E := if t ≤ δ then f t else g t

theorem glueTrajectory_left {δ t : ℝ} {f g : ℝ → E} (ht : t ≤ δ) :
    glueTrajectory δ f g t = f t := if_pos ht

theorem glueTrajectory_right {δ t : ℝ} {f g : ℝ → E} (hfg : f δ = g δ) (ht : δ ≤ t) :
    glueTrajectory δ f g t = g t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [glueTrajectory_left le_rfl, hfg]
  · exact if_neg (not_le.mpr ht)

theorem glueTrajectory_hasDerivWithinAt {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {V : ℝ → E → E} {f g : ℝ → E} (hfg : f δ = g δ)
    (hf : ∀ t ∈ Icc (0 : ℝ) δ, HasDerivWithinAt f (V t (f t)) (Icc 0 δ) t)
    (hg : ∀ t ∈ Icc δ (1 : ℝ), HasDerivWithinAt g (V t (g t)) (Icc δ 1) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (glueTrajectory δ f g) (V t (glueTrajectory δ f g t)) (Icc 0 1) t := by
  have hfl (t : ℝ) (ht : t ∈ Icc (0 : ℝ) δ) :
      HasDerivWithinAt (glueTrajectory δ f g) (V t (glueTrajectory δ f g t)) (Icc 0 δ) t := by
    rw [glueTrajectory_left ht.2]
    exact (hf t ht).congr_of_mem (fun s hs => glueTrajectory_left hs.2) ht
  have hgr (t : ℝ) (ht : t ∈ Icc δ (1 : ℝ)) :
      HasDerivWithinAt (glueTrajectory δ f g) (V t (glueTrajectory δ f g t)) (Icc δ 1) t := by
    rw [glueTrajectory_right hfg ht.1]
    exact (hg t ht).congr_of_mem (fun s hs => glueTrajectory_right hfg hs.1) ht
  rcases lt_trichotomy t δ with hlt | heq | hgt
  · apply (hfl t ⟨ht.1, hlt.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with s hs hsδ
    exact ⟨hs.1, hsδ.le⟩
  · subst t
    simpa only [Icc_union_Icc_eq_Icc hδ0 hδ1] using
      (hfl δ ⟨hδ0, le_rfl⟩).union (hgr δ ⟨le_rfl, hδ1⟩)
  · apply (hgr t ⟨hgt.le, ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hgt)] with s hs hsδ
    exact ⟨hsδ.le, hs.2⟩

end SymplecticPacking.BranchSmall.VT
