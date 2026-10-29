import SymplecticPacking.BranchSmall.TransportAnalytic

/-!
# A controlled initial transport segment

A local compact extension supplies the ordinary local solution near `T = 0`.
The extension appears only in this existence proof.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Metric
open SymplecticPacking.Return (CSField flow)
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

section generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_initial_segment {V : ℝ → E → E} {O : Set E} (hO : IsOpen O)
    (hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => V p.1 p.2) (univ ×ˢ O))
    (y : E) (hy : y ∈ O) :
    ∃ (δ : ℝ) (γ : ℝ → E), 0 < δ ∧ δ < 1 ∧ ContDiff ℝ ∞ γ ∧ γ 0 = y ∧
      ∀ t ∈ Icc (0 : ℝ) δ, γ t ∈ O ∧ HasDerivAt γ (V t (γ t)) t := by
  obtain ⟨χ, _, _, _, _, _, hW0, hWc, hWe⟩ := exists_smooth_compact_extension
    (f := fun p : ℝ × E => V p.1 p.2)
    (isCompact_singleton : IsCompact {((0 : ℝ), y)}) (isOpen_univ.prod hO)
    (singleton_subset_iff.mpr ⟨mem_univ _, hy⟩) hV
  let W : ℝ → E → E := fun t z => χ (t, z) • V t z
  have hW : CSField W := ⟨hW0, hWc⟩
  let γ : ℝ → E := fun t => flow W t y
  have hγ : ContDiff ℝ ∞ γ := hW.flow_smooth.comp (contDiff_id.prodMk contDiff_const)
  have hγ0 : γ 0 = y := hW.flow_zero y
  have he : (fun p : ℝ × E => W p.1 p.2) =ᶠ[𝓝 (0, y)] fun p => V p.1 p.2 :=
    hWe.filter_mono (nhds_le_nhdsSet (mem_singleton _))
  have htend : Tendsto (fun t => (t, γ t)) (𝓝 (0 : ℝ)) (𝓝 (0, y)) := by
    simpa only [hγ0, id_eq] using (continuous_id.prodMk hγ.continuous).tendsto 0
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), W t (γ t) = V t (γ t) ∧ γ t ∈ O :=
    htend.eventually (he.and ((continuous_snd.tendsto (0, y)).eventually (hO.mem_nhds hy)))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, γ, hδ, (min_le_right _ _).trans_lt (by norm_num), hγ, hγ0, ?_⟩
  intro t ht
  have htε : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hδε
  have hh := hεsub htε
  refine ⟨hh.2, ?_⟩
  have hd := hW.flow_hasDerivAt y t
  rw [hh.1] at hd
  exact hd

end generic
end SymplecticPacking.BranchSmall.VT
