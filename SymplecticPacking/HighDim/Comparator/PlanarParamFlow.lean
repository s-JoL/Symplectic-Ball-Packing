import SymplecticPacking.HighDim.Comparator.PlanarJointIntegral
import SymplecticPacking.Return.Flow
import SymplecticPacking.Qhat.Flow

/-!
# Smooth frozen-parameter flows

A parameter is included as a constant coordinate of one compactly supported
vector field. Uniqueness identifies its fibre flow with the specified planar flow.
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Complex Function
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]

/-- Smooth dependence of the specified planar flow on an entire finite-dimensional parameter. -/
theorem compact_param_flow_smooth {W : P → ℝ → ℂ → ℂ}
    (hW : ContDiff ℝ ∞ (fun q : P × (ℝ × ℂ) => W q.1 q.2.1 q.2.2))
    (hcW : HasCompactSupport (fun q : P × (ℝ × ℂ) => W q.1 q.2.1 q.2.2))
    (hgood : ∀ p, Qhat.GoodField (W p)) :
    ContDiff ℝ ∞ (fun q : P × (ℝ × ℂ) => Qhat.flowOf (W q.1) q.2.1 q.2.2) := by
  let V : ℝ → P × ℂ → P × ℂ := fun t x => (0, W x.1 t x.2)
  let e : (ℝ × (P × ℂ)) ≃ₜ (P × (ℝ × ℂ)) :=
    { toFun := fun q => (q.2.1, (q.1, q.2.2))
      invFun := fun q => (q.2.1, (q.1, q.2.2))
      left_inv := by rintro ⟨t, p, z⟩; rfl
      right_inv := by rintro ⟨p, t, z⟩; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hV : Return.CSField V := by
    constructor
    · exact contDiff_const.prodMk (hW.comp
        (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)))
    · exact (hcW.comp_homeomorph e).comp_left (g := fun z : ℂ => ((0 : P), z)) rfl
  have hfst (p : P) (z : ℂ) (t : ℝ) : (Return.flow V t (p, z)).1 = p := by
    have hd (s : ℝ) : HasDerivAt (fun t => (Return.flow V t (p, z)).1) 0 s := by
      have hh := (ContinuousLinearMap.fst ℝ P ℂ).hasFDerivAt.comp_hasDerivAt s
        (hV.flow_hasDerivAt (p, z) s)
      change HasDerivAt (fun t => (Return.flow V t (p, z)).1) 0 s at hh
      exact hh
    have hh := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    rw [hh, hV.flow_zero]
  have heq (p : P) (z : ℂ) (t : ℝ) : Qhat.flowOf (W p) t z = (Return.flow V t (p, z)).2 := by
    apply (hgood p).flowOf_eq
    constructor
    · change (Return.flow V 0 (p, z)).2 = z
      rw [hV.flow_zero]
    · intro s
      have hd := (ContinuousLinearMap.snd ℝ P ℂ).hasFDerivAt.comp_hasDerivAt s (hV.flow_hasDerivAt (p, z) s)
      change HasDerivAt (fun t => (Return.flow V t (p, z)).2)
        (W (Return.flow V s (p, z)).1 s (Return.flow V s (p, z)).2) s at hd
      rw [hfst p z s] at hd
      exact hd
  have hs : ContDiff ℝ ∞ (fun q : P × (ℝ × ℂ) => (Return.flow V q.2.1 (q.1, q.2.2)).2) :=
    contDiff_snd.comp (hV.flow_smooth.comp
      (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)))
  have he : (fun q : P × (ℝ × ℂ) => Qhat.flowOf (W q.1) q.2.1 q.2.2) =
      (fun q : P × (ℝ × ℂ) => (Return.flow V q.2.1 (q.1, q.2.2)).2) :=
    funext fun q => heq q.1 q.2.2 q.2.1
  rw [he]
  exact hs

end SymplecticPacking.HighDim.PlanarGen

namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Metric
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [CompleteSpace P]

/-- Local parameter dependence, obtained by cutting off only the frozen parameter.
The supplied compact set is a common support in time and space. -/
theorem local_param_flow_smooth {W : P → ℝ → ℂ → ℂ} {U : Set P} (hU : IsOpen U)
    (hW : ContDiffOn ℝ ∞ (fun q : P × (ℝ × ℂ) => W q.1 q.2.1 q.2.2) (U ×ˢ univ))
    (hgood : ∀ p ∈ U, Qhat.GoodField (W p))
    {K : Set (ℝ × ℂ)} (hK : IsCompact K)
    (hsupp : ∀ p ∈ U, ∀ q ∉ K, W p q.1 q.2 = 0) :
    ContDiffOn ℝ ∞ (fun q : P × (ℝ × ℂ) => Qhat.flowOf (W q.1) q.2.1 q.2.2)
      (U ×ˢ univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q.1 hq.1
  let c : ContDiffBump q.1 := ⟨ε/4, ε/2, by positivity, by linarith⟩
  let W' : P → ℝ → ℂ → ℂ := fun p t z => c p • W p t z
  have hcsub : tsupport c ⊆ U := by
    intro p hp
    rw [c.tsupport_eq] at hp
    exact hball (lt_of_le_of_lt (mem_closedBall.mp hp) (by
      change ε/2 < ε
      linarith))
  have hc : ContDiff ℝ ∞ (fun p : P × (ℝ × ℂ) => c p.1) :=
    (c.contDiff (n := ⊤)).comp contDiff_fst
  have hs : ContDiff ℝ ∞ (fun p : P × (ℝ × ℂ) => W' p.1 p.2.1 p.2.2) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 ∈ U
    · exact hc.contDiffAt.smul (hW.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
    · have hpc : p.1 ∉ tsupport c := fun h => hp (hcsub h)
      have hz := continuous_fst.continuousAt.preimage_mem_nhds
        (notMem_tsupport_iff_eventuallyEq.mp hpc)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with r hr
      change c r.1 • W r.1 r.2.1 r.2.2 = (0 : ℂ)
      simp only [Pi.zero_apply] at hr
      rw [hr, zero_smul]
  have hcomp : HasCompactSupport (fun p : P × (ℝ × ℂ) => W' p.1 p.2.1 p.2.2) := by
    apply HasCompactSupport.intro (c.hasCompactSupport.isCompact.prod hK)
    intro p hp
    by_cases hpc : p.1 ∈ tsupport c
    · have hpK : p.2 ∉ K := fun h => hp ⟨hpc, h⟩
      change c p.1 • W p.1 p.2.1 p.2.2 = 0
      rw [hsupp p.1 (hcsub hpc) p.2 hpK, smul_zero]
    · change c p.1 • W p.1 p.2.1 p.2.2 = 0
      rw [image_eq_zero_of_notMem_tsupport hpc, zero_smul]
  have hgood' (p : P) : Qhat.GoodField (W' p) := by
    refine ⟨hs.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
    · exact HasCompactSupport.intro hK (fun r hr => by
        change c p • W p r.1 r.2 = 0
        by_cases hpc : p ∈ tsupport c
        · rw [hsupp p (hcsub hpc) r hr, smul_zero]
        · rw [image_eq_zero_of_notMem_tsupport hpc, zero_smul])
    · intro t z ht
      change c p • W p t z = 0
      by_cases hpc : p ∈ tsupport c
      · rw [(hgood p (hcsub hpc)).time t z ht, smul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hpc, zero_smul]
  have hf := compact_param_flow_smooth hs hcomp hgood'
  apply hf.contDiffAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ p : P × (ℝ × ℂ) in 𝓝 q, p.1 ∈ closedBall q.1 (ε/4) :=
    continuous_fst.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ (by positivity))
  filter_upwards [hnear] with p hp
  have hfields : W' p.1 = W p.1 := by
    funext t z
    change c p.1 • W p.1 t z = W p.1 t z
    rw [c.one_of_mem_closedBall hp, one_smul]
  rw [hfields]

end SymplecticPacking.HighDim.PlanarGen
