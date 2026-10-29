import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.Return.Flow

/-!
# Flows on `[0,1]` by comparison with compactly supported fields
(supporting `vectorTransfer_spec`, supplement prop:vtr-transport (e), prop:vtr-return (c))

`flowI V t₀ y t` (`VectorTransfer.lean`) is the definite description of the unique solution of
`u' = V(s, u)` on `[0,1]`. The fields `transportField`, `returnField` are only smooth on an open
region `O`; the analytic input of the supplement is that they agree there with a compactly
supported smooth field `W` (a cutoff) whose trajectories from the relevant initial points stay
in `O` for `s ∈ [0,1]`. This file proves the generic consequences:

* `flowI V 0 y t = flow W (clamp t) y` (existence and uniqueness of the `[0,1]`-solution of `V`,
  the uniqueness argument being a first-exit argument: a `V`-solution agrees with the
  `W`-trajectory as long as it stays in `O`, and the agreement set is open-closed);
* the same near `y` (the staying condition is open), hence `y ↦ flowI V 0 y 1` is `C^∞` at `y`;
* the backward flow `flowInv W 1` is a continuous left inverse;
* the time-reversed versions for `flowI V 1 z 0` (via `revField V s z = −V(1 − s) z`).
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open SymplecticPacking.Return (CSField flow flowInv)
open scoped ContDiff

section compare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The clamp `s ↦ max 0 (min 1 s)` onto `[0,1]`. -/
def clampI (s : ℝ) : ℝ := max 0 (min 1 s)

theorem clampI_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clampI s = s := by
  unfold clampI
  rw [min_eq_right hs.2, max_eq_right hs.1]

theorem clampI_mem (s : ℝ) : clampI s ∈ Icc (0 : ℝ) 1 := by
  unfold clampI
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clampI_clampI (s : ℝ) : clampI (clampI s) = clampI s := clampI_of_mem (clampI_mem s)

theorem clampI_one_sub (s : ℝ) : clampI (1 - s) = 1 - clampI s := by
  unfold clampI
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- `V` and `W` agree on `[0,1] × O`. -/
def AgreesOn (V W : ℝ → E → E) (O : Set E) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ O, V s z = W s z

/-- The `W`-trajectory of `y` stays in `O` for `s ∈ [0,1]`. -/
def StaysIn (W : ℝ → E → E) (O : Set E) (y : E) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, flow W s y ∈ O

variable [CompleteSpace E] {V W : ℝ → E → E} {O : Set E}

theorem isSolI_flow (hW : CSField W) (hVW : AgreesOn V W O) {y : E} (hy : StaysIn W O y) :
    IsSolI V 0 y (fun s => flow W (clampI s) y) := by
  refine ⟨?_, ?_, ?_⟩
  · change flow W (clampI 0) y = y
    rw [clampI_of_mem ⟨le_rfl, zero_le_one⟩]
    exact hW.flow_zero y
  · intro s
    change flow W (clampI s) y = flow W (clampI (clampI s)) y
    rw [clampI_clampI]
  · intro s hs
    have hd := (hW.flow_hasDerivAt y s).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    have hval : V s (flow W (clampI s) y) = W s (flow W s y) := by
      rw [clampI_of_mem hs]
      exact hVW s hs _ (hy s hs)
    rw [hval]
    exact hd.congr_of_mem (fun t ht => by simp only [clampI_of_mem ht]) hs

theorem isSolI_unique (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn V W O) {y : E}
    (hy : StaysIn W O y) {v : ℝ → E} (hv : IsSolI V 0 y v) (s : ℝ) :
    v s = flow W (clampI s) y := by
  obtain ⟨hv0, hvc, hvd⟩ := hv
  obtain ⟨K, hK⟩ := hW.lipschitz_slice
  let u : ℝ → E := fun t => flow W t y
  have hu : ∀ t, HasDerivAt u (W t (u t)) t := fun t => hW.flow_hasDerivAt y t
  have hvcont : ContinuousOn v (Icc 0 1) := fun t ht => (hvd t ht).continuousWithinAt
  have hucont : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have hsub : Icc (0 : ℝ) 1 ⊆ {t | v t = u t} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · have h := (hvcont.prodMk hucont.continuousOn).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_diagonal (X := E))
      convert h using 1
      ext t
      simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_diagonal_iff]
      exact and_comm
    · change v 0 = flow W 0 y
      rw [hv0, hW.flow_zero]
    · rintro x ⟨hxe, hx0, hx1⟩
      have hxe : v x = u x := hxe
      have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx1.le⟩
      have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[≥] x :=
        mem_of_superset (Icc_mem_nhdsGE hx1) (Icc_subset_Icc_left hx0)
      have hvO : v ⁻¹' O ∈ 𝓝[≥] x := by
        have hc : ContinuousWithinAt v (Ici x) x :=
          (hvcont x hxI).mono_of_mem_nhdsWithin hIcc
        apply hc.preimage_mem_nhdsWithin
        rw [hxe]
        exact hO.mem_nhds (hy x hxI)
      have huO : u ⁻¹' O ∈ 𝓝[≥] x :=
        (hucont.continuousAt.continuousWithinAt).preimage_mem_nhdsWithin
          (hO.mem_nhds (hy x hxI))
      have hP : (v ⁻¹' O ∩ u ⁻¹' O) ∩ Ico x 1 ∈ 𝓝[≥] x :=
        inter_mem (inter_mem hvO huO) (Ico_mem_nhdsGE hx1)
      obtain ⟨c, hc, hcP⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hP
      have hxc : x < c := hc
      set d := min ((x + c) / 2) ((x + 1) / 2) with hd
      have hxd : x < d := by rw [hd]; exact lt_min (by linarith) (by linarith)
      have hdc : d < c := by rw [hd]; exact (min_le_left _ _).trans_lt (by linarith)
      have hd1 : d ≤ 1 := by rw [hd]; exact (min_le_right _ _).trans (by linarith)
      have hIP : ∀ t ∈ Ico x d, v t ∈ O ∧ u t ∈ O ∧ t ∈ Ico x 1 := fun t ht => by
        have := hcP ⟨ht.1, ht.2.trans hdc⟩
        exact ⟨this.1.1, this.1.2, this.2⟩
      have heq : EqOn v u (Icc x d) := by
        apply ODE_solution_unique_of_mem_Icc_right (v := W) (s := fun _ => univ) (K := K)
        · intro t _
          exact (hK t).lipschitzOnWith
        · exact hvcont.mono (Icc_subset_Icc hx0 hd1)
        · intro t ht
          obtain ⟨hvt, -, htx, ht1⟩ := hIP t ht
          have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hx0.trans htx, ht1.le⟩
          have h := hvd t htI
          rw [hVW t htI _ hvt] at h
          exact h.mono_of_mem_nhdsWithin
            (mem_of_superset (Icc_mem_nhdsGE ht1) (Icc_subset_Icc_left htI.1))
        · intro t _; exact mem_univ _
        · exact hucont.continuousOn
        · intro t _; exact (hu t).hasDerivWithinAt
        · intro t _; exact mem_univ _
        · exact hxe
      exact mem_of_superset (Ioo_mem_nhdsGT hxd) fun t ht => heq ⟨ht.1.le, ht.2.le⟩
  have hc : v s = v (clampI s) := hvc s
  rw [hc]
  exact hsub (clampI_mem s)

theorem existsUnique_isSolI (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn V W O) {y : E}
    (hy : StaysIn W O y) : ∃! u : ℝ → E, IsSolI V 0 y u :=
  ⟨_, isSolI_flow hW hVW hy, fun v hv => funext fun s => isSolI_unique hW hO hVW hy hv s⟩

theorem flowI_eq_flow (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn V W O) {y : E}
    (hy : StaysIn W O y) (t : ℝ) : flowI V 0 y t = flow W (clampI t) y :=
  flowI_eq (existsUnique_isSolI hW hO hVW hy) (isSolI_flow hW hVW hy) t

theorem flowI_one_eq_flow (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn V W O) {y : E}
    (hy : StaysIn W O y) : flowI V 0 y 1 = flow W 1 y := by
  rw [flowI_eq_flow hW hO hVW hy, clampI_of_mem ⟨zero_le_one, le_rfl⟩]

variable [FiniteDimensional ℝ E]

/-- Staying in an open set is an open condition on the initial point. -/
theorem staysIn_eventually (hW : CSField W) (hO : IsOpen O) {y₀ : E} (hy : StaysIn W O y₀) :
    ∀ᶠ y in 𝓝 y₀, StaysIn W O y := by
  have hcont : Continuous (fun p : E × ℝ => flow W p.2 p.1) :=
    hW.flow_smooth.continuous.comp continuous_swap
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro s hs
  exact hcont.continuousAt.preimage_mem_nhds (hO.mem_nhds (hy s hs))

/-- **Smoothness of the time-one map.** -/
theorem flowI_one_contDiffAt (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn V W O)
    {y₀ : E} (hy : StaysIn W O y₀) : ContDiffAt ℝ ∞ (fun y => flowI V 0 y 1) y₀ := by
  apply (hW.flow_slice_smooth 1).contDiffAt.congr_of_eventuallyEq
  filter_upwards [staysIn_eventually hW hO hy] with y hy'
  exact flowI_one_eq_flow hW hO hVW hy'

/-! ### Time reversal -/

/-- The reversed field `s, z ↦ −V(1 − s, z)`. -/
def revField (V : ℝ → E → E) (s : ℝ) (z : E) : E := -V (1 - s) z

theorem revField_revField (V : ℝ → E → E) : revField (revField V) = V := by
  funext s z
  simp only [revField, sub_sub_cancel, neg_neg]

theorem isSolI_rev {V : ℝ → E → E} {t₀ : ℝ} {z : E} {u : ℝ → E} (hu : IsSolI V t₀ z u) :
    IsSolI (revField V) (1 - t₀) z (fun s => u (1 - s)) := by
  obtain ⟨hu0, huc, hud⟩ := hu
  have huc' : ∀ s, u s = u (clampI s) := huc
  refine ⟨?_, ?_, ?_⟩
  · show u (1 - (1 - t₀)) = z
    rw [sub_sub_cancel, hu0]
  · intro s
    change u (1 - s) = u (1 - clampI s)
    rw [huc' (1 - s), clampI_one_sub, ← clampI_of_mem (s := 1 - clampI s), clampI_one_sub,
      clampI_clampI]
    have := clampI_mem s
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · intro s hs
    have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hg : HasDerivWithinAt (fun s : ℝ => 1 - s) (-1) (Icc 0 1) s :=
      ((hasDerivAt_id s).const_sub 1).hasDerivWithinAt
    have hmaps : MapsTo (fun s : ℝ => 1 - s) (Icc 0 1) (Icc 0 1) := fun t ht =>
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := (hud (1 - s) hs').scomp s hg hmaps
    simpa only [revField, neg_smul, one_smul, Function.comp_def] using h

/-- `flowI V 1 z 0 = flowI (revField V) 0 z 1` whenever the reversed problem is uniquely
solvable. -/
theorem flowI_back_eq (V : ℝ → E → E) {z : E}
    (h : ∃! w : ℝ → E, IsSolI (revField V) 0 z w) : flowI V 1 z 0 = flowI (revField V) 0 z 1 := by
  obtain ⟨w, hw, hwu⟩ := h
  have hV : IsSolI V 1 z (fun s => w (1 - s)) := by
    have := isSolI_rev hw
    rw [revField_revField, sub_zero] at this
    exact this
  have hex : ∃! u : ℝ → E, IsSolI V 1 z u := by
    refine ⟨_, hV, fun u hu => funext fun s => ?_⟩
    have h1 := hwu _ (by
      have := isSolI_rev hu
      rw [sub_self] at this
      exact this)
    have := congrFun h1 (1 - s)
    simpa only [sub_sub_cancel] using this
  rw [flowI_eq hex hV 0, flowI_eq ⟨w, hw, hwu⟩ hw 1, sub_zero]

theorem flowI_back_eq_flow (hW : CSField W) (hO : IsOpen O) (hVW : AgreesOn (revField V) W O)
    {z : E} (hz : StaysIn W O z) : flowI V 1 z 0 = flow W 1 z := by
  rw [flowI_back_eq V (existsUnique_isSolI hW hO hVW hz), flowI_one_eq_flow hW hO hVW hz]

/-- **Smoothness of the backward time-one map.** -/
theorem flowI_back_contDiffAt (hW : CSField W) (hO : IsOpen O)
    (hVW : AgreesOn (revField V) W O) {z₀ : E} (hz : StaysIn W O z₀) :
    ContDiffAt ℝ ∞ (fun z => flowI V 1 z 0) z₀ := by
  apply (hW.flow_slice_smooth 1).contDiffAt.congr_of_eventuallyEq
  filter_upwards [staysIn_eventually hW hO hz] with z hz'
  exact flowI_back_eq_flow hW hO hVW hz'

/-! ### Local control: the per-point analytic input -/

/-- **Local control** of `V` along the trajectory of `y`: a compactly supported smooth field `W`
agreeing with `V` on an open set `O` containing the `W`-trajectory of `y` over `[0,1]` (in the
applications: a cutoff of `V` near the compact trajectory, where `V` is smooth). -/
def LocalControl (V : ℝ → E → E) (y : E) : Prop :=
  ∃ W : ℝ → E → E, ∃ O : Set E, CSField W ∧ IsOpen O ∧ AgreesOn V W O ∧ StaysIn W O y

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem csField_revField (hW : CSField W) : CSField (revField W) := by
  refine ⟨?_, ?_⟩
  · have h := hW.smooth.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd :
      ContDiff ℝ ∞ (fun p : ℝ × E => ((1 : ℝ) - p.1, p.2)))
    exact h.neg
  · have h := (hW.compact.comp_homeomorph
      ((Homeomorph.subLeft (1 : ℝ)).prodCongr (Homeomorph.refl E))).neg
    exact h

theorem flow_revField (hW : CSField W) (y : E) (s : ℝ) :
    flow (revField W) s (flow W 1 y) = flow W (1 - s) y := by
  have hu : SymplecticPacking.Return.IsSolFrom (revField W) 0 (flow W 1 y)
      (fun s => flow W (1 - s) y) := by
    refine ⟨by simp only [sub_zero], fun s => ?_⟩
    have h := (hW.flow_hasDerivAt y (1 - s)).scomp s ((hasDerivAt_id s).const_sub 1)
    simpa only [revField, neg_smul, one_smul, Function.comp_def, id] using h
  exact (csField_revField hW).flowFrom_eq hu s

theorem localControl_rev {y : E} (h : LocalControl V y) :
    LocalControl (revField V) (flowI V 0 y 1) := by
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := h
  refine ⟨revField W, O, (csField_revField hW), hO, fun s hs z hz => ?_, fun s hs => ?_⟩
  · have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simp only [revField, hVW (1 - s) hs' z hz]
  · rw [flowI_one_eq_flow hW hO hVW hy, flow_revField hW]
    exact hy (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- The backward `[0,1]`-flow inverts the forward one. -/
theorem flowI_back_forward {y : E} (h : LocalControl V y) :
    flowI V 1 (flowI V 0 y 1) 0 = y := by
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := h
  have hc := localControl_rev ⟨W, O, hW, hO, hVW, hy⟩
  have hagree : AgreesOn (revField V) (revField W) O := fun s hs z hz => by
    have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simp only [revField, hVW (1 - s) hs' z hz]
  have hst : StaysIn (revField W) O (flowI V 0 y 1) := fun s hs => by
    rw [flowI_one_eq_flow hW hO hVW hy, flow_revField hW]
    exact hy (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [flowI_back_eq_flow (csField_revField hW) hO hagree hst, flowI_one_eq_flow hW hO hVW hy,
    flow_revField hW, sub_self, hW.flow_zero]

/-- **Forward map, smoothness** under local control. -/
theorem flowI_one_contDiffAt_of_control {y : E} (h : LocalControl V y) :
    ContDiffAt ℝ ∞ (fun y => flowI V 0 y 1) y := by
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := h
  exact flowI_one_contDiffAt hW hO hVW hy

/-- **Backward map, smoothness** under local control of the reversed field. -/
theorem flowI_back_contDiffAt_of_control {z : E} (h : LocalControl (revField V) z) :
    ContDiffAt ℝ ∞ (fun z => flowI V 1 z 0) z := by
  obtain ⟨W, O, hW, hO, hVW, hz⟩ := h
  exact flowI_back_contDiffAt hW hO hVW hz

/-- **Forward map, continuous left inverse** (the backward `[0,1]`-flow). -/
theorem flowI_one_ctsLeftInv {S : Set E} (hS : ∀ y ∈ S, LocalControl V y) :
    ∃ g : E → E, ContinuousOn g ((fun y => flowI V 0 y 1) '' S) ∧
      LeftInvOn g (fun y => flowI V 0 y 1) S := by
  refine ⟨fun z => flowI V 1 z 0, ?_, fun y hy => flowI_back_forward (hS y hy)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (flowI_back_contDiffAt_of_control (localControl_rev (hS y hy))).continuousAt
    |>.continuousWithinAt

theorem flowI_back_eq_of_control {z : E} (h : LocalControl (revField V) z) :
    flowI V 1 z 0 = flowI (revField V) 0 z 1 := by
  obtain ⟨W, O, hW, hO, hVW, hz⟩ := h
  exact flowI_back_eq V (existsUnique_isSolI hW hO hVW hz)

/-- **Backward map, continuous left inverse** (the forward `[0,1]`-flow). -/
theorem flowI_back_ctsLeftInv {S : Set E} (hS : ∀ z ∈ S, LocalControl (revField V) z) :
    ∃ g : E → E, ContinuousOn g ((fun z => flowI V 1 z 0) '' S) ∧
      LeftInvOn g (fun z => flowI V 1 z 0) S := by
  have hc : ∀ z ∈ S, LocalControl V (flowI V 1 z 0) := fun z hz => by
    have := localControl_rev (hS z hz)
    rwa [revField_revField, ← flowI_back_eq_of_control (hS z hz)] at this
  refine ⟨fun w => flowI V 0 w 1, ?_, fun z hz => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (flowI_one_contDiffAt_of_control (hc z hz)).continuousAt.continuousWithinAt
  · change flowI V 0 (flowI V 1 z 0) 1 = z
    have h1 := flowI_back_forward (hS z hz)
    have hr := localControl_rev (hS z hz)
    rw [← flowI_back_eq_of_control (hS z hz)] at h1 hr
    rw [flowI_back_eq_of_control hr, revField_revField] at h1
    exact h1

end compare

end SymplecticPacking.BranchSmall.VT
