import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.BranchSmall.VectorTransferSpecFlow
import SymplecticPacking.BranchSmall.BundlePotential
import SymplecticPacking.BranchSmall.ReturnControl
import OAI.Geometry.BallPacking.CircleAction.CircleRelativeOneForm

/-!
# The horizontal field on its regular domain

The explicit constraint system has a unique horizontal lift wherever the quadric
Jacobian is surjective. This file proves its smoothness there and supplies the
generic cutoff comparison along a compact trajectory. Complete trajectories and
the radial-tube local control are constructed in `TransportTrajectory.lean`.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open SymplecticPacking.Return (CSField flow plateau)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff

/-! ### Generic: local control from smoothness on an open set and a trajectory inside it -/

section generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local control from a smooth region and a trajectory in it.** If `V` is jointly `C^∞` on
`ℝ × O` (`O` open) and `γ` solves `γ' = V(s, γ)` on `[0,1]` from `y` inside `O`, then `V` is
locally controlled along `y`. -/
theorem localControl_within_of_contDiffOn {V : ℝ → E → E} {O : Set E} (hO : IsOpen O)
    (hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => V p.1 p.2) (univ ×ˢ O))
    {y : E} {γ : ℝ → E} (hγ0 : γ 0 = y) (hγO : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ O)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (V s (γ s)) (Icc 0 1) s) :
    ∃ W O', CSField W ∧ IsOpen O' ∧ O' ⊆ O ∧ AgreesOn V W O' ∧ StaysIn W O' y := by
  have hγc : ContinuousOn γ (Icc 0 1) := fun s hs => (hγ s hs).continuousWithinAt
  set K := γ '' Icc (0 : ℝ) 1 with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hγc
  have hKO : K ⊆ O := by
    rintro _ ⟨s, hs, rfl⟩
    exact hγO s hs
  obtain ⟨U₁, hU₁o, hKU₁, hU₁O, hU₁c⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨U₂, hU₂o, hKU₂, hU₂U₁, -⟩ := exists_open_between_and_isCompact_closure hK hU₁o hKU₁
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU₁o isClosed_closure hU₂U₁
  have hχ0 : ∀ z, z ∉ closure U₁ → χ z = 0 := fun z hz => by
    have : z ∉ Function.support χ := by
      rw [hχs]; exact fun h => hz (subset_closure h)
    exact Function.notMem_support.mp this
  have hχone : ∀ z ∈ U₂, χ z = 1 := fun z hz => (hχ1 z).1 (subset_closure hz)
  set ψ : ℝ → ℝ := plateau (-1) 0 1 2 with hψdef
  have hψ : ContDiff ℝ ∞ ψ := SymplecticPacking.Return.plateau_contDiff _ _ _ _
  have hψone : ∀ s ∈ Icc (0 : ℝ) 1, ψ s = 1 := fun s hs =>
    SymplecticPacking.Return.plateau_eq_one (by norm_num) (by norm_num) hs.1 hs.2
  let W : ℝ → E → E := fun s z => (ψ s * χ z) • V s z
  have hWV : AgreesOn V W U₂ := fun s hs z hz => by
    simp only [W, hψone s hs, hχone z hz, mul_one, one_smul]
  have hWcs : CSField W := by
    refine ⟨?_, ?_⟩
    · rw [contDiff_iff_contDiffAt]
      intro p
      by_cases hp : p.2 ∈ O
      · have hVat : ContDiffAt ℝ ∞ (fun p : ℝ × E => V p.1 p.2) p :=
          hV.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ _, hp⟩)
        have hs : ContDiffAt ℝ ∞ (fun p : ℝ × E => ψ p.1 * χ p.2) p :=
          ((hψ.comp contDiff_fst).mul (hχ.comp contDiff_snd)).contDiffAt
        exact hs.smul hVat
      · have hp' : p.2 ∉ closure U₁ := fun h => hp (hU₁O h)
        apply SymplecticPacking.Return.contDiffAt_of_eventually_zero
        have hev : ∀ᶠ p' : ℝ × E in 𝓝 p, p'.2 ∈ (closure U₁)ᶜ :=
          continuous_snd.continuousAt.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hp')
        filter_upwards [hev] with p' hp''
        simp only [W, hχ0 p'.2 hp'', mul_zero, zero_smul, Pi.zero_apply]
    · apply HasCompactSupport.intro (isCompact_Icc.prod hU₁c)
      intro p hp
      simp only [mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hψ0 : ψ p.1 = 0 := by
          simp only [mem_Icc, not_and_or, not_le] at hp
          rcases hp with hp | hp
          · exact SymplecticPacking.Return.plateau_eq_zero_left (by norm_num) hp.le
          · exact SymplecticPacking.Return.plateau_eq_zero_right (by norm_num) hp.le
        simp only [W, hψ0, zero_mul, zero_smul]
      · simp only [W, hχ0 p.2 hp, mul_zero, zero_smul]
  refine ⟨W, U₂, hWcs, hU₂o,
    (fun z hz => hU₁O (subset_closure (hU₂U₁ (subset_closure hz)))), hWV, ?_⟩
  -- the cutoff flow follows `γ` on `[0,1]`
  obtain ⟨Kl, hKl⟩ := hWcs.lipschitz_slice
  have hflow_cont : Continuous (fun s => flow W s y) :=
    continuous_iff_continuousAt.2 fun t => (hWcs.flow_hasDerivAt y t).continuousAt
  have heq : EqOn (fun s => flow W s y) γ (Icc 0 1) := by
    apply ODE_solution_unique_of_mem_Icc_right (v := W) (s := fun _ => univ) (K := Kl)
    · intro t _
      exact (hKl t).lipschitzOnWith
    · exact hflow_cont.continuousOn
    · intro t _
      exact (hWcs.flow_hasDerivAt y t).hasDerivWithinAt
    · intro t _; exact mem_univ _
    · exact hγc
    · intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
      have h := hγ t htI
      rw [hWV t htI _ (hKU₂ ⟨t, htI, rfl⟩)] at h
      exact h.mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left htI.1))
    · intro t _; exact mem_univ _
    · change flow W 0 y = γ 0
      rw [hWcs.flow_zero, hγ0]
  intro s hs
  rw [show flow W s y = γ s from heq hs]
  exact hKU₂ ⟨s, hs, rfl⟩


/-- Local control, forgetting only the inclusion of its agreement region in the
original smooth region. -/
theorem localControl_of_contDiffOn {V : ℝ → E → E} {O : Set E} (hO : IsOpen O)
    (hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => V p.1 p.2) (univ ×ˢ O))
    {y : E} {γ : ℝ → E} (hγ0 : γ 0 = y) (hγO : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ O)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (V s (γ s)) (Icc 0 1) s) :
    LocalControl V y := by
  obtain ⟨W, U, hW, hU, _hUO, hVW, hy⟩ :=
    localControl_within_of_contDiffOn hO hV hγ0 hγO hγ
  exact ⟨W, U, hW, hU, hVW, hy⟩

end generic

/-! ### The good set of the transport field -/

variable {q : ℕ}

/-- The open set of `Tot q` over which the Jacobian of `equations` is surjective, in explicit form:
`z₀ ≠ 0` or no `z_j` vanishes, and no two `z_j` vanish. -/
def goodSet (q : ℕ) : Set (Tot q) :=
  {y | (y.1.1 ≠ 0 ∨ ∀ j, y.1.2 j ≠ 0) ∧ ∀ i j, i ≠ j → y.1.2 i ≠ 0 ∨ y.1.2 j ≠ 0}

theorem isOpen_goodSet (q : ℕ) : IsOpen (goodSet q) := by
  have hc0 : Continuous (fun y : Tot q => y.1.1) := continuous_fst.comp continuous_fst
  have hcj : ∀ j, Continuous (fun y : Tot q => y.1.2 j) := fun j =>
    (continuous_apply j).comp (continuous_snd.comp continuous_fst)
  have hne : ∀ j, IsOpen {y : Tot q | y.1.2 j ≠ 0} := fun j =>
    isOpen_ne_fun (hcj j) continuous_const
  have h1 : IsOpen {y : Tot q | y.1.1 ≠ 0 ∨ ∀ j, y.1.2 j ≠ 0} := by
    have he : {y : Tot q | y.1.1 ≠ 0 ∨ ∀ j, y.1.2 j ≠ 0} =
        {y : Tot q | y.1.1 ≠ 0} ∪ ⋂ j, {y : Tot q | y.1.2 j ≠ 0} := by
      ext y; simp only [mem_setOf_eq, mem_union, mem_iInter]
    rw [he]
    exact (isOpen_ne_fun hc0 continuous_const).union (isOpen_iInter_of_finite hne)
  have h2 : IsOpen {y : Tot q | ∀ i j, i ≠ j → y.1.2 i ≠ 0 ∨ y.1.2 j ≠ 0} := by
    have he : {y : Tot q | ∀ i j, i ≠ j → y.1.2 i ≠ 0 ∨ y.1.2 j ≠ 0} =
        ⋂ i, ⋂ j, ({_y : Tot q | i = j} ∪ ({y : Tot q | y.1.2 i ≠ 0} ∪ {y : Tot q | y.1.2 j ≠ 0})) := by
      ext y
      simp only [mem_setOf_eq, mem_iInter, mem_union]
      constructor
      · intro h i j
        by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr (h i j hij)
      · intro h i j hij
        rcases h i j with h' | h'
        · exact absurd h' hij
        · exact h'
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_const.union ((hne i).union (hne j))
  exact h1.inter h2

/-- Points over the curve lie in the good set (`at_most_one_zero`, `base_ne_zero_at_branch`). -/
theorem mem_goodSet_of_mem_locus (m : ℕ) {y : Tot (m + 2)} (hy : y.1 ∈ locus (parameters m)) :
    y ∈ goodSet (m + 2) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · by_cases h : ∀ j, y.1.2 j ≠ 0
    · exact Or.inr h
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      exact Or.inl (base_ne_zero_at_branch (parameters_nonzero m).out hy hj)
  · by_contra h
    push_neg at h
    exact hij (at_most_one_zero (parameters_injective m).out hy h.1 h.2)

/-! ### Explicit horizontal linear system -/

theorem goodSet_jacobian_surjective {y : Tot q} (hy : y ∈ goodSet q) :
    Function.Surjective (jacobian y.1) := by
  classical
  by_cases hw : ∀ j, y.1.2 j ≠ 0
  · intro u
    refine ⟨(0, fun j => u j / (2 * y.1.2 j)), ?_⟩
    ext j
    simp only [jacobian_apply, mul_zero, sub_zero]
    exact mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (hw j))
  · push_neg at hw
    obtain ⟨i, hi⟩ := hw
    have ht : y.1.1 ≠ 0 := hy.1.resolve_right (fun h => h i hi)
    intro u
    let v : ℂ := -u i / (2 * y.1.1)
    refine ⟨(v, fun j => if j = i then 0 else (u j + 2 * y.1.1 * v) / (2 * y.1.2 j)), ?_⟩
    have hv : 2 * y.1.1 * v = -u i := mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ht)
    ext j
    simp only [jacobian_apply]
    by_cases hji : j = i
    · subst j
      simp only [hi, mul_zero, zero_mul, zero_sub, hv, neg_neg]
    · have hj : y.1.2 j ≠ 0 := (hy.2 j i hji).resolve_right (fun h => h hi)
      rw [ite_eq_right hji, mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hj), add_sub_cancel_right]

def transportConstraint (T : ℝ) (y : Tot q) : Tot q →L[ℝ] (Fin q → ℂ) :=
  (realJacobian y.1).comp (ContinuousLinearMap.fst ℝ _ _) -
    T • ContinuousLinearMap.snd ℝ _ _

@[simp] theorem transportConstraint_apply (T : ℝ) (y v : Tot q) :
    transportConstraint T y v = jacobian y.1 v.1 - (T : ℂ) • v.2 := by
  simp only [transportConstraint, sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, realJacobian,
    ContinuousLinearMap.coe_restrictScalars']
  rfl

theorem transportConstraint_surjective (T : ℝ) {y : Tot q} (hy : y ∈ goodSet q) :
    Function.Surjective (transportConstraint T y) := by
  intro u
  obtain ⟨v, hv⟩ := goodSet_jacobian_surjective hy u
  refine ⟨(v, 0), ?_⟩
  simp only [transportConstraint_apply, hv, smul_zero, sub_zero]

theorem transportConstraint_I (T : ℝ) (y v : Tot q) :
    transportConstraint T y (Complex.I • v) = Complex.I • transportConstraint T y v := by
  simp only [transportConstraint_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub]
  rw [smul_comm (T : ℂ) Complex.I]

theorem transport_kernel_nondegenerate {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (T : ℝ) (y : Tot q) (v : Tot q) (hv : transportConstraint T y v = 0)
    (horth : ∀ w, transportConstraint T y w = 0 → bundleForm b y v w = 0) : v = 0 := by
  by_contra hn
  have hI : transportConstraint T y (Complex.I • v) = 0 := by
    rw [transportConstraint_I, hv, smul_zero]
  have hp := bundleForm_pos hb0 hb y v hn
  rw [horth _ hI] at hp
  exact lt_irrefl _ hp

theorem transportSystem_invertible {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (T : ℝ) {y : Tot q} (hy : y ∈ goodSet q) :
    (horizontalSystem (bundleForm b y) (transportConstraint T y)).IsInvertible :=
  horizontalSystem_isInvertible (transportConstraint_surjective T hy)
    (transport_kernel_nondegenerate hb0 hb T y)

theorem transport_existsUnique {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (T : ℝ) {y : Tot q} (hy : y ∈ goodSet q) :
    ∃! v : Tot q, jacobian y.1 v.1 - (T : ℂ) • v.2 = y.2 ∧
      ∀ k : Tot q, jacobian y.1 k.1 - (T : ℂ) • k.2 = 0 → bundleForm b y v k = 0 := by
  let v := symplecticHorizontalLift (bundleForm b y) (transportConstraint T y) y.2
  have hi := transportSystem_invertible hb0 hb T hy
  have hv : transportConstraint T y v = y.2 := symplecticHorizontalLift_projects hi _
  have hvo : ∀ k, transportConstraint T y k = 0 → bundleForm b y v k = 0 :=
    fun k hk => symplecticHorizontalLift_orthogonal hi y.2 hk
  refine ⟨v, ⟨by simpa only [transportConstraint_apply] using hv,
    fun k hk => hvo k (by simpa only [transportConstraint_apply] using hk)⟩, ?_⟩
  intro w hw
  have hw' : transportConstraint T y w = y.2 := by simpa only [transportConstraint_apply] using hw.1
  apply sub_eq_zero.mp
  apply transport_kernel_nondegenerate hb0 hb T y (w - v)
  · rw [map_sub, hw', hv, sub_self]
  · intro k hk
    rw [map_sub, sub_apply, hw.2 k (by simpa only [transportConstraint_apply] using hk), hvo k hk, sub_self]

/-! ### Smoothness of the horizontal field -/

/-- **Smoothness of the transport field on the good set** (prop:vtr-transport (b),(c), with
lem:vtr-form (c)). For `0 < b < 1/2`, `Ω_b = bundleForm b` is Kähler on `Tot q`; where the Jacobian
is surjective, `R_T(v) = jacobian z v₁ − T v₂` is surjective for every real `T`, its kernel is a
complex subspace on which `Ω_b` is nondegenerate, so the linear problem defining `transportField`
has a unique solution `(a⁻¹ J* S⁻¹ W, −T B⁻¹ S⁻¹ W)` depending smoothly on `(T, y)`. -/
theorem transportField_contDiffOn (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Tot q => transportField a b p.1 p.2) (univ ×ˢ goodSet q) := by
  have hΩ : ContDiff ℝ ∞ (fun p : ℝ × Tot q => bundleForm b p.2) :=
    ddcForm_family_contDiff (Φ := fun _ : ℝ => bundlePot (q := q) b)
      ((bundlePot_contDiff b).comp contDiff_snd)
  have hA : ContDiff ℝ ∞ (fun p : ℝ × Tot q => transportConstraint p.1 p.2) := by
    unfold transportConstraint
    exact ((realJacobian_contDiff.comp contDiff_snd.fst).clm_comp contDiff_const).sub
      (contDiff_fst.smul contDiff_const)
  have hL : ContDiffOn ℝ ∞ (fun p : ℝ × Tot q =>
      symplecticHorizontalLift (bundleForm b p.2) (transportConstraint p.1 p.2) p.2.2)
      (univ ×ˢ goodSet q) := by
    intro p hp
    exact ((symplecticHorizontalLift_contDiffAt hΩ.contDiffAt hA.contDiffAt
      (transportSystem_invertible hb0 hb p.1 hp.2)).clm_apply
        (contDiff_snd.snd.contDiffAt)).contDiffWithinAt
  apply hL.congr
  intro p hp
  have hu := transport_existsUnique hb0 hb p.1 hp.2
  unfold transportField
  rw [dif_pos hu]
  apply hu.unique (SymplecticPacking.Explicit.the_spec hu)
  have hi := transportSystem_invertible hb0 hb p.1 hp.2
  exact ⟨by simpa only [transportConstraint_apply] using symplecticHorizontalLift_projects hi p.2.2,
    fun k hk => symplecticHorizontalLift_orthogonal hi p.2.2
      (by simpa only [transportConstraint_apply] using hk)⟩


end SymplecticPacking.BranchSmall.VT
