import SymplecticPacking.BranchSmall.TransportControl

/-!
# The transport ends on the graph `X₁` (supporting `transport_graph`)

Supplement prop:vtr-transport (a),(e). The transport field `transportField a b T` is, where its
linear problem is uniquely solvable, a solution `V` of `D_z(equations) V_z − T V_W = W`. Along a
trajectory `γ` of the field the function `G(T) = equations(z(T)) − T W(T)` therefore has
derivative `D(equations) ż − W − T Ẇ = W − W = 0`, so `G` is constant; it vanishes at `T = 0`
when the trajectory starts over the curve, hence at `T = 1`: `W(1) = equations(z(1))`.

* `transportField_existsUnique` (prop:vtr-transport (b),(c) with lem:vtr-form (c): on `goodSet`
  the Jacobian is surjective, so `R_T(v) = jacobian z v₁ − T v₂` is surjective, and `Ω_b` is
  Kähler for `0 < b < 1/2`, so it is nondegenerate on the complex subspace `ker R_T`; hence the
  `Ω_b`-orthogonal lift exists and is unique). This is the linear-algebra core of
  `transportField_contDiffOn` (`TransportControl.lean`).
* `transportField_lin` (proved from it): the field solves the linear constraint.
* `graph_of_trajectory` (proved): the constancy argument above.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology
open OAI.PackingSufficiencySupport.DiagonalQuadrics

variable {q : ℕ}

/-- **Unique solvability of the transport problem on the good set** (prop:vtr-transport (b),(c),
lem:vtr-form (c)). -/
theorem transportField_existsUnique (_a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (T : ℝ) {y : Tot q} (hy : y ∈ goodSet q) :
    ∃! v : Tot q, jacobian y.1 v.1 - (T : ℂ) • v.2 = y.2 ∧
      ∀ k : Tot q, jacobian y.1 k.1 - (T : ℂ) • k.2 = 0 → bundleForm b y v k = 0 := by
  exact transport_existsUnique hb0 hb T hy

/-- On the good set the transport field solves `D_z(equations) V_z − T V_W = W`. -/
theorem transportField_lin (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (T : ℝ) {y : Tot q} (hy : y ∈ goodSet q) :
    jacobian y.1 (transportField a b T y).1 - (T : ℂ) • (transportField a b T y).2 = y.2 := by
  have h := transportField_existsUnique a hb0 hb T hy
  unfold transportField
  split_ifs with h'
  · exact (Explicit.the_spec h').1
  · exact absurd h h'

/-- **A trajectory from the curve ends on the graph** (prop:vtr-transport (a),(e)). -/
theorem graph_of_trajectory (a : Fin q → ℂ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {γ : ℝ → Tot q} (h0 : equations a (γ 0).1 = 0)
    (hγO : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ goodSet q)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt γ (transportField a b s (γ s)) (Icc 0 1) s) :
    (γ 1).2 = equations a (γ 1).1 := by
  set G : ℝ → (Fin q → ℂ) := fun s => equations a (γ s).1 - (s : ℂ) • (γ s).2 with hGdef
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G 0 (Icc 0 1) s := by
    intro s hs
    have h := hγ s hs
    have h1 : HasDerivWithinAt (fun t => (γ t).1) (transportField a b s (γ s)).1 (Icc 0 1) s :=
      (ContinuousLinearMap.fst ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivWithinAt s h
    have h2 : HasDerivWithinAt (fun t => (γ t).2) (transportField a b s (γ s)).2 (Icc 0 1) s :=
      (ContinuousLinearMap.snd ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivWithinAt s h
    have he := ((equations_hasFDerivAt a (γ s).1).restrictScalars ℝ).comp_hasDerivWithinAt s h1
    have hc : HasDerivWithinAt (fun t : ℝ => (t : ℂ)) ((1 : ℝ) : ℂ) (Icc 0 1) s :=
      (hasDerivAt_id s).ofReal_comp.hasDerivWithinAt
    have hm := hc.smul h2
    have hlin := transportField_lin a hb0 hb s (hγO s hs)
    have hsum := he.sub hm
    convert hsum using 1
    · funext t
      rfl
    · rw [ContinuousLinearMap.coe_restrictScalars', Complex.ofReal_one, one_smul, ← sub_sub, hlin,
        sub_self]
  have hcont : ContinuousOn G (Icc 0 1) := fun s hs => (hG s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun s hs => by
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    exact (hG s hsI).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
    1 ⟨zero_le_one, le_rfl⟩
  have h1 : G 1 = 0 := by
    rw [hconst]
    simp only [hGdef, h0, Complex.ofReal_zero, zero_smul, sub_zero]
  have h1' : equations a (γ 1).1 - (γ 1).2 = 0 := by
    simpa only [hGdef, Complex.ofReal_one, one_smul] using h1
  exact (sub_eq_zero.mp h1').symm

end SymplecticPacking.BranchSmall.VT
