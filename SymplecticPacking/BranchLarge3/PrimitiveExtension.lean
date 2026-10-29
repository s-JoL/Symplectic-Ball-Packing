import SymplecticPacking.BranchLarge3.OAIOpen
import SymplecticPacking.Explicit

/-!
# Step S3a: explicit smooth extension of the physical primitive

The explicit version of the OpenAI theorem `CubicModel.exists_physicalPrimitive_extension`:
for a compact moment set `P` mapped by `physicalParameter L` into the lower trapezoid, a smooth
family of one-forms on the genus-one base curve that agrees with the physical primitive
(the Fubini–Study connection form of the normal model with area profile
`physicalArea D S c L`) near `P × cubicExhaustion ℓ`.

Paper: supplement `six-model.tex` (prop:sxm-bordered); the extension is by an explicit cut-off of
the physical primitive outside the lower trapezoid (OpenAI §6).

## Construction

Write `ι = TrapezoidWeight A B`, `a ∈ ℝ^ι` for the coefficient vector and `q ∈ ℝ²` for the moment
parameter. The selected weights of the physical primitive are `probability a r(a,q)`, where
`r(a,q)` is the unique root in the closed quadrant of the centred moment equation
`centered a q r = 0`. Across the edges `q₁ = 0`, `q₂ = 0` of the trapezoid we continue `r` by

* `quadInv a q` — the unique quadrant root (definite description), used at `clamp q`;
* `rootExt a q` — *the root of `centered a q · = 0` closest to `quadInv a (clamp q)`*
  (definite description of the unique closest root, defined when it is unique).

On the trapezoid `rootExt = quadInv`, and by the implicit function theorem it is smooth on a
neighbourhood of `{a > 0} × lowerTrapezoid`. The family is then cut off by an explicit product of
`Real.smoothTransition` factors in the coefficient vector and the moment parameter, with three
constants: `β = sup_{x ∈ C} Σ a_i(x)`, the margin `m` of `L·P` from the upper edges, and the width
`δ = (1/2)·sup{δ ≤ m/2 : the δ-thickening of the compact core lies in the smooth locus}`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Filter

namespace PrimExt

/-! ### Local smoothness of the continued root (generic lattice) -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- Implicit-function data at an axis point `r = (0,t)`: a smooth local root `ψ` together with
local uniqueness of roots. -/
theorem axis_local {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hzero : ∃ i, k i = (0,0))
    (he0 : ∃ i, k i = (1,0)) (he1 : ∃ i, k i = (0,1)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ψ : ((ι → ℝ) × Radial.Plane) → Radial.Plane,
      ψ (a, Radial.moment k a (0,t)) = (0,t) ∧
      ContDiffAt ℝ ω ψ (a, Radial.moment k a (0,t)) ∧
      ∀ᶠ v in 𝓝 (((a, Radial.moment k a (0,t)) : (ι → ℝ) × Radial.Plane), ((0,t) : Radial.Plane)),
        Radial.centered k v.1.1 v.1.2 v.2 = 0 ↔ ψ v.1 = v.2 := by
  let q : (ι → ℝ) × Radial.Plane := (a, Radial.moment k a (0,t))
  let r : Radial.Plane := (0,t)
  let F : ((ι → ℝ) × Radial.Plane) × Radial.Plane → Radial.Plane :=
    fun s => Radial.centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ω F := Radial.centered_contDiff_analytic k
  have hpartial : (fderiv ℝ F (q,r)).comp
      (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Radial.Plane) Radial.Plane) =
      Radial.centeredDerivative k a (Radial.moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by simp) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (Radial.centered_hasFDerivAt k a (Radial.moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L
      ContinuousLinearMap.inr ℝ ((ι → ℝ) × Radial.Plane) Radial.Plane).IsInvertible := by
    rw [hpartial]
    exact Radial.centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r) = 0 :=
    Radial.centered_moment (Radial.polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  have cdf : ContDiffAt ℝ ω F (q,r) := hF.contDiffAt
  refine ⟨cdf.implicitFunction (by simp) hinv, cdf.implicitFunction_apply_self (by simp) hinv,
    cdf.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with v hv
  rw [hz] at hv
  exact hv

/-- Implicit-function data at any boundary point of the quadrant. -/
theorem boundary_local {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hzero : ∃ i, k i = (0,0))
    (he0 : ∃ i, k i = (1,0)) (he1 : ∃ i, k i = (0,1)) {r : Radial.Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1 = 0 ∨ r.2 = 0) :
    ∃ ψ : ((ι → ℝ) × Radial.Plane) → Radial.Plane,
      ψ (a, Radial.moment k a r) = r ∧
      ContDiffAt ℝ ω ψ (a, Radial.moment k a r) ∧
      ∀ᶠ v in 𝓝 (((a, Radial.moment k a r) : (ι → ℝ) × Radial.Plane), r),
        Radial.centered k v.1.1 v.1.2 v.2 = 0 ↔ ψ v.1 = v.2 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs | ht
  · change s = 0 at hs
    subst hs
    exact axis_local ha hzero he0 he1 hr.2
  · change t = 0 at ht
    subst ht
    have hzero' : ∃ i, (k i).swap = (0,0) := by
      obtain ⟨i,hi⟩ := hzero
      exact ⟨i, by simp [hi]⟩
    have he0' : ∃ i, (k i).swap = (1,0) := by
      obtain ⟨i,hi⟩ := he1
      exact ⟨i, by simp [hi]⟩
    have he1' : ∃ i, (k i).swap = (0,1) := by
      obtain ⟨i,hi⟩ := he0
      exact ⟨i, by simp [hi]⟩
    obtain ⟨ψ,hψ,hψs,hψe⟩ := axis_local (k := fun i => (k i).swap) ha hzero' he0' he1' hr.1
    have hm : Radial.moment (fun i => (k i).swap) a (0,s) = (Radial.moment k a (s,0)).swap :=
      Radial.moment_swap k a (s,0)
    rw [hm] at hψ hψs hψe
    let S : (ι → ℝ) × Radial.Plane → (ι → ℝ) × Radial.Plane := fun q => (q.1, q.2.swap)
    have hS : ContDiff ℝ ω S := by
      change ContDiff ℝ ω (fun q : (ι → ℝ) × Radial.Plane => (q.1, (q.2.2, q.2.1)))
      fun_prop
    refine ⟨fun q => (ψ (S q)).swap, ?_, ?_, ?_⟩
    · change (ψ (a, (Radial.moment k a (s,0)).swap)).swap = (s,0)
      rw [hψ]
      rfl
    · have hc : ContDiffAt ℝ ω (fun q => ψ (S q)) (a, Radial.moment k a (s,0)) :=
        hψs.comp (a, Radial.moment k a (s,0)) hS.contDiffAt
      exact hc.snd.prodMk hc.fst
    · have hT : Continuous (fun v : ((ι → ℝ) × Radial.Plane) × Radial.Plane =>
          ((v.1.1, v.1.2.swap), v.2.swap)) :=
        (continuous_fst.fst.prodMk (continuous_swap.comp continuous_fst.snd)).prodMk
          (continuous_swap.comp continuous_snd)
      have he := hT.continuousAt (x := (((a, Radial.moment k a (s,0)) :
        (ι → ℝ) × Radial.Plane), ((s,0) : Radial.Plane))) |>.eventually hψe
      filter_upwards [he] with v hv
      change Radial.centered (fun i => (k i).swap) v.1.1 v.1.2.swap v.2.swap = 0 ↔
        ψ (v.1.1, v.1.2.swap) = v.2.swap at hv
      rw [Radial.centered_swap] at hv
      change Radial.centered k v.1.1 v.1.2 v.2 = 0 ↔ (ψ (v.1.1, v.1.2.swap)).swap = v.2
      rw [Prod.swap_eq_iff_eq_swap, ← hv, Prod.swap_eq_iff_eq_swap]
      rfl

end Generic

/-! ### The explicit continued root -/

variable {A B : ℕ}

/-- The coefficient-and-moment space. -/
abbrev Q (A B : ℕ) := (TrapezoidWeight A B → ℝ) × Radial.Plane

/-- Coordinatewise projection onto the closed quadrant (continuous, not smooth). -/
def clamp (p : Radial.Plane) : Radial.Plane := (max p.1 0, max p.2 0)

open Classical in
/-- The unique quadrant solution of the moment equation (definite description). -/
def quadInv (a : TrapezoidWeight A B → ℝ) (p : Radial.Plane) : Radial.Plane :=
  if h : ∃! r : Radial.Plane, (0 ≤ r.1 ∧ 0 ≤ r.2) ∧ Radial.moment Radial.latticeIndex a r = p then
    SymplecticPacking.Explicit.the h else 0

/-- The centre of the continued root: the quadrant inverse at the clamped parameter. -/
def centerPt (a : TrapezoidWeight A B → ℝ) (p : Radial.Plane) : Radial.Plane :=
  quadInv a (clamp p)

/-- The root predicate: `r` is a root of the centred moment equation closest to the centre. -/
def IsClosestRoot (a : TrapezoidWeight A B → ℝ) (p r : Radial.Plane) : Prop :=
  Radial.centered Radial.latticeIndex a p r = 0 ∧
    ∀ r', Radial.centered Radial.latticeIndex a p r' = 0 → dist r (centerPt a p) ≤ dist r' (centerPt a p)

open Classical in
/-- The continued root: the unique root closest to `centerPt a p` (definite description). -/
def rootExt (a : TrapezoidWeight A B → ℝ) (p : Radial.Plane) : Radial.Plane :=
  if h : ∃! r, IsClosestRoot a p r then SymplecticPacking.Explicit.the h else 0

/-- The continued selected weights. -/
def selExt (z : Q A B) : TrapezoidWeight A B → ℝ :=
  fun i => Radial.probability Radial.latticeIndex z.1 (rootExt z.1 z.2) i

theorem clamp_of_nonneg {p : Radial.Plane} (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2) : clamp p = p := by
  unfold clamp
  rw [max_eq_left h1, max_eq_left h2]

theorem continuous_clamp : Continuous clamp := by
  unfold clamp
  fun_prop

theorem quadInv_eq (hA : 0 < A) (hAB : A ≤ B) {a : TrapezoidWeight A B → ℝ} (ha : ∀ i, 0 < a i)
    {p : Radial.Plane} (hp : p ∈ Radial.lowerTrapezoid A B) :
    quadInv a p = Radial.nonnegativeInverse Radial.latticeIndex a p := by
  have hs : (0 ≤ (Radial.nonnegativeInverse Radial.latticeIndex a p).1 ∧
      0 ≤ (Radial.nonnegativeInverse Radial.latticeIndex a p).2) ∧
      Radial.moment Radial.latticeIndex a (Radial.nonnegativeInverse Radial.latticeIndex a p) = p :=
    ⟨Radial.nonnegativeInverse_nonneg _ _ _, Radial.trapezoid_inverse_spec hAB ha hp⟩
  have hu : ∃! r : Radial.Plane, (0 ≤ r.1 ∧ 0 ≤ r.2) ∧ Radial.moment Radial.latticeIndex a r = p :=
    ⟨_, hs, fun r hr => (Radial.nonnegativeInverse_eq_of_moment ha (Radial.lattice_zero A B)
      (Radial.lattice_unit_fst hA hAB) (Radial.lattice_unit_snd hA hAB) hr.1 hr.2).symm⟩
  unfold quadInv
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact SymplecticPacking.Explicit.the_eq hu hs

theorem rootExt_eq {a : TrapezoidWeight A B → ℝ} {p r : Radial.Plane}
    (hr : IsClosestRoot a p r) (hu : ∀ r', Radial.centered Radial.latticeIndex a p r' = 0 →
      dist r' (centerPt a p) ≤ dist r (centerPt a p) → r' = r) :
    rootExt a p = r := by
  have h : ∃! r, IsClosestRoot a p r := ⟨r, hr, fun r' h' => hu r' h'.1 (h'.2 r hr.1)⟩
  unfold rootExt
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact SymplecticPacking.Explicit.the_eq h hr

/-- On the trapezoid the continued root is the quadrant inverse. -/
theorem rootExt_trap (hA : 0 < A) (hAB : A ≤ B) {a : TrapezoidWeight A B → ℝ} (ha : ∀ i, 0 < a i)
    {p : Radial.Plane} (hp : p ∈ Radial.lowerTrapezoid A B) :
    rootExt a p = Radial.nonnegativeInverse Radial.latticeIndex a p := by
  have hc : centerPt a p = Radial.nonnegativeInverse Radial.latticeIndex a p := by
    unfold centerPt
    rw [clamp_of_nonneg hp.1 hp.2.2.1]
    exact quadInv_eq hA hAB ha hp
  have hroot : Radial.centered Radial.latticeIndex a p
      (Radial.nonnegativeInverse Radial.latticeIndex a p) = 0 := by
    have h := Radial.centered_moment (k := Radial.latticeIndex (A := A) (B := B)) (a := a)
      (Radial.polynomial_pos ha (Radial.lattice_zero A B)
        (Radial.nonnegativeInverse_nonneg Radial.latticeIndex a p)).ne'
    rwa [Radial.trapezoid_inverse_spec hAB ha hp] at h
  apply rootExt_eq
  · refine ⟨hroot, fun r' _ => ?_⟩
    rw [hc, dist_self]
    exact dist_nonneg
  · intro r' _ hd
    rw [hc, dist_self] at hd
    exact dist_le_zero.mp hd

/-- The continued selected weights are smooth near every point of `{a > 0} × lowerTrapezoid`. -/
theorem selExt_contDiffAt_near (hA : 0 < A) (hAB : A ≤ B) {a : TrapezoidWeight A B → ℝ}
    (ha : ∀ i, 0 < a i) {p : Radial.Plane} (hp : p ∈ Radial.lowerTrapezoid A B) :
    ∀ᶠ z in 𝓝 ((a,p) : Q A B), ContDiffAt ℝ ∞ (selExt (A := A) (B := B)) z := by
  have hpos : ∀ᶠ z in 𝓝 ((a,p) : Q A B), ∀ i, 0 < z.1 i :=
    (FiniteMoment.positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds ha
  by_cases hb : p.1 = 0 ∨ p.2 = 0
  · -- boundary point: implicit function theorem
    set r0 := Radial.nonnegativeInverse Radial.latticeIndex a p with hr0
    have hr := Radial.nonnegativeInverse_nonneg (Radial.latticeIndex (A := A) (B := B)) a p
    have he : Radial.moment Radial.latticeIndex a r0 = p := Radial.trapezoid_inverse_spec hAB ha hp
    have hz := Radial.moment_zero_coordinates ha (Radial.lattice_zero A B)
      (Radial.lattice_unit_fst hA hAB) (Radial.lattice_unit_snd hA hAB) hr
    have hbr : r0.1 = 0 ∨ r0.2 = 0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    obtain ⟨ψ,hψ,hψs,hψe⟩ := boundary_local ha (Radial.lattice_zero A B)
      (Radial.lattice_unit_fst hA hAB) (Radial.lattice_unit_snd hA hAB) hr hbr
    rw [he] at hψ hψs hψe
    obtain ⟨ε,hε,hball⟩ : ∃ ε > 0, ∀ z : Q A B, dist z (a,p) < ε → ∀ r : Radial.Plane,
        dist r r0 < ε → (Radial.centered Radial.latticeIndex z.1 z.2 r = 0 ↔ ψ z = r) := by
      obtain ⟨ε,hε,h⟩ := Metric.eventually_nhds_iff.mp hψe
      refine ⟨ε,hε,fun z hz r hr => @h (z,r) ?_⟩
      rw [Prod.dist_eq]
      exact max_lt hz hr
    -- the centre tends to `r0`
    have hgood : ∀ᶠ z in 𝓝 ((a,p) : Q A B),
        (∀ i, 0 < z.1 i) ∧ clamp z.2 ∈ Radial.lowerTrapezoid A B := by
      have hc1 : Tendsto (fun z : Q A B => (clamp z.2).1) (𝓝 (a,p)) (𝓝 p.1) := by
        have := ((continuous_clamp.comp continuous_snd).fst).tendsto ((a,p) : Q A B)
        simpa [clamp_of_nonneg hp.1 hp.2.2.1] using this
      have hc2 : Tendsto (fun z : Q A B => (clamp z.2).1 + (clamp z.2).2) (𝓝 (a,p))
          (𝓝 (p.1 + p.2)) := by
        have := (((continuous_clamp.comp continuous_snd).fst).tendsto ((a,p) : Q A B)).add
          (((continuous_clamp.comp continuous_snd).snd).tendsto ((a,p) : Q A B))
        simpa [clamp_of_nonneg hp.1 hp.2.2.1] using this
      filter_upwards [hpos, hc1.eventually_lt tendsto_const_nhds hp.2.1,
        hc2.eventually_lt tendsto_const_nhds hp.2.2.2] with z hz h1 h2
      exact ⟨hz, le_max_right _ _, h1, le_max_right _ _, h2⟩
    have hT : Tendsto (fun z : Q A B => centerPt z.1 z.2) (𝓝 (a,p)) (𝓝 r0) := by
      have hw := (Radial.trapezoid_inverse_contDiffWithinAt hA hAB ha hp).continuousWithinAt
      have hc : Tendsto (fun z : Q A B => (z.1, clamp z.2)) (𝓝 (a,p))
          (𝓝[{q : Q A B | (∀ j, 0 < q.1 j) ∧ q.2 ∈ Radial.lowerTrapezoid A B}] (a,p)) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have := (continuous_fst.prodMk (continuous_clamp.comp continuous_snd)).tendsto
            ((a,p) : Q A B)
          simpa [clamp_of_nonneg hp.1 hp.2.2.1] using this
        · filter_upwards [hgood] with z hz
          exact hz
      apply (hw.tendsto.comp hc).congr'
      filter_upwards [hgood] with z hz
      exact (quadInv_eq hA hAB hz.1 hz.2).symm
    have hψc : Tendsto ψ (𝓝 (a,p)) (𝓝 r0) := by
      have := hψs.continuousAt.tendsto
      rwa [hψ] at this
    have hEq : ∀ᶠ z in 𝓝 ((a,p) : Q A B), rootExt z.1 z.2 = ψ z := by
      have hb1 : ∀ᶠ z in 𝓝 ((a,p) : Q A B), dist z (a,p) < ε := Metric.ball_mem_nhds _ hε
      have hb2 : ∀ᶠ z in 𝓝 ((a,p) : Q A B), dist (ψ z) r0 < ε / 4 :=
        hψc (Metric.ball_mem_nhds _ (by linarith))
      have hb3 : ∀ᶠ z in 𝓝 ((a,p) : Q A B), dist (centerPt z.1 z.2) r0 < ε / 4 :=
        hT (Metric.ball_mem_nhds _ (by linarith))
      filter_upwards [hb1, hb2, hb3] with z hz1 hz2 hz3
      have hroot : Radial.centered Radial.latticeIndex z.1 z.2 (ψ z) = 0 :=
        (hball z hz1 (ψ z) (by linarith)).mpr rfl
      have hnear : ∀ r', dist r' (centerPt z.1 z.2) ≤ dist (ψ z) (centerPt z.1 z.2) →
          dist r' r0 < ε := by
        intro r' hr'
        have h1 := dist_triangle r' (centerPt z.1 z.2) r0
        have h2 := dist_triangle (ψ z) r0 (centerPt z.1 z.2)
        rw [dist_comm r0] at h2
        linarith
      apply rootExt_eq
      · refine ⟨hroot, fun r' hr' => ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        have := (hball z hz1 r' (hnear r' hlt.le)).mp hr'
        rw [this] at hlt
        exact lt_irrefl _ hlt
      · intro r' hr' hd
        exact ((hball z hz1 r' (hnear r' hd)).mp hr').symm
    have hψev : ∀ᶠ z in 𝓝 ((a,p) : Q A B), ContDiffAt ℝ ∞ ψ z := by
      filter_upwards [hψs.eventually (by simp)] with z hz
      exact hz.of_le le_top
    have h0 : 0 < Radial.polynomial Radial.latticeIndex a (ψ (a,p)) := by
      rw [hψ]
      exact Radial.polynomial_pos ha (Radial.lattice_zero A B) hr
    have hc := ContinuousAt.comp (f := fun z : Q A B => (z.1, ψ z)) (x := (a,p))
      (Radial.polynomial_contDiff (Radial.latticeIndex (A := A) (B := B))).continuous.continuousAt
      (continuousAt_fst.prodMk hψs.continuousAt)
    have hPpos := hc.eventually (eventually_gt_nhds h0)
    have hEq' : ∀ᶠ z in 𝓝 ((a,p) : Q A B), ∀ᶠ w in 𝓝 z, rootExt w.1 w.2 = ψ w :=
      hEq.eventually_nhds
    filter_upwards [hEq', hψev, hPpos] with z hz hzs hzp
    have hs : ContDiffAt ℝ ∞ (fun w : Q A B => fun i =>
        Radial.probability Radial.latticeIndex w.1 (ψ w) i) z := by
      rw [contDiffAt_pi]
      intro i
      exact (Radial.probability_contDiffAt Radial.latticeIndex hzp.ne' i).comp z
        (contDiffAt_fst.prodMk hzs)
    apply hs.congr_of_eventuallyEq
    filter_upwards [hz] with w hw
    funext i
    simp only [selExt, hw]
  · -- interior point: the continued root is the quadrant inverse near `(a,p)`
    have hp0 : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0 < p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    let W : Set (Q A B) := {z | (∀ i, 0 < z.1 i) ∧ 0 < z.2.1 ∧ z.2.1 < A ∧ 0 < z.2.2 ∧
      z.2.1 + z.2.2 < B}
    have hW : IsOpen W := (FiniteMoment.positiveCoefficients_isOpen.preimage continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd.fst).inter
        ((isOpen_lt continuous_snd.fst continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd.snd).inter
            (isOpen_lt (continuous_snd.fst.add continuous_snd.snd) continuous_const))))
    have hpW : ((a,p) : Q A B) ∈ W := ⟨ha, hp0, hp.2.1, hp1, hp.2.2.2⟩
    filter_upwards [hW.mem_nhds hpW] with z hz
    have hzt : ∀ w ∈ W, w.2 ∈ Radial.lowerTrapezoid A B :=
      fun w hw => ⟨hw.2.1.le, hw.2.2.1, hw.2.2.2.1.le, hw.2.2.2.2⟩
    have hinv := Radial.nonnegativeInverse_interior_contDiffAt hz.1 (Radial.lattice_zero A B)
      (Radial.lattice_unit_fst hA hAB) (Radial.lattice_unit_snd hA hAB)
      (FiniteMoment.trapezoidWeight_surrounds hAB ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩)
    have hs : ContDiffAt ℝ ∞ (fun w : Q A B => fun i => Radial.probability Radial.latticeIndex w.1
        (Radial.nonnegativeInverse Radial.latticeIndex w.1 w.2) i) z := by
      rw [contDiffAt_pi]
      intro i
      exact (Radial.probability_contDiffAt Radial.latticeIndex
        (Radial.polynomial_pos hz.1 (Radial.lattice_zero A B)
          (Radial.nonnegativeInverse_nonneg _ _ _)).ne' i).comp z (contDiffAt_fst.prodMk hinv)
    apply hs.congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hz] with w hw
    funext i
    simp only [selExt, rootExt_trap hA hAB hw.1 (hzt w hw)]

/-! ### Explicit constants and cut-off -/

/-- The coefficient vector of the normal model at `x`. -/
def aMap (A B D S : ℕ) (x : BaseCurve) : TrapezoidWeight A B → ℝ :=
  fun i => coefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) x

/-- `β = sup_{x ∈ C_ℓ} Σ_i a_i(x)`. -/
def betaC (A B D S ℓ : ℕ) : ℝ :=
  sSup ((fun x => ∑ i, aMap A B D S x i) '' cubicExhaustion ℓ)

/-- `s₁ = sup_{p ∈ P} (L p)₁`. -/
def sOne (L : ℝ) (P : Set (Moments 2)) : ℝ := sSup ((fun p => (physicalParameter L p).1) '' P)

/-- `s₂ = sup_{p ∈ P} ((L p)₁ + (L p)₂)`. -/
def sTwo (L : ℝ) (P : Set (Moments 2)) : ℝ :=
  sSup ((fun p => (physicalParameter L p).1 + (physicalParameter L p).2) '' P)

/-- The margin `m = min(A - s₁, B - s₂)/4` of `L·P` from the upper edges of the trapezoid. -/
def margin (A B : ℕ) (L : ℝ) (P : Set (Moments 2)) : ℝ :=
  min ((A : ℝ) - sOne L P) ((B : ℝ) - sTwo L P) / 4

/-- The compact core `[1/2, β+1]^ι × {q ≥ 0, q₁ ≤ A - m, q₁ + q₂ ≤ B - m}`. -/
def core (A B : ℕ) (β m : ℝ) : Set (Q A B) :=
  (Set.pi univ fun _ => Icc (1/2 : ℝ) (β + 1)) ×ˢ
    ((Icc (0 : ℝ) B ×ˢ Icc (0 : ℝ) B) ∩ {q | q.1 ≤ A - m ∧ q.1 + q.2 ≤ B - m})

/-- The smooth locus of the continued selected weights. -/
def goodSet (A B : ℕ) : Set (Q A B) := interior {z | ContDiffAt ℝ ∞ (selExt (A := A) (B := B)) z}

/-- The admissible widths. -/
def widthSet (A B : ℕ) (β m : ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ ≤ m / 2 ∧ Metric.cthickening δ (core A B β m) ⊆ goodSet A B}

/-- The extension width `δ = (1/2) sup widthSet`. -/
def width (A B : ℕ) (β m : ℝ) : ℝ := sSup (widthSet A B β m) / 2

/-- The explicit cut-off. -/
def cutoff (A B : ℕ) (β m δ : ℝ) (z : Q A B) : ℝ :=
  (∏ i, Real.smoothTransition (2 * (β + 1 - z.1 i))) *
    Real.smoothTransition (2 + 2 * z.2.1 / δ) * Real.smoothTransition (2 + 2 * z.2.2 / δ) *
    Real.smoothTransition ((A - 2 * m - z.2.1) / m) *
    Real.smoothTransition ((B - 2 * m - z.2.1 - z.2.2) / m)

/-- The cut-off continued selected weights. -/
def extSel (A B : ℕ) (β m δ : ℝ) (z : Q A B) : TrapezoidWeight A B → ℝ :=
  cutoff A B β m δ z • selExt z

/-- The extended primitive family in the moment parameter `q = L p`. -/
def extFamily (A B D S : ℕ) (c β m δ : ℝ) (q : Radial.Plane) : ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i, extSel A B β m δ (aMap A B D S x, q) i •
    weightedFSPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c x

/-! ### Properties of the cut-off -/

section Cutoff

variable {β m δ : ℝ}

/-- The closed region outside which the cut-off vanishes. -/
def region (A B : ℕ) (β m δ : ℝ) : Set (Q A B) :=
  {z | (∀ i, z.1 i ≤ β + 1) ∧ -δ ≤ z.2.1 ∧ -δ ≤ z.2.2 ∧ z.2.1 ≤ A - 2 * m ∧
    z.2.1 + z.2.2 ≤ B - 2 * m}

theorem region_closed : IsClosed (region A B β m δ) := by
  have h1 : IsClosed {z : Q A B | ∀ i, z.1 i ≤ β + 1} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).comp continuous_fst)
      continuous_const
  exact h1.inter ((isClosed_le continuous_const continuous_snd.fst).inter
    ((isClosed_le continuous_const continuous_snd.snd).inter
      ((isClosed_le continuous_snd.fst continuous_const).inter
        (isClosed_le (continuous_snd.fst.add continuous_snd.snd) continuous_const))))

theorem pos_of_smoothTransition_ne {x : ℝ} (h : Real.smoothTransition x ≠ 0) : 0 < x := by
  by_contra hx
  exact h (Real.smoothTransition.zero_of_nonpos (not_lt.mp hx))

theorem mem_region_of_cutoff_ne (hδ : 0 < δ) (hm : 0 < m) {z : Q A B}
    (h : cutoff A B β m δ z ≠ 0) : z ∈ region A B β m δ := by
  unfold cutoff at h
  simp only [mul_ne_zero_iff] at h
  obtain ⟨⟨⟨⟨h0,h1⟩,h2⟩,h3⟩,h4⟩ := h
  have h0' := Finset.prod_ne_zero_iff.mp h0
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · have := pos_of_smoothTransition_ne (h0' i (Finset.mem_univ i))
    linarith
  · have h := pos_of_smoothTransition_ne h1
    rw [mul_div_assoc] at h
    have h' : -1 < z.2.1 / δ := by linarith
    rw [lt_div_iff₀ hδ] at h'
    linarith
  · have h := pos_of_smoothTransition_ne h2
    rw [mul_div_assoc] at h
    have h' : -1 < z.2.2 / δ := by linarith
    rw [lt_div_iff₀ hδ] at h'
    linarith
  · have h := (div_pos_iff_of_pos_right hm).mp (pos_of_smoothTransition_ne h3)
    linarith
  · have h := (div_pos_iff_of_pos_right hm).mp (pos_of_smoothTransition_ne h4)
    linarith

theorem cutoff_eq_one (hδ : 0 < δ) (hm : 0 < m) {z : Q A B} (ha : ∀ i, z.1 i ≤ β + 1/2)
    (h1 : -(δ/2) ≤ z.2.1) (h2 : -(δ/2) ≤ z.2.2) (h3 : z.2.1 ≤ A - 3 * m)
    (h4 : z.2.1 + z.2.2 ≤ B - 3 * m) : cutoff A B β m δ z = 1 := by
  unfold cutoff
  have e0 : (∏ i, Real.smoothTransition (2 * (β + 1 - z.1 i))) = 1 :=
    Finset.prod_eq_one fun i _ => Real.smoothTransition.one_of_one_le (by linarith [ha i])
  have e1 : Real.smoothTransition (2 + 2 * z.2.1 / δ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have : -(1/2) ≤ z.2.1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : 2 * z.2.1 / δ = 2 * (z.2.1 / δ) := by ring
    rw [e]; linarith
  have e2 : Real.smoothTransition (2 + 2 * z.2.2 / δ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have : -(1/2) ≤ z.2.2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : 2 * z.2.2 / δ = 2 * (z.2.2 / δ) := by ring
    rw [e]; linarith
  have e3 : Real.smoothTransition ((A - 2 * m - z.2.1) / m) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hm]; linarith
  have e4 : Real.smoothTransition ((B - 2 * m - z.2.1 - z.2.2) / m) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hm]; linarith
  rw [e0, e1, e2, e3, e4]
  norm_num

theorem cutoff_contDiff : ContDiff ℝ ∞ (cutoff A B β m δ) := by
  have hT : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  unfold cutoff
  refine ((((contDiff_prod fun i _ => hT.comp ?_).mul (hT.comp ?_)).mul (hT.comp ?_)).mul
    (hT.comp ?_)).mul (hT.comp ?_)
  all_goals fun_prop

theorem clamp_aux {q δ : ℝ} (h : -δ ≤ q) (hδ : 0 ≤ δ) :
    |q - max q 0| ≤ δ ∧ max q 0 ≤ q + δ ∧ 0 ≤ max q 0 := by
  rcases le_total 0 q with h0 | h0
  · rw [max_eq_left h0]
    refine ⟨?_, by linarith, h0⟩
    simp only [sub_self, abs_zero]
    linarith
  · rw [max_eq_right h0]
    refine ⟨?_, by linarith, le_rfl⟩
    rw [sub_zero, abs_of_nonpos h0]
    linarith

/-- Points of the region with `a ≥ 1/2` lie in the `δ`-thickening of the core. -/
theorem mem_cthickening_core (hm : 0 < m) (hmA : m ≤ A) (hAB : A ≤ B) (hδ : 0 ≤ δ)
    (hδm : δ ≤ m / 2) {z : Q A B} (hz : z ∈ region A B β m δ) (ha : ∀ i, 1/2 ≤ z.1 i) :
    z ∈ Metric.cthickening δ (core A B β m) := by
  obtain ⟨hz0, hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨d1, u1, n1⟩ := clamp_aux hz1 hδ
  obtain ⟨d2, u2, n2⟩ := clamp_aux hz2 hδ
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hsum : max z.2.1 0 + max z.2.2 0 ≤ B - m := by linarith
  have hx1 : max z.2.1 0 ≤ A - m := by
    rcases le_total 0 z.2.1 with h0 | h0
    · rw [max_eq_left h0]; linarith
    · rw [max_eq_right h0]; linarith
  apply Metric.mem_cthickening_of_dist_le z (z.1, clamp z.2)
  · refine ⟨fun i _ => ⟨ha i, hz0 i⟩, ⟨⟨n1, ?_⟩, ⟨n2, ?_⟩⟩, hx1, hsum⟩
    · show max z.2.1 0 ≤ (B : ℝ)
      linarith
    · show max z.2.2 0 ≤ (B : ℝ)
      linarith
  · rw [Prod.dist_eq, dist_self, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le hδ (max_le d1 d2)

end Cutoff

/-! ### Smoothness of the extended weights -/

theorem core_compact (β m : ℝ) : IsCompact (core A B β m) := by
  have hq : IsClosed {q : Radial.Plane | q.1 ≤ A - m ∧ q.1 + q.2 ≤ B - m} :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).prod
    ((isCompact_Icc.prod isCompact_Icc).inter_right hq)

theorem core_subset_goodSet (hA : 0 < A) (hAB : A ≤ B) {β m : ℝ} (hm : 0 < m) :
    core A B β m ⊆ goodSet A B := by
  rintro ⟨a,q⟩ ⟨ha, ⟨⟨hq1,hq2⟩, hq3, hq4⟩⟩
  have hapos : ∀ i, 0 < a i := fun i => by
    have := (ha i (mem_univ i)).1
    linarith
  have hqt : q ∈ Radial.lowerTrapezoid A B := ⟨hq1.1, by linarith, hq2.1, by linarith⟩
  exact mem_interior_iff_mem_nhds.mpr (selExt_contDiffAt_near hA hAB hapos hqt)

theorem width_spec (hA : 0 < A) (hAB : A ≤ B) {β m : ℝ} (hm : 0 < m) :
    0 < width A B β m ∧ width A B β m ∈ widthSet A B β m := by
  obtain ⟨δ1, hδ1, hsub⟩ := (core_compact (A := A) (B := B) β m).exists_cthickening_subset_open
    isOpen_interior (core_subset_goodSet hA hAB hm)
  set d := min δ1 (m / 2)
  have hd : d ∈ widthSet A B β m :=
    ⟨le_min hδ1.le (by linarith), min_le_right _ _,
      (Metric.cthickening_mono (min_le_left _ _) _).trans hsub⟩
  have hdpos : 0 < d := lt_min hδ1 (by linarith)
  have hbdd : BddAbove (widthSet A B β m) := ⟨m / 2, fun δ hδ => hδ.2.1⟩
  have hsup : d ≤ sSup (widthSet A B β m) := le_csSup hbdd hd
  have hwpos : 0 < width A B β m := by
    unfold width
    linarith
  refine ⟨hwpos, ?_⟩
  have hlt : width A B β m < sSup (widthSet A B β m) := by
    unfold width
    linarith
  obtain ⟨e, he, hwe⟩ := exists_lt_of_lt_csSup ⟨d, hd⟩ hlt
  exact ⟨hwpos.le, hwe.le.trans he.2.1,
    (Metric.cthickening_mono hwe.le _).trans he.2.2⟩

theorem extSel_contDiffAt (hA : 0 < A) (hAB : A ≤ B) {β m : ℝ} (hm : 0 < m) (hmA : m ≤ A)
    {z : Q A B} (ha : ∀ i, 1/2 ≤ z.1 i) :
    ContDiffAt ℝ ∞ (extSel A B β m (width A B β m)) z := by
  obtain ⟨hδ, hδs⟩ := width_spec (β := β) hA hAB hm
  set δ := width A B β m
  by_cases hz : z ∈ region A B β m δ
  · have hc := mem_cthickening_core hm hmA hAB hδs.1 hδs.2.1 hz ha
    have hs : ContDiffAt ℝ ∞ (selExt (A := A) (B := B)) z := interior_subset (hδs.2.2 hc)
    exact cutoff_contDiff.contDiffAt.smul hs
  · have hev : ∀ᶠ w in 𝓝 z, extSel A B β m δ w = 0 := by
      filter_upwards [region_closed.isOpen_compl.mem_nhds hz] with w hw
      have : cutoff A B β m δ w = 0 := by
        by_contra h
        exact hw (mem_region_of_cutoff_ne hδ hm h)
      simp only [extSel, this, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem aMap_ge (A B D S : ℕ) (x : BaseCurve) (i : TrapezoidWeight A B) : 1 ≤ aMap A B D S x i := by
  dsimp [aMap, coefficientNorm]
  linarith [phaseSq_nonneg (weightedPhaseInclusion (cubicDegree D i) (cubicMarkedOrder S i) x)]

theorem aMap_smooth (A B D S : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞ (aMap A B D S) :=
  contMDiff_pi_space.mpr (fun _ => coefficientNorm_smooth _ _)

theorem extFamily_smooth (hA : 0 < A) (hAB : A ≤ B) (D S : ℕ) (c : ℝ) {β m : ℝ} (hm : 0 < m)
    (hmA : m ≤ A) : SmoothOneFormFamily (extFamily A B D S c β m (width A B β m)) := by
  set a := aMap A B D S
  have ha := aMap_smooth A B D S
  set G := extSel A B β m (width A B β m)
  have hterm (i : TrapezoidWeight A B) : SmoothOneFormFamily
      (fun q : Radial.Plane => fun x => G (a x, q) i •
        weightedFSPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c x) := by
    intro b q hq
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hq.2)
    have hac : ContDiffAt ℝ ∞ (fun z : Radial.Plane × RealModel =>
        a ((extChartAt 𝓘(ℝ,RealModel) b).symm z.2)) q :=
      (ha.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
    have hG : ContDiffAt ℝ ∞ G (a ((extChartAt 𝓘(ℝ,RealModel) b).symm q.2), q.1) :=
      extSel_contDiffAt hA hAB hm hmA (fun j => by
        have := aMap_ge A B D S ((extChartAt 𝓘(ℝ,RealModel) b).symm q.2) j
        change 1/2 ≤ aMap A B D S _ j
        linarith)
    have hgc := ((contDiff_apply ℝ ℝ i).contDiffAt.comp _ hG).comp q (hac.prodMk contDiffAt_fst)
    have hw : SmoothOneFormFamily (fun _ : Radial.Plane =>
        weightedFSPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c) :=
      (weightedFSPrimitive_smooth (cubicDegree D i) (cubicMarkedOrder S i) c).comp
        (contDiff_const (c := (0:ℝ)))
    have hwc := (hw b).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target b)).mem_nhds hq)
    simpa only [chartOneForm_spatial_smul,Function.comp_apply,Pi.smul_def'] using
      (hgc.smul hwc).contDiffWithinAt
  convert SmoothOneFormFamily.sum Finset.univ (fun i _ => hterm i) using 1
  funext q x
  simp only [extFamily, Finset.sum_apply]
  rfl

end PrimExt

open PrimExt in
/-- The explicit smooth extension of the physical primitive at exhaustion level `ℓ`. -/
def primitiveExt (A B D S : ℕ) (c L : ℝ) (P : Set (Moments 2)) (ℓ : ℕ) :
    Moments 2 → ManifoldOneForm RealModel BaseCurve :=
  fun p => extFamily A B D S c (betaC A B D S ℓ) (margin A B L P)
    (width A B (betaC A B D S ℓ) (margin A B L P)) (physicalParameter L p)

open PrimExt in
theorem primitiveExt_spec {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (c L : ℝ) {P : Set (Moments 2)} (hP : IsCompact P)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B)) (ℓ : ℕ) :
    SmoothOneFormFamily (primitiveExt A B D S c L P ℓ) ∧
      ∀ᶠ q in 𝓝ˢ (P ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1 ∈ Radial.lowerTrapezoid A B →
        primitiveExt A B D S c L P ℓ q.1 q.2 = physicalPrimitive (A := A) (B := B) D S c L q.1 q.2 := by
  set β := betaC A B D S ℓ
  set m := margin A B L P
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hpc : Continuous (physicalParameter L) := (physicalParameter_smooth L).continuous
  -- the suprema over the compact image of `P`
  have hc1 : Continuous fun p => (physicalParameter L p).1 := hpc.fst
  have hc2 : Continuous fun p => (physicalParameter L p).1 + (physicalParameter L p).2 :=
    hpc.fst.add hpc.snd
  have hs1 : ∀ p ∈ P, (physicalParameter L p).1 ≤ sOne L P := fun p hp =>
    le_csSup (hP.image hc1).bddAbove (mem_image_of_mem _ hp)
  have hs2 : ∀ p ∈ P, (physicalParameter L p).1 + (physicalParameter L p).2 ≤ sTwo L P :=
    fun p hp => le_csSup (hP.image hc2).bddAbove (mem_image_of_mem _ hp)
  have hs1lt : sOne L P < A ∧ 0 ≤ sOne L P := by
    rcases (P.eq_empty_or_nonempty) with he | hne
    · simp [sOne, he, hAr]
    · obtain ⟨p, hp, hpe⟩ := (hP.image hc1).sSup_mem (hne.image _)
      unfold sOne
      rw [← hpe]
      exact ⟨(hPS hp).2.1, (hPS hp).1⟩
  have hs2lt : sTwo L P < B := by
    rcases (P.eq_empty_or_nonempty) with he | hne
    · simp [sTwo, he]
      linarith
    · obtain ⟨p, hp, hpe⟩ := (hP.image hc2).sSup_mem (hne.image _)
      unfold sTwo
      rw [← hpe]
      exact (hPS hp).2.2.2
  have hm : 0 < m := by
    simp only [m, margin]
    have := lt_min (sub_pos.mpr hs1lt.1) (sub_pos.mpr hs2lt)
    linarith
  have hmA : m ≤ A := by
    simp only [m, margin]
    have := min_le_left ((A : ℝ) - sOne L P) ((B : ℝ) - sTwo L P)
    linarith [hs1lt.2]
  have hm1 : m ≤ (A - sOne L P) / 4 := by
    simp only [m, margin]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hm2 : m ≤ (B - sTwo L P) / 4 := by
    simp only [m, margin]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨hδ, -⟩ := width_spec (β := β) hA hAB hm
  refine ⟨(extFamily_smooth hA hAB D S c hm hmA).comp (physicalParameter_smooth L), ?_⟩
  -- agreement near `P × C`
  have haC : Continuous fun x => ∑ i, aMap A B D S x i :=
    continuous_finsetSum _ fun i _ => (coefficientNorm_smooth _ _).continuous
  apply mem_nhdsSet_iff_forall.mpr
  rintro ⟨p0, x0⟩ ⟨hp0, hx0⟩
  have hb0 : ∑ i, aMap A B D S x0 i ≤ β :=
    le_csSup ((cubicExhaustion_compact ℓ).image haC).bddAbove (mem_image_of_mem _ hx0)
  have e1 : ∀ᶠ q in 𝓝 ((p0, x0) : Moments 2 × BaseCurve), ∑ i, aMap A B D S q.2 i < β + 1/2 :=
    (haC.comp continuous_snd).continuousAt.eventually_lt continuousAt_const
      (by show ∑ i, aMap A B D S x0 i < β + 1/2; linarith)
  have e2 : ∀ᶠ q in 𝓝 ((p0, x0) : Moments 2 × BaseCurve),
      (physicalParameter L q.1).1 < A - 3 * m :=
    (hc1.comp continuous_fst).continuousAt.eventually_lt continuousAt_const
      (by have := hs1 p0 hp0; simp only [Function.comp_apply]; linarith)
  have e3 : ∀ᶠ q in 𝓝 ((p0, x0) : Moments 2 × BaseCurve),
      (physicalParameter L q.1).1 + (physicalParameter L q.1).2 < B - 3 * m :=
    (hc2.comp continuous_fst).continuousAt.eventually_lt continuousAt_const
      (by have := hs2 p0 hp0; simp only [Function.comp_apply]; linarith)
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3 hqt
  set z : Radial.Plane := physicalParameter L q.1
  have hapos : ∀ i, 0 < aMap A B D S q.2 i := fun i => by
    linarith [aMap_ge A B D S q.2 i]
  have hcut : cutoff A B β m (width A B β m) (aMap A B D S q.2, z) = 1 := by
    apply cutoff_eq_one hδ hm
    · intro i
      have : aMap A B D S q.2 i ≤ ∑ j, aMap A B D S q.2 j :=
        Finset.single_le_sum (fun j _ => (hapos j).le) (Finset.mem_univ i)
      linarith
    · have := hqt.1; linarith
    · have := hqt.2.2.1; linarith
    · exact hq2.le
    · exact hq3.le
  change (∑ i, extSel A B β m (width A B β m) (aMap A B D S q.2, z) i •
      weightedFSPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c q.2) =
    ∑ i, radialProbability Radial.latticeIndex (cubicDegree D) (cubicMarkedOrder S) z q.2 i •
      weightedFSPrimitive (cubicDegree D i) (cubicMarkedOrder S i) c q.2
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [extSel, hcut, one_smul, selExt, radialProbability, Radial.selected]
  rw [rootExt_trap hA hAB hapos hqt]
  rfl

end SymplecticPacking.BranchLarge3
