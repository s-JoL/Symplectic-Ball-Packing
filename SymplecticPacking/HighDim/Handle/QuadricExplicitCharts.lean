import SymplecticPacking.HighDim.Handle.QuadricPresentationCenters

/-!
# Explicit charts on diagonal quadric curves

Explicit algebraic local coordinates on a diagonal quadric curve.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open scoped ContDiff
open OAI.PackingSufficiencySupport.DiagonalQuadrics

/-- The root near a specified nonzero root, with its branch fixed at the centre. -/
def rootNear (c d : ℂ) : ℂ := c * Complex.sqrt (1 + d / c^2)

theorem rootNear_sq {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    rootNear c d ^ 2 = c^2+d := by
  rw [rootNear, mul_pow, sqrt_sq_complex]
  field_simp

theorem rootNear_ratio {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    rootNear c d / c = Complex.sqrt (1+d/c^2) := by
  simp [rootNear, mul_div_cancel_left₀, hc]

theorem rootNear_self {c z : ℂ} (hc : c ≠ 0) (hz : 0 < (z/c).re) :
    rootNear c (z^2-c^2) = z := by
  have hh : (1 : ℂ) + (z^2-c^2)/c^2 = (z/c)^2 := by field_simp; ring
  rw [rootNear, hh, sqrt_of_sq_pos hz]
  field_simp

theorem rootNear_contDiffAt {c d : ℂ} (hd : 0 < (1+d/c^2).re) :
    ContDiffAt ℂ ∞ (rootNear c) d := by
  exact contDiffAt_const.mul ((sqrt_contDiffAt hd).comp d
    (contDiffAt_const.add (contDiffAt_id.div_const _)))

/-- The algebraic inverse of the ordinary coordinate `z₀`, with all signs fixed by `c`. -/
def ordinaryLocalLift {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) (u : ℂ) : locus a :=
  ⟨(u, fun j => rootNear (c.val.2 j) (u^2-c.val.1^2)), by
    apply mem_locus.mpr
    intro j
    change rootNear (c.val.2 j) (u^2-c.val.1^2)^2 = u^2-a j
    rw [rootNear_sq (hc j), mem_locus.mp c.property j]
    ring⟩

def ordinaryLocalTarget {m : ℕ} {a : Fin m → ℂ} (c : locus a) : Set ℂ :=
  {u | ∀ j, 0 < (1+(u^2-c.val.1^2)/(c.val.2 j)^2 : ℂ).re}

def ordinaryLocalSource {m : ℕ} {a : Fin m → ℂ} (c : locus a) : Set (locus a) :=
  {x | x.val.1 ∈ ordinaryLocalTarget c ∧ ∀ j, 0 < (x.val.2 j/c.val.2 j).re}

theorem ordinaryLocalTarget_open {m : ℕ} {a : Fin m → ℂ} (c : locus a) :
    IsOpen (ordinaryLocalTarget c) := by
  simp only [ordinaryLocalTarget, ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)

theorem ordinaryLocalSource_open {m : ℕ} {a : Fin m → ℂ} (c : locus a) :
    IsOpen (ordinaryLocalSource c) := by
  change IsOpen ((fun x : locus a => x.val.1) ⁻¹' ordinaryLocalTarget c ∩
    {x : locus a | ∀ j, 0 < (x.val.2 j/c.val.2 j).re})
  apply IsOpen.inter ((ordinaryLocalTarget_open c).preimage (by fun_prop))
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)

theorem ordinaryLocalLift_target {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) {u : ℂ} (hu : u ∈ ordinaryLocalTarget c) :
    ordinaryLocalLift c hc u ∈ ordinaryLocalSource c := by
  refine ⟨hu, ?_⟩
  intro j
  change 0 < (rootNear (c.val.2 j) (u^2-c.val.1^2) / c.val.2 j).re
  rw [rootNear_ratio (hc j)]
  exact sqrt_re_pos (hu j)

theorem ordinaryLocalLift_left {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) {x : locus a} (hx : x ∈ ordinaryLocalSource c) :
    ordinaryLocalLift c hc x.val.1 = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    change rootNear (c.val.2 j) (x.val.1^2-c.val.1^2) = x.val.2 j
    have hh : x.val.1^2-c.val.1^2 = (x.val.2 j)^2-(c.val.2 j)^2 := by
      rw [mem_locus.mp x.property j, mem_locus.mp c.property j]
      ring
    rw [hh]
    exact rootNear_self (hc j) (hx.2 j)

theorem ordinaryLocalLift_smooth {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) :
    ContDiffOn ℂ ∞ (fun u => (ordinaryLocalLift c hc u : Affine m)) (ordinaryLocalTarget c) := by
  intro u hu
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_id.prodMk
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℂ ∞ (fun u : ℂ => rootNear (c.val.2 j) (u^2-c.val.1^2)) u
  exact ContDiffAt.comp (f := fun u : ℂ => u^2-c.val.1^2) (g := rootNear (c.val.2 j)) u
    (rootNear_contDiffAt (hu j)) ((contDiffAt_id.pow 2).sub contDiffAt_const)

/-- A local homeomorphism, with no inverse-function or root choices in its definition. -/
def ordinaryExplicitChart {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) : OpenPartialHomeomorph (locus a) ℂ where
  toFun x := x.val.1
  invFun := ordinaryLocalLift c hc
  source := ordinaryLocalSource c
  target := ordinaryLocalTarget c
  map_source' := fun _ hx => hx.1
  map_target' := fun _ hu => ordinaryLocalLift_target c hc hu
  left_inv' := fun _ hx => ordinaryLocalLift_left c hc hx
  right_inv' := fun _ _ => rfl
  open_source := ordinaryLocalSource_open c
  open_target := ordinaryLocalTarget_open c
  continuousOn_toFun := (show Continuous (fun x : locus a => x.val.1) by fun_prop).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    exact continuousOn_iff_continuous_domRestrict.mp (ordinaryLocalLift_smooth c hc).continuousOn

theorem ordinaryExplicitChart_center {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) : c ∈ (ordinaryExplicitChart c hc).source := by
  refine ⟨?_, ?_⟩
  · intro j
    simp
  · intro j
    simp [div_self (hc j)]

/-- The inverse of the coordinate `zᵢ` at a point where all the other roots are regular. -/
def branchLocalLift {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) (v : ℂ) : locus a :=
  ⟨(rootNear c.val.1 (v^2-(c.val.2 i)^2),
    fun j => if j=i then v else rootNear (c.val.2 j) (v^2-(c.val.2 i)^2)), by
    apply mem_locus.mpr
    intro j
    change (if j=i then v else rootNear (c.val.2 j) (v^2-(c.val.2 i)^2))^2 =
      rootNear c.val.1 (v^2-(c.val.2 i)^2)^2-a j
    rw [rootNear_sq hc.1]
    by_cases hji : j=i
    · subst j
      rw [if_pos rfl, mem_locus.mp c.property i]
      ring
    · rw [if_neg hji, rootNear_sq (hc.2 j hji), mem_locus.mp c.property j]
      ring⟩

def branchLocalTarget {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m) : Set ℂ :=
  {v | 0 < (1+(v^2-(c.val.2 i)^2)/c.val.1^2 : ℂ).re ∧
    ∀ j, j≠i → 0 < (1+(v^2-(c.val.2 i)^2)/(c.val.2 j)^2 : ℂ).re}

def branchLocalSource {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m) : Set (locus a) :=
  {x | x.val.2 i ∈ branchLocalTarget c i ∧ 0 < (x.val.1/c.val.1).re ∧
    ∀ j, j≠i → 0 < (x.val.2 j/c.val.2 j).re}

theorem branchLocalTarget_open {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m) :
    IsOpen (branchLocalTarget c i) := by
  change IsOpen ({v : ℂ | 0 < (1+(v^2-(c.val.2 i)^2)/c.val.1^2 : ℂ).re} ∩
    {v : ℂ | ∀ j, j≠i → 0 < (1+(v^2-(c.val.2 i)^2)/(c.val.2 j)^2 : ℂ).re})
  apply IsOpen.inter (isOpen_lt continuous_const (by fun_prop))
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
    isOpen_lt continuous_const (by fun_prop)

theorem branchLocalSource_open {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m) :
    IsOpen (branchLocalSource c i) := by
  change IsOpen ((fun x : locus a => x.val.2 i) ⁻¹' branchLocalTarget c i ∩
    ({x : locus a | 0 < (x.val.1/c.val.1).re} ∩
      {x : locus a | ∀ j, j≠i → 0 < (x.val.2 j/c.val.2 j).re}))
  apply IsOpen.inter ((branchLocalTarget_open c i).preimage (by fun_prop))
  apply IsOpen.inter (isOpen_lt continuous_const (by fun_prop))
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
    isOpen_lt continuous_const (by fun_prop)

theorem branchLocalLift_target {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) {v : ℂ} (hv : v ∈ branchLocalTarget c i) :
    branchLocalLift c i hc v ∈ branchLocalSource c i := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [branchLocalLift, ite_true] using hv
  · change 0 < (rootNear c.val.1 (v^2-(c.val.2 i)^2)/c.val.1).re
    rw [rootNear_ratio hc.1]
    exact sqrt_re_pos hv.1
  · intro j hji
    change 0 < ((if j=i then v else rootNear (c.val.2 j) (v^2-(c.val.2 i)^2))/c.val.2 j).re
    rw [if_neg hji, rootNear_ratio (hc.2 j hji)]
    exact sqrt_re_pos (hv.2 j hji)

theorem branchLocalLift_left {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) {x : locus a} (hx : x ∈ branchLocalSource c i) :
    branchLocalLift c i hc (x.val.2 i) = x := by
  have h0 : (x.val.2 i)^2-(c.val.2 i)^2 = x.val.1^2-c.val.1^2 := by
    rw [mem_locus.mp x.property i, mem_locus.mp c.property i]
    ring
  apply Subtype.ext
  apply Prod.ext
  · change rootNear c.val.1 ((x.val.2 i)^2-(c.val.2 i)^2) = x.val.1
    rw [h0]
    exact rootNear_self hc.1 hx.2.1
  · funext j
    change (if j=i then x.val.2 i else rootNear (c.val.2 j) ((x.val.2 i)^2-(c.val.2 i)^2)) = x.val.2 j
    by_cases hji : j=i
    · subst j
      simp
    · have hj : (x.val.2 i)^2-(c.val.2 i)^2 = (x.val.2 j)^2-(c.val.2 j)^2 := by
        rw [mem_locus.mp x.property i, mem_locus.mp c.property i,
          mem_locus.mp x.property j, mem_locus.mp c.property j]
        ring
      rw [if_neg hji, hj]
      exact rootNear_self (hc.2 j hji) (hx.2.2 j hji)

theorem branchLocalLift_smooth {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) :
    ContDiffOn ℂ ∞ (fun v => (branchLocalLift c i hc v : Affine m)) (branchLocalTarget c i) := by
  intro v hv
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.prodMk
  · change ContDiffAt ℂ ∞ (fun v : ℂ => rootNear c.val.1 (v^2-(c.val.2 i)^2)) v
    exact ContDiffAt.comp (f := fun v : ℂ => v^2-(c.val.2 i)^2) (g := rootNear c.val.1) v
      (rootNear_contDiffAt hv.1) ((contDiffAt_id.pow 2).sub contDiffAt_const)
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℂ ∞ (fun v : ℂ => if j=i then v else rootNear (c.val.2 j) (v^2-(c.val.2 i)^2)) v
    by_cases hji : j=i
    · simp only [ite_eq_left hji]
      exact contDiffAt_id
    · simp only [ite_eq_right hji]
      exact ContDiffAt.comp (f := fun v : ℂ => v^2-(c.val.2 i)^2) (g := rootNear (c.val.2 j)) v
        (rootNear_contDiffAt (hv.2 j hji)) ((contDiffAt_id.pow 2).sub contDiffAt_const)

def branchExplicitChart {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) : OpenPartialHomeomorph (locus a) ℂ where
  toFun x := x.val.2 i
  invFun := branchLocalLift c i hc
  source := branchLocalSource c i
  target := branchLocalTarget c i
  map_source' := fun _ hx => hx.1
  map_target' := fun _ hv => branchLocalLift_target c i hc hv
  left_inv' := fun _ hx => branchLocalLift_left c i hc hx
  right_inv' := fun _ _ => by simp only [branchLocalLift, ite_true]
  open_source := branchLocalSource_open c i
  open_target := branchLocalTarget_open c i
  continuousOn_toFun := (show Continuous (fun x : locus a => x.val.2 i) by fun_prop).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    exact continuousOn_iff_continuous_domRestrict.mp (branchLocalLift_smooth c i hc).continuousOn

theorem branchExplicitChart_center {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) : c ∈ (branchExplicitChart c i hc).source := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp
  · intro j _
    simp
  · simp [div_self hc.1]
  · intro j hji
    simp [div_self (hc.2 j hji)]

#check_explicit ordinaryExplicitChart
#check_explicit branchExplicitChart
end SymplecticPacking.HighDim.ToricPackingStages
