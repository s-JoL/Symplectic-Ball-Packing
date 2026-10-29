import SymplecticPacking.General.Interface

/-!
# Complex coordinates on `ℝ^{2n}` for the large-ball branch

`zc y j = q_j + i p_j` (`General.toPhase`) and its inverse `ofPhase`. In dimension `n = m + 1`
the first complex coordinate `z = zc y 0` is the *first normal fibre* of the coupled model and
`ξ = (zc y 1, …, zc y m)` is the *base ball-chart coordinate* (paper `lem:lrg-slit`,
supplement `lem:two-slit`). The moments are `u = π|z|²` (`fibMoment`) and
`μ = π|ξ|²` (`baseMoment`); `π‖y‖² = u + μ`.

The bridge identities `omega0 = Σ_j Im(conj a_j b_j)` and `‖y‖² = Σ_j |z_j|²` are proved here.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General
open scoped ContDiff

/-- The complex coordinates `z_j = q_j + i p_j`. -/
def zc {n : ℕ} (y : E n) (j : Fin n) : ℂ := toPhase y j

/-- The point of `ℝ^{2n}` with complex coordinates `Z`. -/
def ofPhase {n : ℕ} (Z : Fin n → ℂ) : E n :=
  WithLp.toLp 2 fun i : Fin (2 * n) =>
    if h : (i : ℕ) < n then (Z ⟨i, h⟩).re else (Z ⟨(i : ℕ) - n, by have := i.isLt; omega⟩).im

@[simp] lemma ofPhase_q {n : ℕ} (Z : Fin n → ℂ) (j : Fin n) : ofPhase Z (qIdx j) = (Z j).re := by
  simp [ofPhase, qIdx]

@[simp] lemma ofPhase_p {n : ℕ} (Z : Fin n → ℂ) (j : Fin n) : ofPhase Z (pIdx j) = (Z j).im := by
  have : ¬ ((pIdx j : Fin (2 * n)) : ℕ) < n := by simp [pIdx]
  simp only [ofPhase, PiLp.toLp_apply, dif_neg this]
  congr 2; ext; simp [pIdx]

@[simp] lemma zc_ofPhase {n : ℕ} (Z : Fin n → ℂ) (j : Fin n) : zc (ofPhase Z) j = Z j := by
  apply Complex.ext <;> simp [zc, toPhase]

lemma zc_re {n : ℕ} (y : E n) (j : Fin n) : (zc y j).re = y (qIdx j) := rfl

lemma zc_im {n : ℕ} (y : E n) (j : Fin n) : (zc y j).im = y (pIdx j) := rfl

/-- Every index of `Fin (2n)` is a `q`- or a `p`-index. -/
lemma idx_cases {n : ℕ} (i : Fin (2 * n)) :
    (∃ h : (i : ℕ) < n, i = qIdx ⟨i, h⟩) ∨
      (∃ h : n ≤ (i : ℕ), i = pIdx ⟨(i : ℕ) - n, by have := i.isLt; omega⟩) := by
  by_cases h : (i : ℕ) < n
  · exact Or.inl ⟨h, Fin.ext (by simp [qIdx])⟩
  · refine Or.inr ⟨by omega, Fin.ext ?_⟩
    simp [pIdx]; omega

@[simp] lemma ofPhase_zc {n : ℕ} (y : E n) : ofPhase (zc y) = y := by
  ext i
  rcases idx_cases i with ⟨h, hi⟩ | ⟨h, hi⟩
  · rw [hi, ofPhase_q, zc_re]
  · rw [hi, ofPhase_p, zc_im]

lemma eq_of_zc_eq {n : ℕ} {y y' : E n} (h : ∀ j, zc y j = zc y' j) : y = y' := by
  rw [← ofPhase_zc y, ← ofPhase_zc y']; exact congrArg ofPhase (funext h)

/-- `ofPhase` as a real-linear map. -/
def ofPhaseL (n : ℕ) : (Fin n → ℂ) →ₗ[ℝ] E n where
  toFun := ofPhase
  map_add' Z W := by
    apply eq_of_zc_eq; intro j
    apply Complex.ext <;> simp [zc, toPhase]
  map_smul' r Z := by
    apply eq_of_zc_eq; intro j
    apply Complex.ext <;> simp [zc, toPhase]

/-- `ofPhase` as a continuous linear map. -/
def ofPhaseCLM (n : ℕ) : (Fin n → ℂ) →L[ℝ] E n :=
  LinearMap.toContinuousLinearMap (ofPhaseL n)

@[simp] lemma ofPhaseCLM_apply {n : ℕ} (Z : Fin n → ℂ) : ofPhaseCLM n Z = ofPhase Z := rfl

/-- `zc · j` as a continuous linear map. -/
def zcCLM {n : ℕ} (j : Fin n) : E n →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => zc y j
      map_add' := fun y y' => by apply Complex.ext <;> simp [zc, toPhase]
      map_smul' := fun r y => by apply Complex.ext <;> simp [zc, toPhase] }

@[simp] lemma zcCLM_apply {n : ℕ} (j : Fin n) (y : E n) : zcCLM j y = zc y j := rfl

lemma zc_contDiff {n : ℕ} (j : Fin n) : ContDiff ℝ ∞ (fun y : E n => zc y j) :=
  (zcCLM j).contDiff

lemma ofPhase_contDiff {n : ℕ} : ContDiff ℝ ∞ (ofPhase (n := n)) :=
  (ofPhaseCLM n).contDiff

@[simp] lemma zc_add {n : ℕ} (y y' : E n) (j : Fin n) : zc (y + y') j = zc y j + zc y' j :=
  (zcCLM j).map_add y y'

@[simp] lemma zc_smul {n : ℕ} (r : ℝ) (y : E n) (j : Fin n) : zc (r • y) j = r • zc y j :=
  (zcCLM j).map_smul r y

/-- Splitting a sum over `Fin (2n)` into `q`- and `p`-indices. -/
lemma sum_two_mul {n : ℕ} (f : Fin (2 * n) → ℝ) :
    ∑ i, f i = ∑ j : Fin n, (f (qIdx j) + f (pIdx j)) := by
  rw [Finset.sum_add_distrib, ← Equiv.sum_comp (finCongr (two_mul n)).symm, Fin.sum_univ_add]
  congr 1

/-- `‖y‖² = Σ_j |z_j|²`. -/
lemma norm_sq_eq {n : ℕ} (y : E n) : ‖y‖ ^ 2 = ∑ j, Complex.normSq (zc y j) := by
  rw [EuclideanSpace.norm_sq_eq, sum_two_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.normSq_apply, zc, toPhase, sq]

/-- `ω₀(x, y) = Σ_j Im(conj(x_j) y_j)`. -/
lemma omega0_eq {n : ℕ} (x y : E n) :
    Problem.omega0 x y = ∑ j, ((zc x j).re * (zc y j).im - (zc x j).im * (zc y j).re) := rfl

/-! ### The first fibre and the base in dimension `m + 1` -/

/-- The fibre moment `u = π|z₀|²`. -/
def fibMoment {m : ℕ} (y : E (m + 1)) : ℝ := Real.pi * Complex.normSq (zc y 0)

/-- The base moment `μ = π Σ_{i ≥ 1} |z_i|²` (capacity of the base ball-chart point). -/
def baseMoment {m : ℕ} (y : E (m + 1)) : ℝ :=
  Real.pi * ∑ i : Fin m, Complex.normSq (zc y i.succ)

lemma fibMoment_contDiff {m : ℕ} : ContDiff ℝ ∞ (fibMoment (m := m)) := by
  unfold fibMoment
  simp only [Complex.normSq_apply]
  exact contDiff_const.mul
    ((Complex.reCLM.contDiff.comp (zc_contDiff 0)).mul (Complex.reCLM.contDiff.comp (zc_contDiff 0))
      |>.add ((Complex.imCLM.contDiff.comp (zc_contDiff 0)).mul
        (Complex.imCLM.contDiff.comp (zc_contDiff 0))))

lemma baseMoment_contDiff {m : ℕ} : ContDiff ℝ ∞ (baseMoment (m := m)) := by
  unfold baseMoment
  simp only [Complex.normSq_apply]
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact (Complex.reCLM.contDiff.comp (zc_contDiff _)).mul
      (Complex.reCLM.contDiff.comp (zc_contDiff _))
    |>.add ((Complex.imCLM.contDiff.comp (zc_contDiff _)).mul
      (Complex.imCLM.contDiff.comp (zc_contDiff _)))

end SymplecticPacking.BranchLargeHigh
