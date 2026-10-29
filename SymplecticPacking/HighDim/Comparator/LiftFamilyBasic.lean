import SymplecticPacking.HighDim.Comparator.RealiseGen

/-!
# Elementary facts on the slice data of `RealiseGen.liftGen` (supplement S-lem:plc-slice,
S-lem:plc-faces)

Smoothness of the face lengths and cutoffs, the soft-min bounds `ℓ ≤ L_ν − δ₀` and `ℓ > 0` where
all face lengths exceed `η₀`, the support of the cutoff `χ` (`‖y‖_∞ < 2R`, `L_ν > 5η₀/4`), and the
area of the rescaled point `u/√ℓ`. Used for `liftFamily_smooth/spatial/collar/disc`.
-/

noncomputable section

namespace SymplecticPacking.HighDim.RealiseGen

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m q : ℕ} {Δ : Polytope m q} {F : PolyFn m} {j : Fin m} {e : ℝ}

/-! ### Smoothness -/

theorem contDiff_faceLen (Δ : Polytope m q) (j : Fin m) (ν : Fin q) :
    ContDiff ℝ ∞ (faceLen Δ j ν) := by
  have hfun : faceLen Δ j ν = fun y : Moments m =>
      (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * y i)) / Δ.b ν j := rfl
  rw [hfun]
  refine (contDiff_const.sub (ContDiff.sum fun i _ => ?_)).div_const _
  by_cases h : i = j
  · simp only [if_pos h]; exact contDiff_const
  · simp only [if_neg h]; exact contDiff_const.mul (contDiff_apply ℝ ℝ i)

theorem contDiff_lenCut (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    ContDiff ℝ ∞ (lenCut Δ F j e) := by
  have hfun : lenCut Δ F j e = fun y : Moments m => ∏ ν, (if 0 < Δ.b ν j then
      Real.smoothTransition ((faceLen Δ j ν y - 5 * eta0 F j e / 4) / (eta0 F j e / 2))
      else 1) := rfl
  rw [hfun]
  refine contDiff_prod fun ν _ => ?_
  by_cases h : 0 < Δ.b ν j
  · simp only [if_pos h]
    exact (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp
      (((contDiff_faceLen Δ j ν).sub contDiff_const).div_const _)
  · simp only [if_neg h]; exact contDiff_const

theorem contDiff_boxCut (Δ : Polytope m q) (j : Fin m) : ContDiff ℝ ∞ (boxCut Δ j) := by
  have hfun : boxCut Δ j = fun y : Moments m => ∏ i, (if i = j then 1 else
      1 - Real.smoothTransition ((y i ^ 2 - boxRad Δ ^ 2) / (3 * boxRad Δ ^ 2))) := rfl
  rw [hfun]
  refine contDiff_prod fun i _ => ?_
  by_cases h : i = j
  · simp only [if_pos h]; exact contDiff_const
  · simp only [if_neg h]
    exact contDiff_const.sub
      ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp
        ((((contDiff_apply ℝ ℝ i).pow 2).sub contDiff_const).div_const _))

theorem contDiff_cut (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    ContDiff ℝ ∞ (cut Δ F j e) :=
  (contDiff_boxCut Δ j).mul (contDiff_lenCut Δ F j e)

/-! ### The soft minimum -/

/-- The exponential sum inside `softLen`. -/
def expSum (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) : ℝ :=
  ∑ ν, (if 0 < Δ.b ν j then Real.exp (-faceLen Δ j ν y / softTemp q F j e) else 0)

theorem softLen_eq (y : Moments m) : softLen Δ F j e y =
    -softTemp q F j e * Real.log (expSum Δ F j e y) - softShift F j e := rfl

theorem contDiff_expSum (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    ContDiff ℝ ∞ (expSum Δ F j e) := by
  have hfun : expSum Δ F j e = fun y : Moments m =>
      ∑ ν, (if 0 < Δ.b ν j then Real.exp (-faceLen Δ j ν y / softTemp q F j e) else 0) := rfl
  rw [hfun]
  refine ContDiff.sum fun ν _ => ?_
  by_cases h : 0 < Δ.b ν j
  · simp only [if_pos h]; exact (((contDiff_faceLen Δ j ν).neg).div_const _).exp
  · simp only [if_neg h]; exact contDiff_const

theorem exp_le_expSum {ν : Fin q} (hν : 0 < Δ.b ν j) (y : Moments m) :
    Real.exp (-faceLen Δ j ν y / softTemp q F j e) ≤ expSum Δ F j e y := by
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun ν' => if 0 < Δ.b ν' j then
      Real.exp (-faceLen Δ j ν' y / softTemp q F j e) else 0)
    (fun ν' _ => by split_ifs <;> positivity) (Finset.mem_univ ν)
  simp only [if_pos hν] at this
  exact this

/-- Soft-min upper bound `ℓ(y) ≤ L_ν(y) − δ₀`. -/
theorem softLen_le_faceLen (he : 0 < e) {ν : Fin q} (hν : 0 < Δ.b ν j) (y : Moments m) :
    softLen Δ F j e y ≤ faceLen Δ j ν y - softShift F j e := by
  have hs := softTemp_pos (q := q) F j he
  have h1 := exp_le_expSum (F := F) (e := e) hν y
  have h2 : -faceLen Δ j ν y / softTemp q F j e ≤ Real.log (expSum Δ F j e y) := by
    rw [← Real.log_exp (-faceLen Δ j ν y / softTemp q F j e)]
    exact Real.log_le_log (Real.exp_pos _) h1
  rw [div_le_iff₀ hs] at h2
  rw [softLen_eq]
  nlinarith

/-- Parameters all of whose face lengths exceed `η₀` (an open neighbourhood of `supp χ`). -/
def goodParams (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) : Set (Moments m) :=
  {y | ∀ ν, 0 < Δ.b ν j → eta0 F j e < faceLen Δ j ν y}

/-- On `goodParams` the exponential sum is positive and `ℓ ≥ η₀ − ζ/2 > 0`. -/
theorem expSum_pos_softLen_pos (hΔ : Δ.Spec) (he : 0 < e) {y : Moments m}
    (hy : y ∈ goodParams Δ F j e) : 0 < expSum Δ F j e y ∧ 0 < softLen Δ F j e y := by
  obtain ⟨ν₀, hν₀⟩ := hΔ.bounded_dir j
  have hη := eta0_pos F j he
  have hs := softTemp_pos (q := q) F j he
  have hpos : 0 < expSum Δ F j e y :=
    lt_of_lt_of_le (Real.exp_pos _) (exp_le_expSum (F := F) (e := e) hν₀ y)
  refine ⟨hpos, ?_⟩
  have hq : (0 : ℝ) < q := by
    have : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) ν₀.isLt
    exact_mod_cast this
  have hle : expSum Δ F j e y ≤ q * Real.exp (-eta0 F j e / softTemp q F j e) := by
    have : expSum Δ F j e y ≤ ∑ _ν : Fin q, Real.exp (-eta0 F j e / softTemp q F j e) := by
      refine Finset.sum_le_sum fun ν _ => ?_
      split_ifs with h
      · apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hs.le
        linarith [hy ν h]
      · positivity
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hlog : Real.log (expSum Δ F j e y) ≤ Real.log q + -eta0 F j e / softTemp q F j e := by
    rw [← Real.log_exp (-eta0 F j e / softTemp q F j e), ← Real.log_mul hq.ne' (by positivity)]
    exact Real.log_le_log hpos hle
  have hlq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq
  have hsz : softTemp q F j e * (4 * ((q : ℝ) + 1)) = zeta F j e := by
    unfold softTemp; field_simp
  have hz : zeta F j e = eta0 F j e / 8 := rfl
  have hδ : softShift F j e = zeta F j e / 4 := rfl
  have hmul : softTemp q F j e * (-eta0 F j e / softTemp q F j e) = -eta0 F j e := by
    field_simp
  have h3 : softTemp q F j e * Real.log (expSum Δ F j e y) ≤
      softTemp q F j e * (q - 1) - eta0 F j e := by
    have := mul_le_mul_of_nonneg_left hlog hs.le
    have h4 := mul_le_mul_of_nonneg_left hlq hs.le
    rw [mul_add, hmul] at this
    linarith
  rw [softLen_eq]
  nlinarith

/-! ### Support of the cutoff -/

theorem faceLen_of_lenCut_ne (he : 0 < e) {y : Moments m} (h : lenCut Δ F j e y ≠ 0)
    {ν : Fin q} (hν : 0 < Δ.b ν j) : 5 * eta0 F j e / 4 < faceLen Δ j ν y := by
  have hη := eta0_pos F j he
  have := (Finset.prod_ne_zero_iff.mp h) ν (Finset.mem_univ _)
  rw [if_pos hν] at this
  by_contra hc
  push_neg at hc
  apply this
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

theorem two_le_boxRad (hΔ : Δ.Spec) : 2 ≤ boxRad Δ := by
  unfold boxRad
  have : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
      split_ifs with h
      · exact (div_pos (hΔ.ℓ_pos ν) h).le
      · exact le_rfl
  linarith

theorem abs_lt_of_boxCut_ne (hΔ : Δ.Spec) {y : Moments m} (h : boxCut Δ j y ≠ 0) {i : Fin m}
    (hi : i ≠ j) : |y i| < 2 * boxRad Δ := by
  have hR := two_le_boxRad hΔ
  have := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
  rw [if_neg hi] at this
  have hR0 : 0 < boxRad Δ := by linarith
  have hR2 : 0 < 3 * boxRad Δ ^ 2 := by positivity
  have hlt : (y i ^ 2 - boxRad Δ ^ 2) / (3 * boxRad Δ ^ 2) < 1 := by
    by_contra hc
    push_neg at hc
    exact this (by rw [Real.smoothTransition.one_of_one_le hc]; ring)
  rw [div_lt_one hR2] at hlt
  exact abs_lt_of_sq_lt_sq (by nlinarith) (by linarith)

theorem cut_ne_zero {y : Moments m} (h : cut Δ F j e y ≠ 0) : boxCut Δ j y ≠ 0 ∧ lenCut Δ F j e y ≠ 0 := by
  have h' : boxCut Δ j y * lenCut Δ F j e y ≠ 0 := h
  exact ⟨left_ne_zero_of_mul h', right_ne_zero_of_mul h'⟩

theorem mem_goodParams_of_cut_ne (he : 0 < e) {y : Moments m} (h : cut Δ F j e y ≠ 0) :
    y ∈ goodParams Δ F j e := fun ν hν => by
  have := faceLen_of_lenCut_ne he (cut_ne_zero h).2 hν
  linarith [eta0_pos F j he]

theorem tsupport_cut_subset (he : 0 < e) : tsupport (cut Δ F j e) ⊆ goodParams Δ F j e := by
  have hη := eta0_pos F j he
  let C : Set (Moments m) := ⋂ ν, {y | 0 < Δ.b ν j → 5 * eta0 F j e / 4 ≤ faceLen Δ j ν y}
  have hC : IsClosed C := isClosed_iInter fun ν => by
    by_cases h : 0 < Δ.b ν j
    · simp only [h, true_implies]
      exact isClosed_le continuous_const (contDiff_faceLen Δ j ν).continuous
    · simp only [h, false_implies, setOf_true]; exact isClosed_univ
  have hsub : Function.support (cut Δ F j e) ⊆ C := by
    intro y hy
    have hl : lenCut Δ F j e y ≠ 0 := (cut_ne_zero hy).2
    simp only [C, mem_iInter, mem_setOf_eq]
    intro ν hν
    exact (faceLen_of_lenCut_ne he hl hν).le
  intro y hy ν hν
  have := hC.closure_subset_iff.mpr hsub hy
  simp only [C, mem_iInter, mem_setOf_eq] at this
  linarith [this ν hν]

/-! ### Rescaling -/

theorem planeArea_smul_inv_sqrt {l : ℝ} (hl : 0 < l) (u : Plane) :
    planeArea ((Real.sqrt l)⁻¹ • u) = planeArea u / l := by
  have h : ((Real.sqrt l)⁻¹) ^ 2 = l⁻¹ := by rw [inv_pow, Real.sq_sqrt hl.le]
  simp only [planeArea, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [div_eq_mul_inv, ← h]
  ring

end SymplecticPacking.HighDim.RealiseGen
