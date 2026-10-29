import SymplecticPacking.General.Ham.Curves
import SymplecticPacking.E4

/-!
# Support lemmas for the finite compilation in dimension `2n`

* `hamVF_eq_gradField`, `norm_gradField`: `X_H = J₀ ∇H`, so `‖X_H(t,y)‖ ≤ ‖D_y H(t,y)‖`.
* `opNorm_le_sum_abs`: `‖L‖ ≤ Σ_l |L e_l|` for a linear form on `ℝ^{2n}`.
* `boxCut`: the box cutoff `β_B` in dimension `2n` (Definition `def:cpl-box`, Lemma `lem:cpl-box`).
* `exists_integralCurve_global`: global integral curves of `X_H` for `H` smooth and supported in
  a fixed ball in space (no condition in time) (Lemma `lem:cpl-gronwall`, first part).
-/

noncomputable section

namespace SymplecticPacking.General.Compile

open Metric Set Filter Problem
open scoped ContDiff Topology NNReal

variable {n : ℕ}

/-! ### The Hamiltonian field as a rotated gradient -/

/-- `J₀` applied to the gradient of a linear form `L`. -/
def gradField (L : E n →L[ℝ] ℝ) : E n :=
  WithLp.toLp 2 fun i : Fin (2 * n) =>
    if h : (i : ℕ) < n then L (EuclideanSpace.single ⟨i + n, by omega⟩ 1)
    else -L (EuclideanSpace.single ⟨i - n, by have := i.isLt; omega⟩ 1)

lemma hamVF_eq_gradField (H : ℝ → E n → ℝ) (t : ℝ) (y : E n) :
    Problem.hamVF H t y = gradField (fderiv ℝ (H t) y) := rfl

lemma gradField_sub (L L' : E n →L[ℝ] ℝ) : gradField (L - L') = gradField L - gradField L' := by
  refine PiLp.ext fun i => ?_
  simp only [gradField, PiLp.sub_apply, PiLp.toLp_apply, ContinuousLinearMap.sub_apply]
  split_ifs <;> ring

/-- The Riesz vector of `L` has coordinates `L e_i`. -/
lemma riesz_apply (L : E n →L[ℝ] ℝ) (i : Fin (2 * n)) :
    ((InnerProductSpace.toDual ℝ (E n)).symm L) i = L (EuclideanSpace.single i 1) := by
  rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm, EuclideanSpace.inner_single_left]
  simp

lemma norm_riesz (L : E n →L[ℝ] ℝ) :
    ‖(InnerProductSpace.toDual ℝ (E n)).symm L‖ = ‖L‖ :=
  (InnerProductSpace.toDual ℝ (E n)).symm.norm_map L

/-- The coordinate swap `q_j ↔ p_j`. -/
def swapIdx (i : Fin (2 * n)) : Fin (2 * n) :=
  if h : (i : ℕ) < n then ⟨i + n, by omega⟩ else ⟨i - n, by have := i.isLt; omega⟩

lemma swapIdx_involutive : Function.Involutive (swapIdx (n := n)) := by
  intro i
  unfold swapIdx
  by_cases h : (i : ℕ) < n
  · rw [dif_pos h, dif_neg (by simp only [Fin.val_mk]; omega)]
    ext; simp only [Fin.val_mk]; omega
  · rw [dif_neg h, dif_pos (by simp only [Fin.val_mk]; have := i.isLt; omega)]
    ext; simp only [Fin.val_mk]; omega

lemma norm_gradField (L : E n →L[ℝ] ℝ) : ‖gradField L‖ = ‖L‖ := by
  rw [← norm_riesz L, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  set v := (InnerProductSpace.toDual ℝ (E n)).symm L
  have hpt : ∀ i, ‖(gradField L) i‖ ^ 2 = ‖v (swapIdx i)‖ ^ 2 := by
    intro i
    simp only [v, gradField, PiLp.toLp_apply, riesz_apply, swapIdx, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hpt i]
  exact Equiv.sum_comp (swapIdx_involutive (n := n)).toPerm (fun i => ‖v i‖ ^ 2)

lemma norm_le_sum_abs (z : E n) : ‖z‖ ≤ ∑ l, |z l| := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ l, ‖z l‖ ^ 2) ≤ Real.sqrt ((∑ l, |z l|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        rw [← sq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg (fun l _ => abs_nonneg _) |>.trans
          (le_of_eq (by rw [sq_abs]))
    _ = ∑ l, |z l| := Real.sqrt_sq (Finset.sum_nonneg fun l _ => abs_nonneg _)

/-- `‖L‖ ≤ Σ_l |L e_l|`. -/
lemma opNorm_le_sum_abs (L : E n →L[ℝ] ℝ) : ‖L‖ ≤ ∑ l, |L (EuclideanSpace.single l 1)| := by
  rw [← norm_riesz L]
  refine (norm_le_sum_abs _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun l _ => by rw [riesz_apply]

/-! ### The box cutoff in dimension `2n` -/

/-- `β_B(z) = ∏_l β_{B,1}(z_l)` on `ℝ^{2n}`. -/
def boxCut (n : ℕ) (B : ℝ) (z : E n) : ℝ := ∏ l : Fin (2 * n), boxCutoff1 B (z l)

lemma contDiff_boxCutoff1 (B : ℝ) : ContDiff ℝ ∞ (boxCutoff1 B) := by
  unfold boxCutoff1 flatStep
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma boxCutoff1_mem (B x : ℝ) : boxCutoff1 B x ∈ Icc (0 : ℝ) 1 := by
  unfold boxCutoff1 flatStep
  constructor
  · linarith [Real.smoothTransition.le_one ((x ^ 2 - (B / 2) ^ 2) / ((3 * B / 4) ^ 2 - (B / 2) ^ 2))]
  · linarith [Real.smoothTransition.nonneg ((x ^ 2 - (B / 2) ^ 2) / ((3 * B / 4) ^ 2 - (B / 2) ^ 2))]

lemma boxCutoff1_eq_one {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B / 2) : boxCutoff1 B x = 1 := by
  unfold boxCutoff1 flatStep
  rw [Real.smoothTransition.zero_of_nonpos, sub_zero]
  apply div_nonpos_of_nonpos_of_nonneg
  · have : x ^ 2 ≤ (B / 2) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hx 2; rwa [sq_abs] at this
    linarith
  · nlinarith

lemma boxCutoff1_eq_zero {B x : ℝ} (hB : 0 < B) (hx : 3 * B / 4 ≤ |x|) : boxCutoff1 B x = 0 := by
  unfold boxCutoff1 flatStep
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  have hd : 0 < (3 * B / 4) ^ 2 - (B / 2) ^ 2 := by nlinarith
  rw [le_div_iff₀ hd, one_mul]
  have : (3 * B / 4) ^ 2 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hx 2; rwa [sq_abs] at this
  linarith

lemma contDiff_boxCut (B : ℝ) : ContDiff ℝ ∞ (boxCut n B) := by
  unfold boxCut
  exact contDiff_prod fun l _ =>
    (contDiff_boxCutoff1 B).comp (EuclideanSpace.proj l : E n →L[ℝ] ℝ).contDiff

lemma boxCut_mem (B : ℝ) (z : E n) : boxCut n B z ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun l _ => (boxCutoff1_mem B _).1,
    Finset.prod_le_one₀ (fun l _ => (boxCutoff1_mem B _).1) fun l _ => (boxCutoff1_mem B _).2⟩

lemma boxCut_eq_one {B : ℝ} (hB : 0 < B) {z : E n} (hz : ∀ l, |z l| ≤ B / 2) :
    boxCut n B z = 1 :=
  Finset.prod_eq_one fun l _ => boxCutoff1_eq_one hB (hz l)

lemma boxCut_eq_zero {B : ℝ} (hB : 0 < B) {z : E n} {l : Fin (2 * n)} (hz : 3 * B / 4 ≤ |z l|) :
    boxCut n B z = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ l) (boxCutoff1_eq_zero hB hz)

lemma boxCut_eventually_zero {B : ℝ} (hB : 0 < B) {z : E n} {l : Fin (2 * n)}
    (hz : 3 * B / 4 < |z l|) : boxCut n B =ᶠ[𝓝 z] fun _ => 0 := by
  have hc : Continuous fun w : E n => |w l| :=
    continuous_abs.comp (EuclideanSpace.proj l : E n →L[ℝ] ℝ).continuous
  have : {w : E n | 3 * B / 4 < |w l|} ∈ 𝓝 z := (isOpen_lt continuous_const hc).mem_nhds hz
  filter_upwards [this] with w hw using boxCut_eq_zero hB hw.le

lemma fderiv_boxCut_eq_zero {B : ℝ} (hB : 0 < B) {z : E n} {l : Fin (2 * n)}
    (hz : 3 * B / 4 < |z l|) : fderiv ℝ (boxCut n B) z = 0 := by
  rw [(boxCut_eventually_zero hB hz).fderiv_eq]; simp

/-! ### Global integral curves -/

lemma hamVF_eq_zero_of_norm {H : ℝ → E n → ℝ} {R : ℝ} (hR : ∀ t y, R < ‖y‖ → H t y = 0)
    {t : ℝ} {y : E n} (hy : R < ‖y‖) : Problem.hamVF H t y = 0 := by
  apply General.Ham.hamVF_eq_zero_of_fderiv
  have hev : H t =ᶠ[𝓝 y] fun _ => 0 := by
    have : {w : E n | R < ‖w‖} ∈ 𝓝 y := (isOpen_lt continuous_const continuous_norm).mem_nhds hy
    filter_upwards [this] with w hw using hR t w hw
  rw [hev.fderiv_eq]; simp

/-- On every time window `|t| ≤ T+1`, the field is Lipschitz and bounded uniformly. -/
lemma window_bounds {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {R : ℝ} (hR : ∀ t y, R < ‖y‖ → H t y = 0) (T : ℕ) :
    ∃ K C : ℝ≥0, (∀ t : ℝ, |t| ≤ (T : ℝ) + 1 → LipschitzWith K (Problem.hamVF H t)) ∧
      ∀ t : ℝ, |t| ≤ (T : ℝ) + 1 → ∀ y, ‖Problem.hamVF H t y‖ ≤ C := by
  set V := General.Ham.hamField H
  have hV : ContDiff ℝ ∞ V := General.Ham.hamField_contDiff hH
  let ψ : ContDiffBump (0 : ℝ) := ⟨(T : ℝ) + 1, (T : ℝ) + 2, by positivity, by linarith⟩
  set Wf : ℝ × E n → E n := fun p => ψ p.1 • V p
  have hW : ContDiff ℝ ∞ Wf := (ψ.contDiff.comp contDiff_fst).smul hV
  have hcs : HasCompactSupport Wf := by
    apply HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) ((T : ℝ) + 2)).prod
      (isCompact_closedBall (0 : E n) R))
    rintro ⟨t, y⟩ hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with ht | hy
    · have : ψ t = 0 := by
        apply Function.notMem_support.mp
        rw [ψ.support_eq]
        exact fun h => ht (ball_subset_closedBall h)
      simp [Wf, this]
    · have hy' : R < ‖y‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hy
      simp [Wf, V, General.Ham.hamField, hamVF_eq_zero_of_norm hR hy']
  obtain ⟨K, hK⟩ := hW.lipschitzWith_of_hasCompactSupport hcs (by simp)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hW.continuous
  have hWV : ∀ t : ℝ, |t| ≤ (T : ℝ) + 1 → ∀ y, Wf (t, y) = Problem.hamVF H t y := by
    intro t ht y
    have : ψ t = 1 := ψ.one_of_mem_closedBall (by simpa [mem_closedBall, Real.dist_eq] using ht)
    simp [Wf, V, General.Ham.hamField, this]
  refine ⟨K, ⟨max C 0, le_max_right _ _⟩, fun t ht => ?_, fun t ht y => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun y z => ?_
    have := hK.dist_le_mul (t, y) (t, z)
    rw [hWV t ht, hWV t ht] at this
    simpa [Prod.dist_eq] using this
  · rw [← hWV t ht y]; exact (hC _).trans (le_max_left _ _)

/-- A solution on the window `(-T, T)`. -/
lemma window_solution {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {R : ℝ} (hR : ∀ t y, R < ‖y‖ → H t y = 0) (x : E n) (T : ℕ) :
    ∃ α : ℝ → E n, α 0 = x ∧
      ∀ t ∈ Ioo (-(T : ℝ)) T, HasDerivAt α (Problem.hamVF H t (α t)) t := by
  obtain ⟨K, C, hK, hC⟩ := window_bounds hH hR T
  have hV := General.Ham.hamField_contDiff hH
  have hwin : ∀ t ∈ Icc (-(T : ℝ)) T, |t| ≤ (T : ℝ) + 1 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hPL : IsPicardLindelof (fun t y => Problem.hamVF H t y) (tmin := -(T : ℝ)) (tmax := T)
      ⟨0, by constructor <;> simp⟩ x (C * (T : ℝ≥0)) 0 C K := by
    refine ⟨fun t ht => (hK t (hwin t ht)).lipschitzOnWith, fun y _ => ?_,
      fun t ht y _ => hC t (hwin t ht) y, ?_⟩
    · exact (hV.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · simp
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht => (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

/-- **Global integral curves.** If `H` is jointly smooth and `H(t,y) = 0` for `‖y‖ > R`, then
from every point there is an integral curve of `X_H` defined on all of `ℝ`. -/
theorem exists_integralCurve_global {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {R : ℝ} (hR : ∀ t y, R < ‖y‖ → H t y = 0) (x : E n) :
    ∃ γ : ℝ → E n, γ 0 = x ∧ IsIntegralCurve γ (Problem.hamVF H) := by
  choose α hα0 hα using window_solution hH hR x
  have hcons : ∀ (T T' : ℕ) (s : ℝ), |s| < T → |s| < T' → α T s = α T' s := by
    intro T T' s hT hT'
    set m : ℝ := min (T : ℝ) T'
    have hm : |s| < m := lt_min hT hT'
    have hm0 : 0 < m := lt_of_le_of_lt (abs_nonneg s) hm
    obtain ⟨K, -, hK, -⟩ := window_bounds hH hR T
    have hsub : ∀ t ∈ Ioo (-m) m, t ∈ Ioo (-(T : ℝ)) T ∧ t ∈ Ioo (-(T' : ℝ)) T' := by
      intro t ht
      have h1 : m ≤ T := min_le_left _ _
      have h2 : m ≤ T' := min_le_right _ _
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    have := ODE_solution_unique_of_mem_Ioo (v := Problem.hamVF H) (s := fun _ => univ) (K := K)
      (a := -m) (b := m) (t₀ := 0)
      (fun t ht => (hK t (by
        have := hsub t ht; rw [abs_le]; constructor <;> linarith [this.1.1, this.1.2])).lipschitzOnWith)
      ⟨by linarith, hm0⟩
      (fun t ht => ⟨hα T t (hsub t ht).1, mem_univ _⟩)
      (fun t ht => ⟨hα T' t (hsub t ht).2, mem_univ _⟩)
      (by rw [hα0, hα0])
    exact this ⟨by linarith [neg_abs_le s], lt_of_le_of_lt (le_abs_self s) hm⟩
  set γ : ℝ → E n := fun t => α (⌈|t|⌉₊ + 1) t
  have hlt : ∀ t : ℝ, |t| < ((⌈|t|⌉₊ + 1 : ℕ) : ℝ) := fun t => by
    push_cast; linarith [Nat.le_ceil |t|]
  refine ⟨γ, by simp [γ, hα0], fun t => ?_⟩
  set T := ⌈|t|⌉₊ + 1
  have hev : γ =ᶠ[𝓝 t] α T := by
    have : {s : ℝ | |s| < T} ∈ 𝓝 t :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (hlt t)
    filter_upwards [this] with s hs using hcons _ _ s (hlt s) hs
  have hd := hα T t ⟨by linarith [neg_abs_le t, hlt t], lt_of_le_of_lt (le_abs_self t) (hlt t)⟩
  exact hd.congr_of_eventuallyEq hev

end SymplecticPacking.General.Compile
