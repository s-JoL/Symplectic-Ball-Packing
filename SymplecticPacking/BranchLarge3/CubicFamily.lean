import SymplecticPacking.BranchLarge3.ExactFibreCore
import SymplecticPacking.Return.Flow

/-!
# Step S4b: the explicit exact cubic degeneration family

Let `f(z) = z₁z₂(z₁−z₂)+z₂−2z₁` be the affine cubic (`CubicModel.polynomial`), with gradient
`(f_V, f_W)` and `|∇f|² = gsq`. On `Y = ℂ² × ℂ` we use the explicit vector field

  `X(z, w) = κ_R(|z|²+|w|²) · (h_m(|∇f(z)|²)⁻¹ · (conj f_V(z) w, conj f_W(z) w), 0)`,

where `h_m(s) = s` for `s ≥ m/2` and `h_m ≥ m/4` (so the first component is a right inverse of
`df(z)` applied to `w` wherever `|∇f(z)|² ≥ m/2`), and `κ_R` is a radial cutoff equal to `1` on
`|·|² ≤ R`. Its flow `φ_t` (time cut off outside `[-2,2]`, unique global ODE solution) fixes `w`
and, while it stays where both cutoffs are `1`, satisfies `f(φ_t(z,w)) = f(z) + t w`.

The family is `Φ_t(x, ν, w) = (φ_t(ι x, w)₁, ν)` with `ι` the inclusion of the cubic curve, and
`Γ_t` the pullback of the cone primitive along `(Φ_t, ν, w)`. The parameters `m, R` and the time
bound `ε` are explicit: `m` is half the minimum of `|∇f|²` on `ι(K)`, `R` comes from the maximum
of `|·|²` on the compact data, and `ε = min 1 (δ/(C+1))` with `C = sup |X|` and
`δ = min 1 (m / (2(G+1)))`, `G` the maximum of `|d(|∇f|²)|` on a ball containing the data; the
mean value theorem then keeps every trajectory from the domain inside the region where `X` is
the uncut field, for `|t| ≤ ε`.

Paper: supplement `six-return.tex` (cubic degeneration).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Filter Metric

namespace CubicFamily

/-- The ambient space `ℂ² × ℂ` of the normal flow. -/
abbrev Y := PlaneBase × ℂ

/-- `|∇f(z)|²`. -/
def gsq (z : PlaneBase) : ℝ := Complex.normSq (gradV z) + Complex.normSq (gradW z)

/-- `|y|²` (Euclidean). -/
def nsq (y : Y) : ℝ := Complex.normSq y.1.1 + Complex.normSq y.1.2 + Complex.normSq y.2

theorem normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem gradV_contDiff : ContDiff ℝ ∞ gradV := by
  have h : ContDiff ℂ ∞ gradV := by unfold gradV; fun_prop
  exact h.restrict_scalars ℝ

theorem gradW_contDiff : ContDiff ℝ ∞ gradW := by
  have h : ContDiff ℂ ∞ gradW := by unfold gradW; fun_prop
  exact h.restrict_scalars ℝ

theorem gsq_contDiff : ContDiff ℝ ∞ gsq :=
  (normSq_contDiff.comp gradV_contDiff).add (normSq_contDiff.comp gradW_contDiff)

theorem nsq_contDiff : ContDiff ℝ ∞ nsq :=
  ((normSq_contDiff.comp (contDiff_fst.comp contDiff_fst)).add
    (normSq_contDiff.comp (contDiff_snd.comp contDiff_fst))).add
    (normSq_contDiff.comp contDiff_snd)

theorem gsq_pos_of_polynomial {z : PlaneBase} (hz : polynomial z = 0) : 0 < gsq z := by
  unfold gsq
  rcases gradient_nonzero hz with h | h
  · have := Complex.normSq_pos.mpr h
    have := Complex.normSq_nonneg (gradW z)
    linarith
  · have := Complex.normSq_pos.mpr h
    have := Complex.normSq_nonneg (gradV z)
    linarith

theorem norm_le_sqrt_nsq (y : Y) : ‖y‖ ≤ Real.sqrt (nsq y) := by
  have h1 := Complex.normSq_nonneg y.1.1
  have h2 := Complex.normSq_nonneg y.1.2
  have h3 := Complex.normSq_nonneg y.2
  have hc (u : ℂ) (hu : Complex.normSq u ≤ nsq y) : ‖u‖ ≤ Real.sqrt (nsq y) := by
    rw [← Real.sqrt_sq (norm_nonneg u)]
    apply Real.sqrt_le_sqrt
    rw [← Complex.normSq_eq_norm_sq]
    exact hu
  unfold nsq at *
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le (max_le (hc _ (by linarith)) (hc _ (by linarith))) (hc _ (by linarith))

theorem nsq_nonneg (y : Y) : 0 ≤ nsq y := by
  unfold nsq
  have := Complex.normSq_nonneg y.1.1
  have := Complex.normSq_nonneg y.1.2
  have := Complex.normSq_nonneg y.2
  linarith

theorem nsq_le (y : Y) : nsq y ≤ 3 * ‖y‖ ^ 2 := by
  have h1 : ‖y.1.1‖ ≤ ‖y‖ := (norm_fst_le y.1).trans (norm_fst_le y)
  have h2 : ‖y.1.2‖ ≤ ‖y‖ := (norm_snd_le y.1).trans (norm_fst_le y)
  have h3 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
  unfold nsq
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have := norm_nonneg y.1.1
  have := norm_nonneg y.1.2
  have := norm_nonneg y.2
  nlinarith

/-! ### The regularised inverse and the normal lift -/

/-- `h_m(s)`: equal to `s` for `s ≥ m/2`, and `≥ m/4` everywhere (for `m > 0`). -/
def hreg (m s : ℝ) : ℝ :=
  s * Return.step (m / 4) (m / 2) s + m / 2 * (1 - Return.step (m / 4) (m / 2) s)

theorem step_mem (a b x : ℝ) : 0 ≤ Return.step a b x ∧ Return.step a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem hreg_contDiff (m : ℝ) : ContDiff ℝ ∞ (hreg m) := by
  unfold hreg
  exact (contDiff_id.mul (Return.step_contDiff _ _)).add
    (contDiff_const.mul (contDiff_const.sub (Return.step_contDiff _ _)))

theorem hreg_lower {m : ℝ} (hm : 0 < m) (s : ℝ) : m / 4 ≤ hreg m s := by
  obtain ⟨h0, h1⟩ := step_mem (m / 4) (m / 2) s
  unfold hreg
  by_cases hs : s ≤ m / 4
  · rw [Return.step_eq_zero (by linarith) hs]; linarith
  · rw [not_le] at hs
    nlinarith [mul_nonneg h0 (le_of_lt (sub_pos.mpr hs)), mul_nonneg (sub_nonneg.mpr h1) hm.le]

theorem hreg_eq {m : ℝ} (hm : 0 < m) {s : ℝ} (hs : m / 2 ≤ s) : hreg m s = s := by
  unfold hreg
  rw [Return.step_eq_one (by linarith) hs]; ring

/-- The (regularised) normal lift: `w ↦ h_m(|∇f(z)|²)⁻¹ (conj f_V(z) w, conj f_W(z) w)`. -/
def nlift (m : ℝ) (z : PlaneBase) (w : ℂ) : PlaneBase :=
  (hreg m (gsq z))⁻¹ • (starRingEnd ℂ (gradV z) * w, starRingEnd ℂ (gradW z) * w)

theorem jacobian_nlift {m : ℝ} (hm : 0 < m) {z : PlaneBase} (hz : m / 2 ≤ gsq z) (w : ℂ) :
    jacobian z (nlift m z w) = w := by
  have hg : 0 < gsq z := by linarith
  rw [nlift, hreg_eq hm hz]
  change gradV z * ((gsq z)⁻¹ • (starRingEnd ℂ (gradV z) * w)) +
    gradW z * ((gsq z)⁻¹ • (starRingEnd ℂ (gradW z) * w)) = w
  rw [Complex.real_smul, Complex.real_smul]
  have hv := Complex.mul_conj (gradV z)
  have hw := Complex.mul_conj (gradW z)
  have hgc : ((gsq z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hs : ((gsq z : ℝ) : ℂ) = (Complex.normSq (gradV z) : ℂ) + (Complex.normSq (gradW z) : ℂ) := by
    unfold gsq; push_cast; ring
  calc gradV z * (((gsq z)⁻¹ : ℝ) * (starRingEnd ℂ (gradV z) * w)) +
        gradW z * (((gsq z)⁻¹ : ℝ) * (starRingEnd ℂ (gradW z) * w))
      = ((gsq z)⁻¹ : ℝ) * ((gradV z * starRingEnd ℂ (gradV z) +
          gradW z * starRingEnd ℂ (gradW z)) * w) := by ring
    _ = w := by
      rw [hv, hw, ← hs]; push_cast; field_simp

/-! ### The field and its flow -/

/-- Radial cutoff: `1` for `s ≤ R`, `0` for `s ≥ R + 1`. -/
def cutR (R s : ℝ) : ℝ := 1 - Return.step R (R + 1) s

theorem cutR_eq_one {R s : ℝ} (hs : s ≤ R) : cutR R s = 1 := by
  rw [cutR, Return.step_eq_zero (by linarith) hs, sub_zero]

theorem cutR_eq_zero {R s : ℝ} (hs : R + 1 ≤ s) : cutR R s = 0 := by
  rw [cutR, Return.step_eq_one (by linarith) hs, sub_self]

/-- The autonomous field `X`. -/
def field (m R : ℝ) (y : Y) : Y := cutR R (nsq y) • (nlift m y.1 y.2, (0 : ℂ))

/-- The time-cut field (equal to `X` for `|t| ≤ 1`). -/
def tfield (m R : ℝ) (t : ℝ) (y : Y) : Y := Return.plateau (-2) (-1) 1 2 t • field m R y

/-- The flow of the time-cut field (unique global ODE solution). -/
def flowY (m R : ℝ) (t : ℝ) (y : Y) : Y := Return.flow (tfield m R) t y

theorem field_snd (m R : ℝ) (y : Y) : (field m R y).2 = 0 := by
  simp [field]

theorem nlift_contDiff {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (fun y : Y => nlift m y.1 y.2) := by
  unfold nlift
  have hh : ContDiff ℝ ∞ (fun y : Y => hreg m (gsq y.1)) :=
    (hreg_contDiff m).comp (gsq_contDiff.comp contDiff_fst)
  have hinv : ContDiff ℝ ∞ (fun y : Y => (hreg m (gsq y.1))⁻¹) :=
    hh.inv (fun y => (lt_of_lt_of_le (by linarith) (hreg_lower hm _)).ne')
  have hc : ContDiff ℝ ∞ (fun z : ℂ => starRingEnd ℂ z) := Complex.conjCLE.contDiff
  exact hinv.smul
    (((hc.comp (gradV_contDiff.comp contDiff_fst)).mul contDiff_snd).prodMk
      ((hc.comp (gradW_contDiff.comp contDiff_fst)).mul contDiff_snd))

theorem field_contDiff {m : ℝ} (hm : 0 < m) (R : ℝ) : ContDiff ℝ ∞ (field m R) := by
  unfold field cutR
  exact (contDiff_const.sub ((Return.step_contDiff _ _).comp nsq_contDiff)).smul
    ((nlift_contDiff hm).prodMk contDiff_const)

theorem field_eq_zero {m R : ℝ} {y : Y} (hy : |R| + 2 < ‖y‖) : field m R y = 0 := by
  have h1 : (1 : ℝ) ≤ ‖y‖ := by linarith [abs_nonneg R]
  have h2 : nsq y ≥ ‖y‖ ^ 2 := by
    have := norm_le_sqrt_nsq y
    have h0 : 0 ≤ nsq y := nsq_nonneg y
    calc ‖y‖ ^ 2 ≤ Real.sqrt (nsq y) ^ 2 := by gcongr
      _ = nsq y := Real.sq_sqrt h0
  have h3 : R + 1 ≤ nsq y := by nlinarith [le_abs_self R]
  rw [field, cutR_eq_zero h3, zero_smul]

theorem field_hasCompactSupport (m R : ℝ) : HasCompactSupport (field m R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Y) (|R| + 2))
  intro y hy
  rw [mem_closedBall_zero_iff, not_le] at hy
  exact field_eq_zero hy

theorem plateau_mem (t : ℝ) :
    0 ≤ Return.plateau (-2) (-1) 1 2 t ∧ Return.plateau (-2) (-1) 1 2 t ≤ 1 := by
  unfold Return.plateau
  have a0 := Real.smoothTransition.nonneg ((t - -2) / (-1 - -2))
  have a1 := Real.smoothTransition.le_one ((t - -2) / (-1 - -2))
  have b0 := Real.smoothTransition.nonneg ((2 - t) / (2 - 1))
  have b1 := Real.smoothTransition.le_one ((2 - t) / (2 - 1))
  exact ⟨mul_nonneg a0 b0, mul_le_one₀ a1 b0 b1⟩

theorem tfield_csField {m : ℝ} (hm : 0 < m) (R : ℝ) : Return.CSField (tfield m R) := by
  refine ⟨((Return.plateau_contDiff _ _ _ _).comp contDiff_fst).smul
    ((field_contDiff hm R).comp contDiff_snd), ?_⟩
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Y) (|R| + 2))
  rintro ⟨t, y⟩ hp
  rw [mem_closedBall_zero_iff, not_le, Prod.norm_def, lt_max_iff] at hp
  change Return.plateau (-2) (-1) 1 2 t • field m R y = 0
  rcases hp with ht | hy
  · rw [Real.norm_eq_abs] at ht
    have h2 : 2 < |t| := by linarith [abs_nonneg R]
    rcases lt_abs.mp h2 with h | h
    · rw [Return.plateau_eq_zero_right (by norm_num) h.le, zero_smul]
    · rw [Return.plateau_eq_zero_left (by norm_num) (by linarith), zero_smul]
  · rw [field_eq_zero hy, smul_zero]

theorem tfield_norm_le {m R C : ℝ} (hC : ∀ y, ‖field m R y‖ ≤ C) (t : ℝ) (y : Y) :
    ‖tfield m R t y‖ ≤ C := by
  obtain ⟨h0, h1⟩ := plateau_mem t
  rw [tfield, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  have hc : 0 ≤ C := (norm_nonneg _).trans (hC y)
  calc _ ≤ 1 * C := mul_le_mul h1 (hC y) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

theorem flowY_snd {m : ℝ} (hm : 0 < m) (R t : ℝ) (y : Y) : (flowY m R t y).2 = y.2 := by
  have hV := tfield_csField hm R
  have hd : ∀ u, HasDerivAt (fun u => (flowY m R u y).2) 0 u := by
    intro u
    have h := (ContinuousLinearMap.snd ℝ PlaneBase ℂ).hasFDerivAt.comp_hasDerivAt u
      (hV.flow_hasDerivAt y u)
    have hz : (ContinuousLinearMap.snd ℝ PlaneBase ℂ) (tfield m R u (Return.flow (tfield m R) u y)) = 0 := by
      change (tfield m R u _).2 = 0
      simp [tfield, field_snd]
    rw [hz] at h
    exact h
  have := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  rw [this]
  change (Return.flow (tfield m R) 0 y).2 = y.2
  rw [hV.flow_zero]

/-! ### Explicit parameters -/

section params

variable (K : Set BaseCurve) (H : Set DiskPair)

/-- The compact data `{(ι x, w) : (x, ν, w) ∈ K × H}`. -/
def data : Set Y := (fun q : CubicConeSpace => ((inclusion q.1, q.2.2) : Y)) '' (K ×ˢ H)

/-- Minimum of `|∇f|²` on `ι(K)`. -/
def gmin : ℝ := sInf ((fun x => gsq (inclusion x)) '' K)

/-- The lower bound `m > 0` (half the minimum). -/
def mPar : ℝ := if 0 < gmin K then gmin K / 2 else 1

/-- The radius bound `R₁` (strictly above `|·|²` on the data). -/
def R1 : ℝ := sSup (nsq '' data K H) + 1

/-- The norm radius `r = √R₁ + 1`. -/
def rad : ℝ := Real.sqrt (R1 K H) + 1

/-- The cutoff radius `R = 3 r²`. -/
def RPar : ℝ := 3 * rad K H ^ 2

/-- The bound `G` for `|d(|∇f|²)|` on the ball of radius `r`. -/
def GPar : ℝ := sSup ((fun z => ‖fderiv ℝ gsq z‖) '' closedBall (0 : PlaneBase) (rad K H))

/-- The displacement allowance `δ`. -/
def dPar : ℝ := min 1 (mPar K / (2 * (GPar K H + 1)))

/-- The bound `C` for `|X|`. -/
def CPar : ℝ := sSup (range fun y => ‖field (mPar K) (RPar K H) y‖)

/-- The time bound `ε`. -/
def ePar : ℝ := min 1 (dPar K H / (CPar K H + 1))

/-- The tube domain in `Y`. -/
def Wset : Set Y := {y | nsq y < R1 K H ∧ mPar K < gsq y.1}

theorem mPar_pos : 0 < mPar K := by
  unfold mPar; split_ifs with h
  · positivity
  · norm_num

theorem GPar_nonneg : 0 ≤ GPar K H := Real.sSup_nonneg (by rintro _ ⟨z, -, rfl⟩; positivity)

theorem CPar_nonneg : 0 ≤ CPar K H := Real.sSup_nonneg (by rintro _ ⟨y, rfl⟩; positivity)

theorem dPar_pos : 0 < dPar K H := by
  have := mPar_pos K
  have := GPar_nonneg K H
  unfold dPar
  exact lt_min one_pos (by positivity)

theorem ePar_pos : 0 < ePar K H := by
  have := dPar_pos K H
  have := CPar_nonneg K H
  unfold ePar
  exact lt_min one_pos (by positivity)

theorem ePar_le_one : ePar K H ≤ 1 := min_le_left _ _

theorem field_le_CPar (y : Y) : ‖field (mPar K) (RPar K H) y‖ ≤ CPar K H := by
  apply le_csSup _ (mem_range_self y)
  exact ((field_contDiff (mPar_pos K) _).continuous.norm).bddAbove_range_of_hasCompactSupport
    (field_hasCompactSupport _ _).norm

theorem fderiv_le_GPar {z : PlaneBase} (hz : z ∈ closedBall (0 : PlaneBase) (rad K H)) :
    ‖fderiv ℝ gsq z‖ ≤ GPar K H := by
  have hc : Continuous (fun z => ‖fderiv ℝ gsq z‖) :=
    (gsq_contDiff.continuous_fderiv (by simp)).norm
  exact le_csSup ((isCompact_closedBall _ _).image hc).bddAbove (mem_image_of_mem _ hz)

theorem Wset_isOpen : IsOpen (Wset K H) :=
  (isOpen_lt nsq_contDiff.continuous continuous_const).inter
    (isOpen_lt continuous_const (gsq_contDiff.continuous.comp continuous_fst))

theorem data_subset_Wset {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K)
    (hH : IsCompact H) {q : CubicConeSpace} (hq : q ∈ K ×ˢ H) :
    ((inclusion q.1, q.2.2) : Y) ∈ Wset K H := by
  have hι : Continuous (fun q : CubicConeSpace => ((inclusion q.1, q.2.2) : Y)) :=
    (inclusion_isEmbedding.continuous.comp continuous_fst).prodMk continuous_snd.snd
  have hdc : IsCompact (data K H) := (hK.prod hH).image hι
  constructor
  · have hle : nsq ((inclusion q.1, q.2.2) : Y) ≤ sSup (nsq '' data K H) :=
      le_csSup (hdc.image nsq_contDiff.continuous).bddAbove
        (mem_image_of_mem nsq ⟨q, hq, rfl⟩)
    change _ < sSup (nsq '' data K H) + 1
    linarith
  · have hne : K.Nonempty := ⟨q.1, hq.1⟩
    let g : BaseCurve → ℝ := fun x => gsq (inclusion x)
    have hg : Continuous g := gsq_contDiff.continuous.comp inclusion_isEmbedding.continuous
    have himg : IsCompact (g '' K) := hK.image hg
    obtain ⟨k, hk, hke⟩ := himg.sInf_mem (hne.image g)
    have hpos : 0 < gmin K := by
      change 0 < sInf (g '' K)
      rw [← hke]; exact gsq_pos_of_polynomial (inclusion_polynomial k)
    have hle : gmin K ≤ g q.1 := csInf_le himg.bddBelow (mem_image_of_mem g hq.1)
    change mPar K < g q.1
    rw [mPar, if_pos hpos]
    linarith

/-! ### Trajectories from the tube domain -/

theorem traj {y : Y} (hy : y ∈ Wset K H) {s : ℝ} (hs : s ∈ Icc (-ePar K H) (ePar K H)) :
    tfield (mPar K) (RPar K H) s (flowY (mPar K) (RPar K H) s y) =
        (nlift (mPar K) (flowY (mPar K) (RPar K H) s y).1 (flowY (mPar K) (RPar K H) s y).2,
          (0 : ℂ)) ∧
      mPar K / 2 ≤ gsq (flowY (mPar K) (RPar K H) s y).1 := by
  have hm := mPar_pos K
  have hV := tfield_csField hm (RPar K H)
  have hε1 := ePar_le_one K H
  have hC0 := CPar_nonneg K H
  have hG0 := GPar_nonneg K H
  have hd0 := dPar_pos K H
  have habs : |s| ≤ ePar K H := abs_le.mpr ⟨hs.1, hs.2⟩
  -- displacement
  have hdisp : ‖flowY (mPar K) (RPar K H) s y - y‖ ≤ CPar K H * |s| := by
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => flowY (mPar K) (RPar K H) u y)
      (f' := fun u => tfield (mPar K) (RPar K H) u (flowY (mPar K) (RPar K H) u y))
      (fun u _ => (hV.flow_hasDerivAt y u).hasDerivWithinAt)
      (fun u _ => tfield_norm_le (field_le_CPar K H) u _) (mem_univ 0) (mem_univ s)
    have h0 : flowY (mPar K) (RPar K H) 0 y = y := hV.flow_zero y
    rw [h0, sub_zero, Real.norm_eq_abs] at h
    exact h
  have hCε : CPar K H * |s| ≤ dPar K H := by
    have h1 : CPar K H * |s| ≤ CPar K H * (dPar K H / (CPar K H + 1)) :=
      mul_le_mul_of_nonneg_left (habs.trans (min_le_right _ _)) hC0
    have h2 : CPar K H * (dPar K H / (CPar K H + 1)) ≤ dPar K H := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hd1 : dPar K H ≤ 1 := min_le_left _ _
  set q := flowY (mPar K) (RPar K H) s y with hqdef
  have hqy : ‖q - y‖ ≤ dPar K H := hdisp.trans hCε
  -- radius
  have hy1 : ‖y‖ ≤ Real.sqrt (R1 K H) :=
    (norm_le_sqrt_nsq y).trans (Real.sqrt_le_sqrt hy.1.le)
  have hyr : ‖y‖ ≤ rad K H := by unfold rad; linarith
  have hqr : ‖q‖ ≤ rad K H := by
    have : ‖q‖ ≤ ‖y‖ + ‖q - y‖ := by
      calc ‖q‖ = ‖y + (q - y)‖ := by congr 1; abel
        _ ≤ ‖y‖ + ‖q - y‖ := norm_add_le _ _
    unfold rad; linarith
  have hnq : nsq q ≤ RPar K H := by
    have := nsq_le q
    have h2 : ‖q‖ ^ 2 ≤ rad K H ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hqr 2
    unfold RPar; linarith
  have hcut : cutR (RPar K H) (nsq q) = 1 := cutR_eq_one hnq
  -- gradient
  have hy1b : y.1 ∈ closedBall (0 : PlaneBase) (rad K H) := by
    rw [mem_closedBall_zero_iff]; exact (norm_fst_le y).trans hyr
  have hq1b : q.1 ∈ closedBall (0 : PlaneBase) (rad K H) := by
    rw [mem_closedBall_zero_iff]; exact (norm_fst_le q).trans hqr
  have hmv := (convex_closedBall (0 : PlaneBase) (rad K H)).norm_image_sub_le_of_norm_fderiv_le
    (f := gsq) (fun x _ => gsq_contDiff.differentiable (by simp) x)
    (fun x hx => fderiv_le_GPar K H hx) hy1b hq1b
  have hq1 : ‖q.1 - y.1‖ ≤ dPar K H := (norm_fst_le (q - y)).trans hqy
  have hGd : GPar K H * dPar K H ≤ mPar K / 2 := by
    have h1 : GPar K H * dPar K H ≤ GPar K H * (mPar K / (2 * (GPar K H + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hG0
    have h2 : GPar K H * (mPar K / (2 * (GPar K H + 1))) ≤ mPar K / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hgq : mPar K / 2 ≤ gsq q.1 := by
    rw [Real.norm_eq_abs] at hmv
    have h3 := neg_abs_le (gsq q.1 - gsq y.1)
    have h4 : GPar K H * ‖q.1 - y.1‖ ≤ GPar K H * dPar K H :=
      mul_le_mul_of_nonneg_left hq1 hG0
    linarith [hy.2]
  have hpl : Return.plateau (-2) (-1) 1 2 s = 1 :=
    Return.plateau_eq_one (by norm_num) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
  refine ⟨?_, hgq⟩
  simp only [tfield, field, hpl, hcut, one_smul]

theorem poly_flow {y : Y} (hy : y ∈ Wset K H) {t : ℝ} (ht : t ∈ Icc (-ePar K H) (ePar K H)) :
    polynomial (flowY (mPar K) (RPar K H) t y).1 = polynomial y.1 + t • y.2 := by
  have hm := mPar_pos K
  have hV := tfield_csField hm (RPar K H)
  have hd : ∀ s ∈ Icc (-ePar K H) (ePar K H),
      HasDerivAt (fun u => polynomial (flowY (mPar K) (RPar K H) u y).1) y.2 s := by
    intro s hs
    obtain ⟨htr, hg⟩ := traj K H hy hs
    have h1 := (ContinuousLinearMap.fst ℝ PlaneBase ℂ).hasFDerivAt.comp_hasDerivAt s
      (hV.flow_hasDerivAt y s)
    have h2 := ((polynomial_hasFDerivAt (flowY (mPar K) (RPar K H) s y).1).restrictScalars
      ℝ).comp_hasDerivAt s h1
    have hv : ((jacobian (flowY (mPar K) (RPar K H) s y).1).restrictScalars ℝ)
        ((ContinuousLinearMap.fst ℝ PlaneBase ℂ)
          (tfield (mPar K) (RPar K H) s (Return.flow (tfield (mPar K) (RPar K H)) s y))) = y.2 := by
      change jacobian (flowY (mPar K) (RPar K H) s y).1
        ((tfield (mPar K) (RPar K H) s (flowY (mPar K) (RPar K H) s y)).1) = y.2
      rw [htr, jacobian_nlift hm hg, flowY_snd hm]
    rw [hv] at h2
    exact h2
  have h := NormalLift.curve_eq_add_of_hasDerivAt (ePar_pos K H) hd ht
  have h0 : flowY (mPar K) (RPar K H) 0 y = y := hV.flow_zero y
  simpa only [h0] using h

end params

end CubicFamily

open CubicFamily

/-- The explicit degeneration family of maps `Φ`. -/
def famMap (A B D S : ℕ) (c : ℝ) (K : Set BaseCurve) (H : Set DiskPair) :
    ℝ × CubicConeSpace → CubicAmbient := fun p =>
  ((flowY (mPar K) (RPar K H) p.1 (inclusion p.2.1, p.2.2.2)).1, p.2.2.1)

/-- The explicit family of primitives `Γ`. -/
def famPrim (A B D S : ℕ) (c : ℝ) (K : Set BaseCurve) (H : Set DiskPair) :
    ℝ → ManifoldOneForm CubicConeModel CubicConeSpace :=
  movingPrimitivePullback (E := CubicConeModel) (cubicConePrimitive (A := A) (B := B) D S c)
    (fun p : ℝ × CubicConeSpace => ((famMap A B D S c K H p).1, p.2.2))

/-- The explicit time bound `ε`. -/
def famEps (A B D S : ℕ) (c : ℝ) (K : Set BaseCurve) (H : Set DiskPair) : ℝ := ePar K H

/-- The explicit open domain `U`. -/
def famDomain (A B D S : ℕ) (c : ℝ) (K : Set BaseCurve) (H : Set DiskPair) :
    Set CubicConeSpace :=
  {q | ((inclusion q.1, q.2.2) : CubicFamily.Y) ∈ Wset K H}

theorem fam_spec {A B : ℕ} (D S : ℕ) (c : ℝ)
    {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
    let Φ := famMap A B D S c K H
    let Γ := famPrim A B D S c K H
    let ε := famEps A B D S c K H
    let U := famDomain A B D S c K H
    0 < ε ∧ IsOpen U ∧ K ×ˢ H ⊆ U ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicConeModel)) 𝓘(ℝ, CubicAmbient) ∞ Φ ∧
      (∀ p, Φ (0, p) = (inclusion p.1, p.2.1)) ∧
      SmoothOneFormFamily Γ ∧ Γ 0 = centralCubicPrimitive (A := A) (B := B) D S c ∧
      (∀ t ∈ Icc (-ε) ε, t ≠ 0 → Topology.IsEmbedding (fun p : U => Φ (t, p.val))) ∧
      ∀ t ∈ Icc (-ε) ε, t ≠ 0 → ∀ p ∈ U,
        manifoldExteriorOneForm (Γ t) p =
          (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t, p))).bilinearComp
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t, q)) p)
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t, q)) p) := by
  intro Φ Γ ε U
  have hm := mPar_pos K
  have hV := tfield_csField hm (RPar K H)
  have hflow : ContDiff ℝ ∞ (fun p : ℝ × CubicFamily.Y => flowY (mPar K) (RPar K H) p.1 p.2) :=
    hV.flow_smooth
  have hι : ContMDiff 𝓘(ℝ, CubicConeModel) 𝓘(ℝ, CubicFamily.Y) ∞
      (fun q : CubicConeSpace => ((inclusion q.1, q.2.2) : CubicFamily.Y)) :=
    (inclusion_real_contMDiff.comp (flatProduct_fst_smooth (V := DiskPair))).prodMk_space
      (contDiff_snd.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve)))
  have hν : ContMDiff 𝓘(ℝ, CubicConeModel) 𝓘(ℝ, ℂ) ∞ (fun p : CubicConeSpace => p.2.1) :=
    contDiff_fst.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve))
  have hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicConeModel)) 𝓘(ℝ, CubicAmbient) ∞ Φ :=
    (contDiff_fst.contMDiff.comp (hflow.contMDiff.comp
      (contMDiff_fst.prodMk_space (hι.comp contMDiff_snd)))).prodMk_space (hν.comp contMDiff_snd)
  let g : ℝ × CubicConeSpace → CubicConeTarget := fun p => ((Φ p).1, p.2.2)
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicConeModel)) 𝓘(ℝ, CubicConeTarget) ∞ g :=
    (contDiff_fst.contMDiff.comp hΦ).prodMk_space
      ((flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := DiskPair)).comp
        contMDiff_snd)
  have hUo : IsOpen U := (Wset_isOpen K H).preimage hι.continuous
  have hpoly : ∀ q ∈ U, ∀ t ∈ Icc (-ε) ε, polynomial (Φ (t, q)).1 = t • q.2.2 := by
    intro q hq t ht
    have h := poly_flow K H hq ht
    change polynomial (flowY (mPar K) (RPar K H) t (inclusion q.1, q.2.2)).1 = _
    rw [h]
    change polynomial (inclusion q.1) + t • q.2.2 = t • q.2.2
    rw [inclusion_polynomial, zero_add]
  have hΦ0 : ∀ p : CubicConeSpace, Φ (0, p) = (inclusion p.1, p.2.1) := by
    intro p
    change ((flowY (mPar K) (RPar K H) 0 (inclusion p.1, p.2.2)).1, p.2.1) = _
    rw [show flowY (mPar K) (RPar K H) 0 (inclusion p.1, p.2.2) = (inclusion p.1, p.2.2) from
      hV.flow_zero _]
  refine ⟨ePar_pos K H, hUo, fun q hq => data_subset_Wset hK hH hq, hΦ, hΦ0,
    movingPrimitivePullback_smooth (cubicConePrimitive_smooth D S c) hg, ?_, ?_, ?_⟩
  · have he : (fun p : CubicConeSpace => g (0, p)) = centralCubicCoordinates := by
      funext p
      change ((Φ (0, p)).1, p.2) = (inclusion p.1, p.2)
      rw [hΦ0]
    change manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S c)
      (fun p => g (0, p)) 0 = centralCubicPrimitive (A := A) (B := B) D S c
    rw [he]
    rfl
  · intro t ht ht0
    let J : U → PlaneBase × DiskPair := fun p => (inclusion p.val.1, p.val.2)
    have hJ : Topology.IsEmbedding J :=
      (inclusion_isEmbedding.prodMap Topology.IsEmbedding.id).comp
        Topology.IsEmbedding.subtypeVal
    let Rinv : CubicAmbient → PlaneBase × DiskPair := fun z =>
      ((Return.flowInv (tfield (mPar K) (RPar K H)) t (z.1, t⁻¹ • polynomial z.1)).1,
        (z.2, (Return.flowInv (tfield (mPar K) (RPar K H)) t (z.1, t⁻¹ • polynomial z.1)).2))
    have hin : Continuous (fun z : CubicAmbient =>
        Return.flowInv (tfield (mPar K) (RPar K H)) t (z.1, t⁻¹ • polynomial z.1)) :=
      (hV.flowInv_slice_smooth t).continuous.comp (continuous_fst.prodMk
        (((polynomial_contDiff.continuous).comp' continuous_fst).const_smul t⁻¹))
    have hR : Continuous Rinv := hin.fst.prodMk (continuous_snd.prodMk hin.snd)
    have hc : Continuous (fun p : U => Φ (t, p.val)) :=
      hΦ.continuous.comp (continuous_const.prodMk continuous_subtype_val)
    have hcomp : Rinv ∘ (fun p : U => Φ (t, p.val)) = J := by
      funext p
      have hq2 := flowY_snd hm (RPar K H) t ((inclusion p.val.1, p.val.2.2) : CubicFamily.Y)
      have hpl : t⁻¹ • polynomial (Φ (t, p.val)).1 = p.val.2.2 := by
        rw [hpoly _ p.property t ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      have hpair : ((Φ (t, p.val)).1, t⁻¹ • polynomial (Φ (t, p.val)).1) =
          flowY (mPar K) (RPar K H) t (inclusion p.val.1, p.val.2.2) := by
        rw [hpl]
        exact Prod.ext rfl hq2.symm
      have hback : Return.flowInv (tfield (mPar K) (RPar K H)) t
          ((Φ (t, p.val)).1, t⁻¹ • polynomial (Φ (t, p.val)).1) =
          (inclusion p.val.1, p.val.2.2) := by
        rw [hpair]; exact hV.flowInv_flow t _
      change ((Return.flowInv (tfield (mPar K) (RPar K H)) t
          ((Φ (t, p.val)).1, t⁻¹ • polynomial (Φ (t, p.val)).1)).1,
        ((Φ (t, p.val)).2, (Return.flowInv (tfield (mPar K) (RPar K H)) t
          ((Φ (t, p.val)).1, t⁻¹ • polynomial (Φ (t, p.val)).1)).2)) = _
      rw [hback]
      rfl
    exact Topology.IsEmbedding.of_comp hc hR (hcomp ▸ hJ)
  · intro t ht ht0 p hp
    have he : (fun q => g (t, q)) =ᶠ[𝓝 p] cubicNormalCoordinates t ∘ (fun q => Φ (t, q)) := by
      filter_upwards [hUo.mem_nhds hp] with q hq
      change ((Φ (t, q)).1, q.2) = ((Φ (t, q)).1, ((Φ (t, q)).2, t⁻¹ • polynomial (Φ (t, q)).1))
      rw [hpoly q hq t ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rfl
    exact movingPrimitivePullback_exterior_comp (cubicConePrimitive_smooth D S c) hg
      (cubicNormalCoordinates_smooth t) (hΦ.comp (contMDiff_const.prodMk contMDiff_id)) he

end SymplecticPacking.BranchLarge3
